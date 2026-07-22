set shell := ["bash", "-uc"]

ormolu := "ormolu"
nix_fmt := "nixpkgs-fmt"
shellcheck := "shellcheck --external-sources --source-path=SCRIPTDIR"

# List available recipes
default:
    @just --list

# auto-format Haskell source code using ormolu
format-hs:
    @echo "running {{ormolu}} --mode inplace"
    @{{ormolu}} --mode inplace $(git ls-files '*.hs' '*.hs-boot')

# auto-format changed Haskell source code using ormolu
format-hs-changed:
    #!/usr/bin/env bash
    set -euo pipefail
    base=$(git merge-base HEAD origin/main)
    changed=$(git diff --diff-filter=d --name-only "$base" | grep -E '\.(hs|hs-boot)$' || true)
    if [ -n "$changed" ]; then
      echo "running {{ormolu}} --mode inplace"
      {{ormolu}} --mode inplace $changed
    fi

# check Haskell source code formatting using ormolu
check-format-hs:
    @echo "running {{ormolu}} --mode check"
    @{{ormolu}} --mode check $(git ls-files '*.hs' '*.hs-boot')

# check changed Haskell source code formatting using ormolu
check-format-hs-changed:
    #!/usr/bin/env bash
    set -euo pipefail
    base=$(git merge-base HEAD origin/main)
    changed=$(git diff --diff-filter=d --name-only "$base" | grep -E '\.(hs|hs-boot)$' || true)
    if [ -n "$changed" ]; then
      echo "running {{ormolu}} --mode check"
      {{ormolu}} --mode check $changed
    fi

# auto-format Nix source code using nixpkgs-fmt
format-nix:
    #!/usr/bin/env bash
    set -euo pipefail
    if command -v {{nix_fmt}} >/dev/null; then
      echo "running {{nix_fmt}}"
      {{nix_fmt}} $(git ls-files '*.nix' 'nix/*.nix')
    else
      echo "{{nix_fmt}} is not installed; skipping"
    fi

# check Nix source code formatting using nixpkgs-fmt
check-format-nix:
    #!/usr/bin/env bash
    set -euo pipefail
    if command -v {{nix_fmt}} >/dev/null; then
      echo "running {{nix_fmt}} --check"
      {{nix_fmt}} --check $(git ls-files '*.nix' 'nix/*.nix')
    else
      echo "{{nix_fmt}} is not installed; skipping"
    fi

# auto-format all Haskell and Nix source
format: format-hs format-nix

# auto-format changed Haskell source and all Nix source
format-changed: format-hs-changed format-nix

# check all Haskell and Nix formatting
check-format: check-format-hs check-format-nix

# check changed Haskell formatting and all Nix formatting
check-format-changed: check-format-hs-changed check-format-nix

# lint shell scripts using shellcheck
lint-shell:
    #!/usr/bin/env bash
    set -euo pipefail
    files=$(git ls-files '*.sh')
    if [ -n "$files" ]; then
      echo "running shellcheck"
      {{shellcheck}} $files
    fi

# lint changed shell scripts using shellcheck
lint-shell-changed:
    #!/usr/bin/env bash
    set -euo pipefail
    base=$(git merge-base HEAD origin/main)
    changed=$(git diff --diff-filter=d --name-only "$base" | grep -E '\.sh$' || true)
    if [ -n "$changed" ]; then
      echo "running shellcheck"
      {{shellcheck}} $changed
    fi

# build all Haskell packages
build:
    cabal build all --enable-tests --enable-benchmarks

# remove build artifacts
clean:
    cabal clean

# run all test suites
test:
    cabal test all

# build Haddock documentation
haddock:
    cabal haddock

# --- Release & publish ---

# fail unless tracked tree is clean and we're on an up-to-date main
_require-clean-main:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
      echo "error: uncommitted changes to tracked files; commit or stash first" >&2
      exit 1
    fi
    branch=$(git rev-parse --abbrev-ref HEAD)
    if [ "$branch" != "main" ]; then
      echo "error: must be on 'main' (currently on '$branch')" >&2
      exit 1
    fi
    git fetch --quiet origin main
    if [ "$(git rev-parse HEAD)" != "$(git rev-parse origin/main)" ]; then
      echo "error: local 'main' is out of sync with 'origin/main'; pull/push first" >&2
      exit 1
    fi

# fail unless the cabal version matches the top versioned changelog entry
_check-version:
    #!/usr/bin/env bash
    set -euo pipefail
    cabal_v=$(awk '/^version:/{print $2; exit}' monoidal-functors.cabal)
    log_v=$(awk '/^## [0-9]/{print $2; exit}' CHANGELOG.md)
    if [ "$cabal_v" != "$log_v" ]; then
      echo "error: cabal version ($cabal_v) does not match changelog version ($log_v)" >&2
      exit 1
    fi
    echo "version $cabal_v is consistent between cabal file and changelog"

# fail if the current cabal version already has a git tag
_require-unreleased:
    #!/usr/bin/env bash
    set -euo pipefail
    version=$(awk '/^version:/{print $2; exit}' monoidal-functors.cabal)
    if git rev-parse -q --verify "refs/tags/${version}" >/dev/null; then
      echo "error: tag ${version} already exists; is this version already released?" >&2
      exit 1
    fi
    echo "version ${version} has no existing tag"

# open a release PR: bump version, timestamp changelog, push branch, open PR
release VERSION: _require-clean-main
    #!/usr/bin/env bash
    set -euo pipefail
    version="{{VERSION}}"
    if ! [[ "$version" =~ ^[0-9]+(\.[0-9]+)*$ ]]; then
      echo "error: VERSION must be dotted digits, e.g. 0.3.0.0 (got '$version')" >&2
      exit 1
    fi
    if ! grep -q '^## Upcoming$' CHANGELOG.md; then
      echo "error: no '## Upcoming' section in CHANGELOG.md to promote" >&2
      exit 1
    fi
    date=$(date +%F)
    branch="release/${version}"
    git checkout -b "$branch"
    sed -i -E "s/^(version:[[:space:]]*).*/\1${version}/" monoidal-functors.cabal
    sed -i "0,/^## Upcoming$/s//## Upcoming\n\n## ${version} -- ${date}/" CHANGELOG.md
    git commit -am "Release ${version}"
    git push -u origin "$branch"
    body=$(awk -v h="## ${version} -- ${date}" '$0==h{f=1;next} /^## /{f=0} f' CHANGELOG.md)
    gh pr create --title "Release ${version}" --body "$body"

# upload a reversible Hackage candidate for preview (Hackage builds the docs)
publish-candidate: _require-clean-main _check-version
    #!/usr/bin/env bash
    set -euo pipefail
    version=$(awk '/^version:/{print $2; exit}' monoidal-functors.cabal)
    cabal sdist all
    sdist="dist-newstyle/sdist/monoidal-functors-${version}.tar.gz"
    [ -f "$sdist" ] || { echo "error: sdist not found at $sdist" >&2; exit 1; }
    cabal upload "$sdist"
    echo "Uploaded candidate. Review: https://hackage.haskell.org/package/monoidal-functors-${version}/candidate"

# final, irreversible Hackage publish then tag the release (Hackage builds the docs)
publish: _require-clean-main _check-version _require-unreleased test
    #!/usr/bin/env bash
    set -euo pipefail
    version=$(awk '/^version:/{print $2; exit}' monoidal-functors.cabal)
    # sanity gate: abort before publishing if Haddocks do not build (not uploaded)
    cabal haddock all
    cabal sdist all
    sdist="dist-newstyle/sdist/monoidal-functors-${version}.tar.gz"
    [ -f "$sdist" ] || { echo "error: sdist not found at $sdist" >&2; exit 1; }
    cabal upload --publish "$sdist"
    git tag -a "${version}" -m "Release ${version}"
    git push origin "${version}"
    echo "Published monoidal-functors-${version} to Hackage and pushed tag ${version}."
