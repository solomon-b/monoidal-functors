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
