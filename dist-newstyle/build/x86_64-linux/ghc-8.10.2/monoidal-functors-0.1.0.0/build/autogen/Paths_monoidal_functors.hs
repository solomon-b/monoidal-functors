{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_monoidal_functors (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/solomon/.cabal/bin"
libdir     = "/home/solomon/.cabal/lib/x86_64-linux-ghc-8.10.2/monoidal-functors-0.1.0.0-inplace"
dynlibdir  = "/home/solomon/.cabal/lib/x86_64-linux-ghc-8.10.2"
datadir    = "/home/solomon/.cabal/share/x86_64-linux-ghc-8.10.2/monoidal-functors-0.1.0.0"
libexecdir = "/home/solomon/.cabal/libexec/x86_64-linux-ghc-8.10.2/monoidal-functors-0.1.0.0"
sysconfdir = "/home/solomon/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "monoidal_functors_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "monoidal_functors_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "monoidal_functors_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "monoidal_functors_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "monoidal_functors_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "monoidal_functors_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
