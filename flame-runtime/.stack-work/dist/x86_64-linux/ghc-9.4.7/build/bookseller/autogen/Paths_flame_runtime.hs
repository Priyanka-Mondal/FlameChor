{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_flame_runtime (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
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
version = Version [0,1,0,2] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/manu/myFlame/flame/.stack-work/install/x86_64-linux/98ce0bd3bb3851922c1334b62ec3a4523273a011b466dc7e1153f8084b3ed2d0/9.4.7/bin"
libdir     = "/home/manu/myFlame/flame/.stack-work/install/x86_64-linux/98ce0bd3bb3851922c1334b62ec3a4523273a011b466dc7e1153f8084b3ed2d0/9.4.7/lib/x86_64-linux-ghc-9.4.7/flame-runtime-0.1.0.2-EIxyWlqARRDHj7kLFhCye8-bookseller"
dynlibdir  = "/home/manu/myFlame/flame/.stack-work/install/x86_64-linux/98ce0bd3bb3851922c1334b62ec3a4523273a011b466dc7e1153f8084b3ed2d0/9.4.7/lib/x86_64-linux-ghc-9.4.7"
datadir    = "/home/manu/myFlame/flame/.stack-work/install/x86_64-linux/98ce0bd3bb3851922c1334b62ec3a4523273a011b466dc7e1153f8084b3ed2d0/9.4.7/share/x86_64-linux-ghc-9.4.7/flame-runtime-0.1.0.2"
libexecdir = "/home/manu/myFlame/flame/.stack-work/install/x86_64-linux/98ce0bd3bb3851922c1334b62ec3a4523273a011b466dc7e1153f8084b3ed2d0/9.4.7/libexec/x86_64-linux-ghc-9.4.7/flame-runtime-0.1.0.2"
sysconfdir = "/home/manu/myFlame/flame/.stack-work/install/x86_64-linux/98ce0bd3bb3851922c1334b62ec3a4523273a011b466dc7e1153f8084b3ed2d0/9.4.7/etc"

getBinDir     = catchIO (getEnv "flame_runtime_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "flame_runtime_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "flame_runtime_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "flame_runtime_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "flame_runtime_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "flame_runtime_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
