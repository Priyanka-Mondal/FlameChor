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
bindir     = "/home/priyanka/Flame/.stack-work/install/x86_64-linux/18f66e4077c12dac9dbc69fc83a04e69423e035e61d91b5d4c2edfe282df2815/9.4.7/bin"
libdir     = "/home/priyanka/Flame/.stack-work/install/x86_64-linux/18f66e4077c12dac9dbc69fc83a04e69423e035e61d91b5d4c2edfe282df2815/9.4.7/lib/x86_64-linux-ghc-9.4.7/flame-runtime-0.1.0.2-HI5LguuKnWzImIfC9XLSwM-bookseller-1-simple"
dynlibdir  = "/home/priyanka/Flame/.stack-work/install/x86_64-linux/18f66e4077c12dac9dbc69fc83a04e69423e035e61d91b5d4c2edfe282df2815/9.4.7/lib/x86_64-linux-ghc-9.4.7"
datadir    = "/home/priyanka/Flame/.stack-work/install/x86_64-linux/18f66e4077c12dac9dbc69fc83a04e69423e035e61d91b5d4c2edfe282df2815/9.4.7/share/x86_64-linux-ghc-9.4.7/flame-runtime-0.1.0.2"
libexecdir = "/home/priyanka/Flame/.stack-work/install/x86_64-linux/18f66e4077c12dac9dbc69fc83a04e69423e035e61d91b5d4c2edfe282df2815/9.4.7/libexec/x86_64-linux-ghc-9.4.7/flame-runtime-0.1.0.2"
sysconfdir = "/home/priyanka/Flame/.stack-work/install/x86_64-linux/18f66e4077c12dac9dbc69fc83a04e69423e035e61d91b5d4c2edfe282df2815/9.4.7/etc"

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
