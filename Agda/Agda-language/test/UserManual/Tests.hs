{-# LANGUAGE CPP               #-}
{-# LANGUAGE DoAndIfThenElse   #-}
{-# LANGUAGE OverloadedStrings #-}

module UserManual.Tests where

import Succeed.Tests (mkSucceedTest)

import Test.Tasty
import System.FilePath

import Utils

testDir :: FilePath
testDir = "doc" </> "user-manual"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir Rec testDir

  -- Andreas, Victor, 2016-07-25:
  -- Don't --ignore-interfaces for user manual test!
  -- Otherwise parts of the standard library are type-checked again.
  -- Ulf, 2017-02-24: Or, we could just not depend on the standard library
  -- for the user manual...
  let extraOpts = ["--ignore-interfaces"] :: [String]

  let tests' = map (mkSucceedTest extraOpts testDir) inpFiles

  return $ testGroup "UserManual" tests'
