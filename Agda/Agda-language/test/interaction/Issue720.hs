{-# LANGUAGE RecordWildCards #-}

import Control.Monad
import System.Directory

import RunAgda

file          = "Issue720.agda"
interfaceFile = file ++ "i"

main :: IO ()
main = runAgda [] $ \(AgdaCommands { .. }) -> do

  let load = do
        send $ command "load" file (Just "Interactive Direct") (Just [])
        echoUntilPrompt

  -- Discard the first prompt.
  echoUntilPrompt

  -- Load the file, and wait for Agda to complete.
  load

  -- Remove the interface file.
  exists <- doesFileExist interfaceFile
  when exists $ removeFile interfaceFile

  -- Reload.
  load

  return ()
