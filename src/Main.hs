module Main where

import Idris.Main
import Idris.Core.TT
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Options

import IRTS.Compiler
import IRTS.CodegenMalfunction
import IRTS.CodegenCommon

import System.Environment
import System.Exit



data Opts = Opts { inputs :: [FilePath],
                   output :: FilePath,
                   interface :: Bool }



showUsage :: IO a
showUsage = do
  putStrLn
    "A code generator which is intended to be called by the compiler, not by a user."
  putStrLn "Usage: idris-malfunction <ibc-files> [-o <output-file>]"
  exitSuccess



getOpts :: IO Opts
getOpts = process (Opts [] "a.out" False) <$> getArgs
 where
  process opts ("-o" : o      : xs) = process (opts { output = o }) xs
  process opts ("--interface" : xs) = process (opts { interface = True }) xs
  process opts (x : xs) = process (opts { inputs = x : inputs opts }) xs
  process opts []                   = opts



malfunction_main :: Opts -> Idris ()
malfunction_main opts = do
  elabPrims
  loadInputs (inputs opts) Nothing
  mainProg <- elabMain
  ir <- compile (Via IBCFormat "malfunction") (output opts) (Just mainProg)
  runIO $ codegenMalfunction (ir { interfaces = interface opts })



main :: IO ()
main = do
  opts <- getOpts
  if null (inputs opts) then showUsage else runMain (malfunction_main opts)
