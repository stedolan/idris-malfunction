module Main where

import Idris.Main
import Idris.Core.TT
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Options

import IRTS.Compiler
import IRTS.CodegenMalfunction

import System.Environment
import System.Exit

data Opts = Opts { inputs :: [FilePath],
                   output :: FilePath,
                   isEval :: Bool }

showUsage = do putStrLn "A code generator which is intended to be called by the compiler, not by a user."
               putStrLn "Usage: idris-malfunction <ibc-files> [-o <output-file>]"
               exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do xs <- getArgs
             return $ process (Opts [] "a.out" False) xs
  where
    process opts ("-o":o:xs) = process (opts { output = o }) xs
    process opts ("--interface":xs) = process (opts {isEval = True}) xs
    -- process opts ("--interface":xs) = error "this seems important, what do?"
    process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
    process opts [] = opts

malfunction_main :: Opts -> Idris ()
malfunction_main opts = do elabPrims
                           loadInputs (inputs opts) Nothing
                           mainProg <- elabMain
                           ir <- compile (Via IBCFormat "malfunction") (output opts) (Just mainProg)
                           runIO $ if isEval opts == False 
                                    then codegenMalfunction ir
                                    else evalMalfunction ir

main :: IO ()
main = do opts <- getOpts
          if (null (inputs opts))
             then showUsage
             else  runMain (malfunction_main opts)