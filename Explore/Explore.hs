import Idris.Main
import Idris.Core.TT
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.REPL
import Idris.Options
import IRTS.CodegenCommon

import IRTS.Compiler

import System.Environment
import System.Exit
import Control.Monad

import Util.System

getDecls :: CodeGenerator
getDecls ci = do
    let repr =  unwords $ map (\ x -> show x ++ "\n\n\n") (liftDecls ci)
    putStrLn repr
    writeFile (outputFile ci) repr

doStuff :: FilePath -> Idris ()
doStuff file = do 
    elabPrims
    loadInputs [file] Nothing
    mainProg <- elabMain
    ir <- compile (Via IBCFormat "malfunction") (file ++ ".lang.repr") (Just mainProg)
    runIO $ getDecls ir

main :: IO ()
main = do
     (file:_) <- getArgs
     runMain $ doStuff file