module IRTS.CodegenMalfunction(codegenMalfunction) where

import Idris.Core.TT
import qualified Idris.Core.CaseTree as CaseTree
import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Simplified

import Data.List
import Data.Char
import Data.Ord
import qualified Data.Set as S
import qualified Data.Graph as Graph
import Data.Maybe(mapMaybe)
import Data.Function (on)
import Control.Monad
import Control.Exception

import System.Process
import System.Directory


data Sexp = S [Sexp] | A String | KInt Int | KStr String
-- shoudln't we have a KBigInt and a KFloat etc?

instance Show Sexp where
  show s = render s "" where
    render (S s) k = "(" ++ foldr render (") " ++ k) s
    render (A s) k = s ++ " " ++ k
    render (KInt n) k = show n ++ " " ++ k
    render (KStr s) k = show s ++ " " ++ k


okChar :: Char -> Bool
okChar c = (isAscii c && isAlpha c) || isDigit c || c `elem` ".&|$+-!@#^*~?<>=_"

cgSym :: String -> Sexp
cgSym s = A ('$' : chars s)
  where
    chars :: String -> String
    chars (c:cs) | okChar c = c:chars cs
                 | otherwise = "%" ++ show (ord c) ++ "%" ++ chars cs
    chars [] = []

codegenMalfunction :: CodeGenerator
codegenMalfunction ci = do
  let langDeclarations = liftDecls ci
  writeFile langFile $ stringify langDeclarations
  writeFile tmp $ show $
    S (A "module" : shuffle langDeclarations
       [S [A "_", S [A "apply", cgName (sMN 0 "runMain"), KInt 0]],
        S [A "export"]])
  callCommand $ "malfunction fmt " ++ tmp ++ " > " ++ mlfFile
  catch
   (callCommand $ "malfunction compile -o " ++ outputFile ci ++ " " ++ mlfFile) handler
   -- use tmp, it's faster
  removeFile tmp
  where
    handler :: SomeException -> IO ()
    handler ex = putStrLn $ "Caught exception: " ++ show ex
    tmp = "idris_malfunction_output.mlf"
    mlfFile = outputFile ci ++ ".mlf"
    langFile = outputFile ci ++ ".lang"
    stringify =  unwords . map (\decl -> show decl ++ "\n\n") 

shuffle :: [(Name, LDecl)] -> [Sexp] -> [Sexp]
shuffle decls rest = prelude ++ toBindings (Graph.stronglyConnComp (mapMaybe toNode decls))
  where
    toBindings :: [Graph.SCC (Name, LDecl)] -> [Sexp]
    toBindings [] = rest
    toBindings (Graph.AcyclicSCC decl : comps) =
      case cgDecl decl of
        Just sexp -> sexp : toBindings comps
        Nothing -> toBindings comps
    toBindings (Graph.CyclicSCC decls : comps) = S (A "rec" : mapMaybe cgDecl decls) : toBindings comps
   
    toNode :: (Name, LDecl) -> Maybe ((Name, LDecl), Name, [Name])
    toNode decl@(name, LFun _ _ _ body) =
       Just (decl, name, S.toList (free body))
    toNode _ = Nothing

    freeCase :: LAlt -> S.Set Name
    freeCase (LConCase _ name names exp) =
       S.unions $ S.singleton name : free exp : map S.singleton names 
    freeCase (LConstCase _ exp) = free exp
    freeCase (LDefaultCase exp) = free exp
    
    free :: LExp -> S.Set Name
    free (LV name) = S.singleton name
    free (LApp _ exp exps) = S.unions $ free exp : map free exps
    free (LLazyApp name exps) = S.unions $ S.singleton name : map free exps
    free (LLazyExp exp) = free exp
    free (LForce exp) = free exp
    free (LLet name exp1 exp2) =
       S.unions [S.singleton name, free exp1, free exp2]
    free (LLam names exp) = S.unions $ free exp : map S.singleton names
    free (LProj exp _) = free exp
    free (LCon _ _ name exps) = S.unions $ S.singleton name : map free exps
    free (LCase _ exp alts) = S.unions $ free exp : map freeCase alts
    free (LConst _ ) = S.empty
    free (LForeign _ _ args) = S.unions $ map (free . snd) args
    free (LOp _ exps) = S.unions $ map free exps
    free (LNothing) = S.empty
    free (LError _) = S.empty
    
    prelude :: [Sexp]
    prelude = [
      S [A"$%strrev",
         S [A"lambda", S [A"$s"],
              S [A"let", S [A"$n", S [A"-", S [A"length.byte", A"$s"], KInt 1]],
                 S [A"apply", S[A"global", A"$String", A"$mapi"],
                    S[A"lambda", S[A"$i", A"$c"],
                      S[A"load.byte", A"$s", S[A"-", A"$n", A"$i"]]],
                    A"$s"]]]]
      ]


cgName :: Name -> Sexp
cgName = cgSym . showCG

-- cgVar :: LVar -> Sexp
-- cgVar (Loc n) = cgSym (show n)
-- cgVar (Glob n) = cgName n

cgDecl :: (Name, LDecl) -> Maybe Sexp
cgDecl (name, LFun _ _ args body) =
     Just $ S [cgName name, S [A "lambda", mkargs args, cgExp body]]
    where
     mkargs :: [Name] -> Sexp
     mkargs [] = S [A "$%unused"]
    --  mkargs args = S $ map (cgSym . show . fst) $ zip [0..] args
     mkargs args = S $ map cgName args
cgDecl _ = Nothing

cgExp :: LExp -> Sexp
cgExp (LV name) = cgName name
-- I think in mlf functions need at least one argument
cgExp (LApp _ fn []) = S [A "apply", cgExp fn, KInt 0]
cgExp (LApp _ fn args) = S (A "apply" : cgExp fn : map cgExp args)
cgExp (LLazyApp name []) = S [A "apply", cgName name , KInt 0] -- fixme
cgExp (LLazyApp name args) = S (A "apply" : cgName name : map cgExp args) --fixme
cgExp (LLazyExp e) = cgExp e
cgExp (LForce e) = cgExp e
cgExp (LLet name exp body) = S [A "let", S [cgName name, cgExp exp], cgExp body]
cgExp (LLam args body) = S [A "lambda", S $ map cgName args, cgExp body] 
cgExp (LProj e idx) = S [A "field", KInt (idx + 1), cgExp e]
cgExp (LCon _ tag name args) = 
  S (A "block": S [A "tag", KInt (tag `mod` 200)] : KInt tag : map cgExp args)
  -- why is tag twice? 
cgExp (LCase _ e cases) = cgSwitch e cases
cgExp (LConst k) = cgConst k
cgExp (LForeign fn ret args) = error "no FFI" -- fixme
cgExp (LOp prim args) = cgOp prim args
cgExp LNothing = KInt 0
cgExp (LError s) =
   S [A "apply", S [A "global", A "$Pervasives", A "$failwith"],
    KStr $ "error: " ++ show s]

cgSwitch :: LExp -> [LAlt] -> Sexp
cgSwitch e cases =
  S [A "let", S [scr, cgExp e],
     S $ [A "switch", scr] ++
         map cgTagGroup taggroups ++
         concatMap cgNonTagCase cases]
  where
    scr = A "$%sw"    
    tagcases = concatMap (\c -> case c of
       c@(LConCase tag n args body) -> [(tag, c)]
       _ -> []) cases -- better with filter and then map?
    taggroups =
      map (\cases -> ((fst $ head cases) `mod` 200, map snd cases)) $
      groupBy ((==) `on` ((`mod` 200) . fst)) $
      sortBy (comparing fst) $ tagcases -- why sort?
    cgTagGroup (tagmod, cases) =
      S [S [A "tag", KInt tagmod], cgTagClass cases]
--    cgTagClass [c] =
--      cgProjections c
    cgTagClass cases =
      S (A "switch" : S [A "field", KInt 0, scr] :
         [S [KInt tag, cgProjections c] | c@(LConCase tag _ _ _) <- cases])
    cgProjections (LConCase tag name args body) =
      S ([A "let"] ++
         zipWith (\i n -> S [cgName n, S [A "field", KInt (i + 1), scr]]) [0..] args ++ 
         [cgExp body])
    cgNonTagCase (LConCase _ _ _ _) = []
    cgNonTagCase (LConstCase (I n) e) = [S [KInt n, cgExp e]]
    cgNonTagCase (LConstCase (BI n) e) = [S [KInt (fromInteger n), cgExp e]]
    cgNonTagCase (LConstCase (Ch c) e) = [S [KInt (ord c), cgExp e]]
    cgNonTagCase (LConstCase k e) = error $ "unsupported constant selector: " ++ show k
    cgNonTagCase (LDefaultCase e) = [S [A "_", S [A "tag", A "_"], cgExp e]]
    
arithSuffix :: ArithTy -> String
arithSuffix (ATInt ITNative) = ""
arithSuffix (ATInt ITChar) = ""
arithSuffix (ATInt ITBig) = ".ibig"
arithSuffix s = error $ "unsupported arithmetic type: " ++ show s


stdlib :: [String] -> [LExp] -> Sexp
stdlib path args =
   S (A "apply" : S (A "global" : map (A . ('$':)) path) : map cgExp args)

pervasive :: String -> [LExp] -> Sexp
pervasive f args = stdlib ["Pervasives", f] args

cgOp :: PrimFn -> [LExp] -> Sexp
cgOp LStrConcat [l, r] =
  S [A "apply", S [A "global", A "$Pervasives", A "$^"], cgExp l, cgExp r]
cgOp LStrCons [c, r] =
  S [A "apply", S [A "global", A "$Pervasives", A "$^"],
     S [A "apply", S [A "global", A "$String", A "$make"],
        KInt 1, cgExp c], cgExp r] -- fixme safety
cgOp LWriteStr [_, str] =
  S [A "apply", S [A "global", A "$Pervasives", A "$print_string"], cgExp str]
cgOp LReadStr [_] = S [A "apply", S [A "global", A "$Pervasives", A "$read_line"], KInt 0]
cgOp (LPlus t) args = S (A ("+" ++ arithSuffix t) : map cgExp args)
cgOp (LMinus t) args = S (A ("-" ++ arithSuffix t) : map cgExp args)
cgOp (LTimes t) args = S (A ("*" ++ arithSuffix t) : map cgExp args)
cgOp (LSRem t) args = S (A ("%" ++ arithSuffix t) : map cgExp args)
cgOp (LEq t) args = S (A ("==" ++ arithSuffix t) : map cgExp args)
cgOp (LSLt t) args = S (A ("<" ++ arithSuffix t) : map cgExp args)
cgOp (LSGt t) args = S (A (">" ++ arithSuffix t) : map cgExp args)
cgOp (LSLe t) args = S (A ("<=" ++ arithSuffix t) : map cgExp args)
cgOp (LSGe t) args = S (A (">=" ++ arithSuffix t) : map cgExp args)
cgOp (LIntStr ITNative) args = pervasive "string_of_int" args
cgOp (LIntStr ITBig) args = stdlib ["Z", "to_string"] args
cgOp (LChInt _) [x] = cgExp x
cgOp (LIntCh _) [x] = cgExp x
cgOp (LSExt _ _) [x] = cgExp x -- FIXME
cgOp (LTrunc _ _) [x] = cgExp x -- FIXME
cgOp (LStrInt ITNative) [x] = pervasive "int_of_string" [x]
cgOp LStrEq args = stdlib ["String", "equal"] args
cgOp LStrLen [x] = S [A "length.byte", cgExp x]
cgOp LStrHead [x] = S [A "load.byte", cgExp x, KInt 0]
cgOp LStrIndex args = S (A "store.byte" : map cgExp args)
cgOp LStrTail [x] =
   S [A "apply", S [A "global", A "$String", A "$sub"], cgExp x
   , KInt 1, S [A "-", cgOp LStrLen [x], KInt 1]]
cgOp LStrRev [s] = S [A "apply", A "$%strrev", cgExp s]
cgOp p _ = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]


cgConst :: Const -> Sexp
cgConst (I n) = KInt n
cgConst (BI n) =  A $ show n ++ ".ibig"
cgConst (Fl x) = error "no floats"
cgConst (Ch i) = KInt (ord i)
cgConst (Str s) = KStr s
cgConst k = error $ "unimplemented constant " ++ show k