module IRTS.CodegenMalfunction(codegenMalfunction) where

import Idris.Core.TT
import qualified Idris.Core.CaseTree as CaseTree
import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Simplified

import Data.List
import Data.Char
import Data.Ord
import qualified Data.Map.Strict as Map
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
    render :: Sexp -> String -> String
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
    chars [] = []
    chars (c:cs) | okChar c = c:chars cs
                 | otherwise = "%" ++ show (ord c) ++ "%" ++ chars cs

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

    stringify :: [(Name, LDecl)] -> String
    stringify =  unwords . map (\decl -> show decl ++ "\n\n") 

shuffle :: [(Name, LDecl)] -> [Sexp] -> [Sexp]
shuffle decls rest = prelude ++ toBindings (Graph.stronglyConnComp (mapMaybe toNode decls))
  where
    conTagArity :: Map.Map Name (Int, Int)
    conTagArity = Map.fromList $ map makeMap conDecls
      where 
        conDecls :: [(Name, LDecl)]
        conDecls = filter (\x -> case x of
                                  (_, LConstructor _ _ _) -> True
                                  _ -> False) decls
        makeMap :: (Name, LDecl) -> (Name, (Int, Int))
        makeMap (_, LConstructor name tag arity) =  (name, (tag, arity))

    toBindings :: [Graph.SCC (Name, LDecl)] -> [Sexp]
    toBindings [] = rest
    toBindings (Graph.AcyclicSCC decl : comps) =
      case cgDecl conTagArity decl of
        Just sexp -> sexp : toBindings comps
        Nothing -> toBindings comps
    toBindings (Graph.CyclicSCC decls : comps) =
       S (A "rec" : mapMaybe (cgDecl conTagArity) decls) : toBindings comps
   
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

cgDecl :: Map.Map Name (Int, Int) -> (Name, LDecl) -> Maybe Sexp
cgDecl conMap (name, LFun _ _ args body) =
     Just $ S [cgName name, S [A "lambda", mkargs args, cgExp conMap body]]
    where
     mkargs :: [Name] -> Sexp
     mkargs [] = S [A "$%unused"]
    --  mkargs args = S $ map (cgSym . show . fst) $ zip [0..] args
     mkargs args = S $ map cgName args
cgDecl _  _ = Nothing

cgExp :: Map.Map Name (Int, Int) -> LExp -> Sexp
cgExp _ (LV name) = cgName name
-- I think in mlf functions need at least one argument
cgExp m (LApp _ fn []) = S [A "apply", cgExp m fn, KInt 0]
cgExp m (LApp _ fn args) = S (A "apply" : cgExp m fn : map (cgExp m) args)
cgExp _ (LLazyApp name []) = S [A "apply", cgName name , KInt 0] -- fixme
cgExp m (LLazyApp name args) = S (A "apply" : cgName name : map (cgExp m) args) --fixme
cgExp m (LLazyExp e) = cgExp m e
cgExp m (LForce e) = cgExp m e
cgExp m (LLet name exp body) = S [A "let", S [cgName name, cgExp m exp], cgExp m body]
cgExp m (LLam args body) = S [A "lambda", S $ map cgName args, cgExp m body] 
cgExp m (LProj e idx) = S [A "field", KInt (idx + 1), cgExp m e]
cgExp m (LCon _ tag name args) = 
  S (A "block": S [A "tag", KInt (tag `mod` 200)] : KInt tag : map (cgExp m) args)
  -- why is tag twice? wastei
cgExp conMap (LCase _ e cases) = cgSwitch conMap e cases
cgExp _ (LConst k) = cgConst k
cgExp _ (LForeign fn ret args) = error "no FFI" -- fixme
cgExp m (LOp prim args) = cgOp m prim args
cgExp _ LNothing = KInt 0
cgExp _ (LError s) =
   S [A "apply", S [A "global", A "$Pervasives", A "$failwith"],
    KStr $ "error: " ++ show s]

cgSwitch :: Map.Map Name (Int, Int) -> LExp -> [LAlt] -> Sexp
cgSwitch conMap e cases =
  S [A "let", S [scr, cgExp conMap e],
     S $ [A "switch", scr] ++
         map cgTagGroup taggroups ++
         concatMap cgNonTagCase cases]
  where
    scr :: Sexp
    scr = A "$A%sw"    

    getTag :: Name -> Int
    getTag n = case Map.lookup n conMap of 
          Just (tag, arity) -> tag
          Nothing -> error "This should never happen"

    tagcases :: [(Int, LAlt)]
    tagcases = concatMap (\c -> case c of
       c@(LConCase tag n args body) -> [(getTag n, c)]
       _ -> []) cases -- better filter and then map?

    taggroups :: [(Int, [LAlt])]
    taggroups =
      map (\cases -> ((fst $ head cases) `mod` 200, map snd cases)) $
      groupBy ((==) `on` ((`mod` 200) . fst)) $
      sortBy (comparing fst) $ tagcases -- why sort?

    cgTagGroup ::  (Int, [LAlt]) -> Sexp
    cgTagGroup (tagmod, cases) =
      S [S [A "tag", KInt tagmod], cgTagClass cases]
--    cgTagClass [c] =
--      cgProjections c
    cgTagClass :: [LAlt] -> Sexp
    cgTagClass cases =
      S (A "switch" : S [A "field", KInt 0, scr] :
         [S [KInt (getTag n), cgProjections c] | c@(LConCase tag n _ _) <- cases])

    cgProjections :: LAlt -> Sexp
    cgProjections (LConCase tag name args body) =
      S ([A "let"] ++
         zipWith (\i n -> S [cgName n, S [A "field", KInt (i + 1), scr]]) [0..] args ++ 
         [cgExp conMap body])

    cgNonTagCase :: LAlt -> [Sexp]
    cgNonTagCase (LConCase _ _ _ _) = []
    cgNonTagCase (LConstCase (I n) e) = [S [KInt n, cgExp conMap e]]
    cgNonTagCase (LConstCase (BI n) e) = [S [KInt (fromInteger n), cgExp conMap e]]
    cgNonTagCase (LConstCase (Ch c) e) = [S [KInt (ord c), cgExp conMap e]]
    cgNonTagCase (LConstCase k e) = error $ "unsupported constant selector: " ++ show k
    cgNonTagCase (LDefaultCase e) = [S [A "_", S [A "tag", A "_"], cgExp conMap e]]
    
arithSuffix :: ArithTy -> String
arithSuffix (ATInt ITNative) = ""
arithSuffix (ATInt ITChar) = ""
arithSuffix (ATInt ITBig) = ".ibig"
arithSuffix s = error $ "unsupported arithmetic type: " ++ show s


stdlib :: Map.Map Name (Int, Int) -> [String] -> [LExp] -> Sexp
stdlib  m path args =
   S (A "apply" : S (A "global" : map (A . ('$':)) path) : map (cgExp m) args)

pervasive :: Map.Map Name (Int, Int) -> String -> [LExp] -> Sexp
pervasive m f args = stdlib m ["Pervasives", f] args

cgOp :: Map.Map Name (Int, Int) -> PrimFn -> [LExp] -> Sexp
cgOp m LStrConcat [l, r] =
  S [A "apply", S [A "global", A "$Pervasives", A "$^"], cgExp m l, cgExp m r]
cgOp m LStrCons [c, r] =
  S [A "apply", S [A "global", A "$Pervasives", A "$^"],
     S [A "apply", S [A "global", A "$String", A "$make"],
        KInt 1, cgExp m c], cgExp m r] -- fixme safety
cgOp m LWriteStr [_, str] =
  S [A "apply", S [A "global", A "$Pervasives", A "$print_string"], cgExp m str]
cgOp m LReadStr [_] =
   S [A "apply", S [A "global", A "$Pervasives", A "$read_line"], KInt 0]
cgOp m (LPlus t) args = S (A ("+" ++ arithSuffix t) : map  (cgExp m) args)
cgOp m (LMinus t) args = S (A ("-" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LTimes t) args = S (A ("*" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LSRem t) args = S (A ("%" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LEq t) args = S (A ("==" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LSLt t) args = S (A ("<" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LSGt t) args = S (A (">" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LSLe t) args = S (A ("<=" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LSGe t) args = S (A (">=" ++ arithSuffix t) : map (cgExp m) args)
cgOp m (LIntStr ITNative) args = pervasive m "string_of_int" args
cgOp m (LIntStr ITBig) args = stdlib m ["Z", "to_string"] args
cgOp m (LChInt _) [x] = cgExp m x
cgOp m (LIntCh _) [x] = cgExp m x
cgOp m (LSExt _ _) [x] = cgExp m x -- FIXME
cgOp m (LTrunc _ _) [x] = cgExp m x -- FIXME
cgOp m (LStrInt ITNative) [x] = pervasive m "int_of_string" [x]
cgOp m LStrEq args = stdlib m ["String", "equal"] args
cgOp m LStrLen [x] = S [A "length.byte", cgExp m x]
cgOp m LStrHead [x] = S [A "load.byte", cgExp m x, KInt 0]
cgOp m LStrIndex args = S (A "store.byte" : map (cgExp m) args)
cgOp m LStrTail [x] =
   S [A "apply", S [A "global", A "$String", A "$sub"], cgExp m x
   , KInt 1, S [A "-", cgOp m LStrLen [x], KInt 1]]
cgOp m LStrRev [s] = S [A "apply", A "$%strrev", cgExp m s]
cgOp m p _ = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]


cgConst :: Const -> Sexp
cgConst (I n) = KInt n
cgConst (BI n) =  A $ show n ++ ".ibig"
cgConst (Fl x) = error "no floats"
cgConst (Ch i) = KInt (ord i)
cgConst (Str s) = KStr s
cgConst k = error $ "unimplemented constant " ++ show k