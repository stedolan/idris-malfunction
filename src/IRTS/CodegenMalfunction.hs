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
import Data.Function (on)
import Control.Monad

import System.Process
import System.Directory



data Sexp = S [Sexp] | A String | KInt Int | KStr String

instance Show Sexp where
  show s = render s "" where
    render (S s) k = "(" ++ foldr render (") " ++ k) s
    render (A s) k = s ++ " " ++ k
    render (KInt n) k = show n ++ " " ++ k
    render (KStr s) k = show s ++ " " ++ k


okChar c = (isAscii c && isAlpha c) || isDigit c || c `elem` ".&|$+-!@#^*~?<>=_"

cgSym s = A ('$' : chars s)
  where
    chars (c:cs) | okChar c = c:chars cs
                 | otherwise = "%" ++ show (ord c) ++ "%" ++ chars cs
    chars [] = []

codegenMalfunction :: CodeGenerator
codegenMalfunction ci = do
  writeFile tmp $ show $
    S (A "module" : shuffle (simpleDecls ci)
       [S [A "_", S [A "apply", cgName (sMN 0 "runMain"), KInt 0]],
        S [A "export"]])
  callCommand $ "malfunction compile -o '" ++ outputFile ci ++ "' '" ++ tmp ++ "'"
  removeFile tmp
  where
    tmp = "idris_malfunction_output.mlf"

shuffle decls rest = prelude ++ toBindings (Graph.stronglyConnComp (map toNode decls))
  where
    toBindings [] = rest
    toBindings (Graph.AcyclicSCC decl : comps) = cgDecl decl : toBindings comps
    toBindings (Graph.CyclicSCC decls : comps) = S (A "rec" : map cgDecl decls) : toBindings comps
    
    toNode decl@(name, SFun _ _ _ body) =
      (decl, name, S.toList (free body))

    freev (Glob n) = S.singleton n
    freev (Loc k) = S.empty

    -- stupid over-approximation, since global names not shadowed
    free (SV v) = freev v
    free (SApp _ n _) = S.singleton n
    free (SLet v e1 e2) = S.unions [freev v, free e1, free e2]
    free (SUpdate v e) = S.unions [freev v, free e]
    free (SCon (Just v) _ n vs) = S.unions (freev v : S.singleton n : map freev vs)
    free (SCon Nothing _ n vs) = S.unions (S.singleton n : map freev vs)    
    free (SCase _ v cases) = S.unions (freev v : map freeCase cases)
    free (SChkCase v cases) = S.unions (freev v : map freeCase cases)
    free (SProj v _) = freev v
    free (SConst _) = S.empty
    free (SForeign _ _ args) = S.unions (map (freev . snd) args)
    free (SOp _ args) = S.unions (map freev args)
    free (SNothing) = S.empty
    free (SError s) = S.empty

    freeCase (SConCase _ _ n ns e) = S.unions [S.singleton n, S.fromList ns, free e]
    freeCase (SConstCase _ e) = free e
    freeCase (SDefaultCase e) = free e

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

cgVar (Loc n) = cgSym (show n)
cgVar (Glob n) = cgName n

cgDecl :: (Name, SDecl) -> Sexp
cgDecl (name, SFun _ args i body) = S [cgName name, S [A "lambda", mkargs args, cgExp body]]
  where
    mkargs [] = S [A "$%unused"]
    mkargs args = S $ map (cgVar . Loc . fst) $ zip [0..] args

cgExp :: SExp -> Sexp
cgExp (SV v) = cgVar v
cgExp (SApp _ fn []) = S [A "apply", cgName fn, KInt 0]
cgExp (SApp _ fn args) = S (A "apply" : cgName fn : map cgVar args)
cgExp (SLet v e body) = S [A "let", S [cgVar v, cgExp e], cgExp body]
cgExp (SUpdate v e) = cgExp e
cgExp (SProj e idx) = S [A "field", KInt (idx + 1), cgVar e]
cgExp (SCon _ tag name args) = S (A "block": S [A "tag", KInt (tag `mod` 200)] : KInt tag : map cgVar args)
cgExp (SCase _ e cases) = cgSwitch e cases
cgExp (SChkCase e cases) = cgSwitch e cases
cgExp (SConst k) = cgConst k
cgExp (SForeign fn ret args) = error "no FFI"
cgExp (SOp prim args) = cgOp prim args
cgExp SNothing = KInt 0
cgExp (SError s) = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "error: " ++ show s]

cgSwitch e cases =
  S [A "let", S [scr, cgVar e],
     S $ [A "switch", scr] ++
         map cgTagGroup taggroups ++
         concatMap cgNonTagCase cases]
  where
    scr = A "$%sw"    
    tagcases = concatMap (\c -> case c of
       c@(SConCase lv tag n args body) -> [(tag, c)]
       _ -> []) cases
    taggroups =
      map (\cases -> ((fst $ head cases) `mod` 200, map snd cases)) $
      groupBy ((==) `on` ((`mod` 200) . fst)) $
      sortBy (comparing fst) $ tagcases
    cgTagGroup (tagmod, cases) =
      S [S [A "tag", KInt tagmod], cgTagClass cases]
--    cgTagClass [c] =
--      cgProjections c
    cgTagClass cases =
      S (A "switch" : S [A "field", KInt 0, scr] :
         [S [KInt tag, cgProjections c] | c@(SConCase _ tag _ _ _) <- cases])
    cgProjections (SConCase lv tag n args body) =
      S ([A "let"] ++
         zipWith3 (\v i n -> S [cgVar (Loc v), S [A "field", KInt (i+1), scr]]) [lv..] [0..] args ++
         [cgExp body])
    cgNonTagCase (SConCase _ _ _ _ _) = []
    cgNonTagCase (SConstCase (I n) e) = [S [KInt n, cgExp e]]
    cgNonTagCase (SConstCase (BI n) e) = [S [KInt (fromInteger n), cgExp e]]
    cgNonTagCase (SConstCase (Ch c) e) = [S [KInt (ord c), cgExp e]]
    cgNonTagCase (SConstCase k e) = error $ "unsupported constant selector: " ++ show k
    cgNonTagCase (SDefaultCase e) = [S [A "_", S [A "tag", A "_"], cgExp e]]
    

intSuffix (ITNative)     = ".int"
intSuffix (ITChar)       = ""
--intSuffix (ITFixed IT32) = ".i32"
--intSuffix (ITFixed IT64) = ".i64"
intSuffix ITBig          = ".ibig"
intSuffix s = error $ "unsupported integer type: " ++ show s

arithSuffix (ATInt x) = intSuffix x
arithSuffix s = error $ "unsupported arithmetic type: " ++ show s


stdlib path args = S (A "apply" : S (A "global" : map (A . ('$':)) path) : map cgVar args)

pervasive f args = stdlib ["Pervasives", f] args

cgOp LStrConcat [l, r] =
  S [A "apply", S [A "global", A "$Pervasives", A "$^"], cgVar l, cgVar r]
cgOp LStrCons [c, r] =
  S [A "apply", S [A "global", A "$Pervasives", A "$^"],
     S [A "apply", S [A "global", A "$String", A "$make"],
        KInt 1, cgVar c], cgVar r] -- fixme safety
cgOp LWriteStr [_, str] =
  S [A "apply", S [A "global", A "$Pervasives", A "$print_string"], cgVar str]
cgOp LReadStr [_] = S [A "apply", S [A "global", A "$Pervasives", A "$read_line"], KInt 0]

cgOp p@(LPlus (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LPlus (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LPlus t) args = S (A ("+" ++ arithSuffix t) : map cgVar args)
cgOp p@(LMinus (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LMinus (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LMinus t) args = S (A ("-" ++ arithSuffix t) : map cgVar args)
cgOp p@(LTimes (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LTimes (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LTimes t) args = S (A ("*" ++ arithSuffix t) : map cgVar args)
cgOp p@(LSDiv (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSDiv (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSDiv t) args = S (A ("/" ++ arithSuffix t) : map cgVar args)
cgOp p@(LSRem (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSRem (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSRem t) args = S (A ("%" ++ arithSuffix t) : map cgVar args)

cgOp p@(LEq (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LEq (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LEq t) args = S (A ("==" ++ arithSuffix t) : map cgVar args)
cgOp p@(LSLt (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSLt (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSLt t) args = S (A ("<" ++ arithSuffix t) : map cgVar args)
cgOp p@(LSGt (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSGt (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSGt t) args = S (A (">" ++ arithSuffix t) : map cgVar args)
cgOp p@(LSLe (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSLe (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSLe t) args = S (A ("<=" ++ arithSuffix t) : map cgVar args)
cgOp p@(LSGe (ATInt (ITFixed IT8))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSGe (ATInt (ITFixed IT16))) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSGe t) args = S (A (">=" ++ arithSuffix t) : map cgVar args)

cgOp p@(LSHL (ITFixed IT8)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSHL (ITFixed IT16)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSHL t) args = S (A ("<<" ++ intSuffix t) : map cgVar args) 

cgOp p@(LLSHR (ITFixed IT8)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LLSHR (ITFixed IT16)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LLSHR t) args = S (A (">>" ++ intSuffix t) : map cgVar args) 

cgOp p@(LASHR (ITFixed IT8)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LASHR (ITFixed IT16)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LASHR t) args = S (A ("a>>" ++ intSuffix t) : map cgVar args) 

cgOp p@(LAnd (ITFixed IT8)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LAnd (ITFixed IT16)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LAnd t) args = S (A ("&" ++ intSuffix t) : map cgVar args) 

cgOp p@(LOr (ITFixed IT8)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LOr (ITFixed IT16)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LOr t) args = S (A ("|" ++ intSuffix t) : map cgVar args) 

cgOp p@(LXOr (ITFixed IT8)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LXOr (ITFixed IT16)) args = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LXOr t) args = S (A ("^" ++ intSuffix t) : map cgVar args) 

cgOp (LIntStr ITNative) args = pervasive "string_of_int" args
cgOp (LIntStr ITBig) args = stdlib ["Z", "to_string"] args
cgOp (LChInt _) [x] = cgVar x
cgOp (LIntCh _) [x] = cgVar x

cgOp p@(LSExt from (ITFixed IT8)) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSExt from (ITFixed IT16)) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSExt (ITFixed IT8) to) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LSExt (ITFixed IT16) to) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LSExt from to) [x]  = S [A ("convert" ++ (intSuffix from) ++ (intSuffix to)) , cgVar x]

cgOp p@(LTrunc from (ITFixed IT8)) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LTrunc from (ITFixed IT16)) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LTrunc (ITFixed IT8) to) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp p@(LTrunc (ITFixed IT16) to) [x] = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]
cgOp (LTrunc from to) [x] = S [A ("convert" ++ (intSuffix from) ++ (intSuffix to)) , cgVar x]

cgOp (LStrInt ITNative) [x] = pervasive "int_of_string" [x]
cgOp LStrEq args = stdlib ["String", "equal"] args
cgOp LStrLen [x] = S [A "length.byte", cgVar x]
cgOp LStrHead [x] = S [A "load.byte", cgVar x, KInt 0]
cgOp LStrIndex args = S (A "store.byte" : map cgVar args)
cgOp LStrTail [x] = S [A "apply", S [A "global", A "$String", A "$sub"], cgVar x, KInt 1,
                       S [A "-", cgOp LStrLen [x], KInt 1]]
cgOp LStrRev [s] = S [A "apply", A "$%strrev", cgVar s]
cgOp p _ = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented: " ++ show p]





cgConst (I n) = KInt n
cgConst (BI n) = A $ (show n) ++ ".ibig"
cgConst (Fl x) = error "no floats"
cgConst (Ch i) = KInt (ord i)
cgConst (Str s) = KStr s
--cgConst (B32 n) = A $ (show n) ++ ".i32"
--cgConst (B64 n) =  A $ (show n) ++ ".i64"
cgConst k = S [A "apply", S [A "global", A "$Pervasives", A "$failwith"], KStr $ "unimplemented constant: " ++ show k]


