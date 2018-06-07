module IRTS.CodegenMalfunction(codegenMalfunction, evalMalfunction) where

import Idris.Core.TT
import IRTS.CodegenCommon
import IRTS.Lang

import Data.List
import Data.Char
import Data.Ord
import qualified Data.Map.Strict as Map
import qualified Data.Set as S
import qualified Data.Graph as Graph
import Data.Maybe(mapMaybe)
import Data.Function (on)
import Control.Exception
import Control.Monad(mapM)

import System.Process
import System.Directory



data Sexp = S [Sexp] | A String | KInt Int
            | KBigInt Integer | KStr String
             deriving (Eq)

instance Show Sexp where
  show sexp = render sexp "" where
    render :: Sexp -> String -> String
    render (S s      ) k = "(" ++ foldr render (") " ++ k) s
    render (A s      ) k = s ++ " " ++ k
    render (KInt n   ) k = show n ++ " " ++ k
    render (KStr s   ) k = show s ++ " " ++ k
    render (KBigInt s) k = show s ++ ".ibig " ++ k




newtype Translate a =
   MkTrn ( Map.Map Name (Int, Int) -> Either String a)


instance Functor Translate where
  fmap f (MkTrn t) = MkTrn $
                       \m -> case t m of
                         Right a -> Right (f a)
                         Left err -> Left err

instance Applicative Translate where
  pure a =  MkTrn $ \m -> Right a
  MkTrn f <*> MkTrn t = MkTrn $
                      \m -> case f m of
                         Right f -> case t m of
                           Right a -> Right (f a)
                           Left err -> Left err
                         Left err -> Left err

instance Monad Translate where
  MkTrn t >>= f = MkTrn $
                      \m -> case t m of
                         Right a -> let MkTrn h = f a in h m
                         Left err -> Left err



runTranslate :: Translate a -> Map.Map Name (Int, Int) -> Either String a
runTranslate (MkTrn t) = t



ask :: Translate (Map.Map Name (Int, Int))
ask = MkTrn $ \m -> Right m



crashWith :: String -> Translate a
crashWith err = MkTrn $ \m -> Left err



okChar :: Char -> Bool
okChar c =
  (isAscii c && isAlpha c) || isDigit c || c `elem` ".&|$+-!@#^*~?<>=_"



cgSym :: String -> Sexp
cgSym s = A ('$' : chars s)
 where
  chars :: String -> String
  chars [] = []
  chars (c : cs) | okChar c  = c : chars cs
                 | otherwise = "%" ++ show (ord c) ++ "%" ++ chars cs



codegenMalfunction :: CodeGenerator
codegenMalfunction ci = do
  let langDeclarations = liftDecls ci
  writeFile langFile $ stringify langDeclarations
  writeFile tmp $ show $ S
    (A "module" : shuffle
      langDeclarations
      [ S
        [A "_", S [A "apply", cgName (sMN 0 "runMain"), KStr "unused_runMain"]]
      , S [A "export"]
      ]
    )
  callCommand $ "malfunction fmt " ++ tmp ++ " > " ++ mlfFile
  catch
    (callCommand $ "malfunction compile -o " ++ outputFile ci ++ " " ++ mlfFile)
    handler
   -- use tmp, it's faster
  removeFile tmp
 where
  mlfFile  = outputFile ci ++ ".mlf"
  langFile = outputFile ci ++ ".lang"



evalMalfunction :: CodeGenerator
evalMalfunction ci = do
  let langDeclarations = liftDecls ci
  writeFile langFile $ stringify langDeclarations
  writeFile tmp $ show $ S
    (A "let" : shuffle
      langDeclarations
      [S [A "apply", cgName (sMN 0 "runMain"), KStr "unused_runMain"]]
    )
  callCommand $ "malfunction fmt " ++ tmp ++ " > " ++ mlfFile
  catch (callCommand $ "cat " ++ tmp ++ " | malfunction eval ") handler
  removeFile tmp
 where
  mlfFile  = outputFile ci ++ ".mlf"
  langFile = outputFile ci ++ ".lang"



tmp :: FilePath
tmp = "idris_malfunction_output.mlf"



handler :: SomeException -> IO ()
handler ex = putStrLn $ "Caught exception: " ++ show ex



stringify :: [(Name, LDecl)] -> String
stringify = unwords . map (\decl -> show decl ++ "\n\n")



shuffle :: [(Name, LDecl)] -> [Sexp] -> [Sexp]
shuffle decls rest = prelude
  ++ toBindings (Graph.stronglyConnComp (mapMaybe toNode decls))
 where
  nameTagMap :: Map.Map Name (Int, Int)
  nameTagMap = Map.fromList
    [ (name, (tag, arity)) | (_, LConstructor name tag arity) <- decls ]

  toBindings :: [Graph.SCC (Name, LDecl)] -> [Sexp]
  toBindings [] = rest
  toBindings (Graph.AcyclicSCC decl : comps) =
    case runTranslate (cgDecl decl) nameTagMap of
      Right (Just sexp) -> sexp : toBindings comps
      Right Nothing     -> toBindings comps
      Left  err         -> error err
  toBindings (Graph.CyclicSCC dcls : comps) = S (A "rec" : mapMaybe go dcls)
    : toBindings comps
   where
    go decl = case runTranslate (cgDecl decl) nameTagMap of
      Right maybeSexp -> maybeSexp
      Left  err       -> error err

  toNode :: (Name, LDecl) -> Maybe ((Name, LDecl), Name, [Name])
  toNode decl@(name, LFun _ _ _ body) = Just (decl, name, S.toList (free body))
  toNode _                            = Nothing

  freeCase :: LAlt -> S.Set Name
  freeCase (LConCase _ name names exp) =
    S.unions $ S.singleton name : free exp : map S.singleton names
  freeCase (LConstCase _ exp) = free exp
  freeCase (LDefaultCase exp) = free exp

  free :: LExp -> S.Set Name
  free (LV name           ) = S.singleton name
  free (LApp _ exp exps   ) = S.unions $ free exp : map free exps
  free (LLazyApp name exps) = S.unions $ S.singleton name : map free exps
  free (LLazyExp exp      ) = free exp
  free (LForce   exp      ) = free exp
  free (LLet name exp1 exp2) =
    S.unions [S.singleton name, free exp1, free exp2]
  free (LLam  names exp   ) = S.unions $ free exp : map S.singleton names
  free (LProj exp   _     ) = free exp
  free (LCon _ _ name exps) = S.unions $ S.singleton name : map free exps
  free (LCase _ exp alts  ) = S.unions $ free exp : map freeCase alts
  free (LConst _          ) = S.empty
  free (LForeign _ _ args ) = S.unions $ map (free . snd) args
  free (LOp _ exps        ) = S.unions $ map free exps
  free LNothing             = S.empty
  free (LError _)           = S.empty

  prelude :: [Sexp]
  prelude =
    [ S
        [ A "$%strrev"
        , S
          [ A "lambda"
          , S [A "$s"]
          , S
            [ A "let"
            , S [A "$n", S [A "-", S [A "length.byte", A "$s"], KInt 1]]
            , S
              [ A "apply"
              , S [A "global", A "$String", A "$mapi"]
              , S
                [ A "lambda"
                , S [A "$i", A "$c"]
                , S [A "load.byte", A "$s", S [A "-", A "$n", A "$i"]]
                ]
              , A "$s"
              ]
            ]
          ]
        ]
    ]



cgName :: Name -> Sexp
cgName = cgSym . showCG



cgDecl :: (Name, LDecl) -> Translate (Maybe Sexp)
cgDecl (name, LFun _ _ args body) = do
  b <- cgExp body
  return $ Just $ S [cgName name, S [A "lambda", mkargs args, b]]
 where
  mkargs :: [Name] -> Sexp
  mkargs []   = S [A "$%unused"]
  mkargs args = S $ map cgName args
cgDecl _ = pure Nothing



cgExp :: LExp -> Translate Sexp
cgExp e = do
  -- a <- cgExp' e
  -- pure $ S [A "seq",
  --   S [A "apply", print_endline,
  --   A $ show $ show e ++ "\n"], a]
  cgExp' e
 where
  print_endline :: Sexp
  print_endline = S [A "global", A "$Pervasives", A "$print_endline"]



cgExp' :: LExp -> Translate Sexp
cgExp' (LV name          ) = pure $ cgName name

cgExp' (LApp tail fn []  ) = cgExp fn

cgExp' (LApp tail fn args) = do
  f  <- cgExp fn
  as <- mapM cgExp args
  pure $ S $ [A "apply", f] ++ as

cgExp' (LLazyApp name []) =
  pure $ S [A "lambda", S [A "$lazy_unused"], cgName name]

cgExp' (LLazyApp name args) = do
  as <- mapM cgExp args
  pure
    $ S
        [ A "lambda"
        , S [A "$lazy_unused_mult"]
        , S $ [A "apply", cgName name] ++ as
        ]

cgExp' (LLazyExp e) = crashWith "LLazyExp???????"
  -- a <- cgExp e
  -- pure $ S [A "lambda", S [A "$delay"], a]
cgExp' (LForce   e) = do
  a <- cgExp e
  pure $ S [A "apply", a, KStr "force_unused"]
  -- cgExp e

cgExp' (LLet name exp body) = do
  e <- cgExp exp
  b <- cgExp body
  pure $ S [A "let", S [cgName name, e], b]

cgExp' (LLam args body) = do
  e <- cgExp body
  pure $ S [A "lambda", S $ map cgName args, e]

cgExp' (LProj e idx) = do
  a <- cgExp e
  pure $ S [A "field", KInt idx, a]

cgExp' (LCon maybeName tag name []) =
  if tag > 199 then crashWith "tag > 199" else pure $ KInt tag

cgExp' (LCon maybeName tag name args) = if tag > 199
  then crashWith "tag > 199"
  else do
    as <- mapM cgExp args
    pure $ S $ [A "block", S [A "tag", KInt tag]] ++ as

cgExp' (LCase _ e cases     ) = cgSwitch e cases
cgExp' (LConst k            ) = cgConst k
cgExp' (LForeign fn ret args) = error "no FFI" -- fixme
cgExp' (LOp prim args       ) = cgOp prim args
cgExp' LNothing               = pure $ KStr "erased"
cgExp' (LError s)             = pure $ S
  [ A "apply"
  , S [A "global", A "$Pervasives", A "$failwith"]
  , KStr $ "error: " ++ show s
  ]



concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f []       = pure []
concatMapM f (a : as) = do
  bs <- f a
  rs <- concatMapM f as
  pure $ bs ++ rs



cgSwitch :: LExp -> [LAlt] -> Translate Sexp
cgSwitch e cases = do
  a    <- cgExp e
  ts   <- taggroups
  tgs  <- mapM cgTagGroup ts
  ntgs <- concatMapM cgNonTagCase cases
  pure $ S [A "let", S [scr, a], S $ [A "switch", scr] ++ tgs ++ ntgs]
 where
  scr :: Sexp
  scr = A "$%matchOn"

  getTag n m = case Map.lookup n m of
    Just (tag, arity) -> tag
    Nothing           -> error "This should never happen"

  oneOfThree (a, _, _) = a
  twoOfThree (_, a, _) = a
  threeOfThree (_, _, a) = a

  tagcases :: Translate [(Int, LAlt, Bool)]
  tagcases = do
    m <- ask
    pure $ concatMap
      (\c -> case c of
        (LConCase _ n [] _) -> [(getTag n m, c, False)]
        (LConCase _ n _  _) -> [(getTag n m, c, True)]
        _                   -> []
      )
      cases -- better filter and then map?

  taggroups :: Translate [(Int, [LAlt], Bool)]
  taggroups =
    map
        (\cases ->
          ( oneOfThree $ head cases
          , map twoOfThree cases
          , threeOfThree $ head cases
          )
        )
      .   groupBy ((==) `on` oneOfThree)
      .   sortBy (comparing oneOfThree)
      <$> tagcases -- why sort?

  cgTagGroup :: (Int, [LAlt], Bool) -> Translate Sexp
  cgTagGroup (tagmod, cases, isBlock) = do
    tgs <- cgTagClass cases
    if isBlock
      then pure $ S $ S [A "tag", KInt tagmod] : tgs
      else pure $ S $ KInt tagmod : tgs

  cgTagClass :: [LAlt] -> Translate [Sexp]
  cgTagClass cases = do
    let fcs = [ c | c@(LConCase tag n _ _) <- cases ]
    mapM cgProjections fcs

  cgProjections :: LAlt -> Translate Sexp
  cgProjections (LConCase tag name args body) = do
    let fields =
          zipWith (\i n -> S [cgName n, S [A "field", KInt i, scr]]) [0 ..] args
    exp <- cgExp body
    if null fields then pure exp else pure $ S $ [A "let"] ++ fields ++ [exp]

  cgNonTagCase :: LAlt -> Translate [Sexp]
  cgNonTagCase LConCase{}           = mapM pure []
  cgNonTagCase (LConstCase (I n) e) = do
    a <- cgExp e
    pure [S [KInt n, a]]
  cgNonTagCase (LConstCase (BI n) e) = do
    a <- cgExp e
    pure [S [KInt (fromInteger n), a]] --FIXME if use KBigInt compiler cries
  cgNonTagCase (LConstCase (Ch c) e) = do
    a <- cgExp e
    pure [S [KInt (ord c), a]]
  cgNonTagCase (LConstCase k e) =
    crashWith $ "unsupported constant selector: " ++ show k
  cgNonTagCase (LDefaultCase e) = do
    a <- cgExp e
    pure [S [A "_", S [A "tag", A "_"], a]]



arithSuffix :: ArithTy -> String
arithSuffix (ATInt ITNative) = ""
arithSuffix (ATInt ITChar  ) = ""
arithSuffix (ATInt ITBig   ) = ".ibig"
arithSuffix s                = error $ "unsupported arithmetic type: " ++ show s



stdlib :: [String] -> [LExp] -> Translate Sexp
stdlib path args = do
  as <- mapM cgExp args
  pure $ S $ [A "apply", S (A "global" : map (A . ('$' :)) path)] ++ as



pervasive :: String -> [LExp] -> Translate Sexp
pervasive f = stdlib ["Pervasives", f]



cgOp :: PrimFn -> [LExp] -> Translate Sexp
cgOp LStrConcat [l, r] = do
  le <- cgExp l
  re <- cgExp r
  pure $ S [A "apply", S [A "global", A "$Pervasives", A "$^"], le, re]

cgOp LStrCons [c, r] = do
  cc <- cgExp c
  rr <- cgExp r
  pure $ S
    [ A "apply"
    , S [A "global", A "$Pervasives", A "$^"]
    , S [A "apply", S [A "global", A "$String", A "$make"], KInt 1, cc]
    , rr
    ] -- fixme safety

cgOp LWriteStr [_, str] = do
  s <- cgExp str
  pure $ S [A "apply", S [A "global", A "$Pervasives", A "$print_endline"], s]

cgOp LReadStr [_] = pure
  $ S [A "apply", S [A "global", A "$Pervasives", A "$read_line"], KInt 0]

cgOp (LPlus t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("+" ++ arithSuffix t) : as

cgOp (LMinus t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("-" ++ arithSuffix t) : as

cgOp (LTimes t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("*" ++ arithSuffix t) : as

cgOp (LSRem t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("%" ++ arithSuffix t) : as

cgOp (LEq t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("==" ++ arithSuffix t) : as

cgOp (LSLt t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("<" ++ arithSuffix t) : as

cgOp (LSGt t) args = do
  as <- mapM cgExp args
  pure $ S $ A (">" ++ arithSuffix t) : as

cgOp (LSLe t) args = do
  as <- mapM cgExp args
  pure $ S $ A ("<=" ++ arithSuffix t) : as

cgOp (LSGe t) args = do
  as <- mapM cgExp args
  pure $ S $ A (">=" ++ arithSuffix t) : as

cgOp (LIntStr ITNative) args = pervasive "string_of_int" args
cgOp (LIntStr ITBig   ) args = stdlib ["Z", "to_string"] args
cgOp (LChInt  _       ) [x]  = cgExp x
cgOp (LIntCh  _       ) [x]  = cgExp x
cgOp (LSExt  _ _      ) [x]  = cgExp x -- FIXME
cgOp (LTrunc _ _      ) [x]  = cgExp x -- FIXME
cgOp (LStrInt ITNative) [x]  = pervasive "int_of_string" [x]
cgOp LStrEq             args = stdlib ["String", "equal"] args

cgOp LStrLen            [x]  = do
  e <- cgExp x
  pure $ S [A "length.byte", e]

cgOp LStrHead [x] = do
  e <- cgExp x
  pure $ S [A "load.byte", e, KInt 0]

cgOp LStrIndex args = do
  as <- mapM cgExp args
  pure $ S $ A "store.byte" : as

cgOp LStrTail [x] = do
  e <- cgExp x
  o <- cgOp LStrLen [x]
  pure $ S
    [ A "apply"
    , S [A "global", A "$String", A "$sub"]
    , e
    , KInt 1
    , S [A "-", o, KInt 1]
    ]

cgOp LStrRev [s] = do
  e <- cgExp s
  pure $ S [A "apply", A "$%strrev", e]

cgOp p _ = pure $ S
  [ A "apply"
  , S [A "global", A "$Pervasives", A "$failwith"]
  , KStr $ "unimplemented: " ++ show p
  ]



cgConst :: Const -> Translate Sexp
cgConst (I   n) = pure $ KInt n
cgConst (BI  n) = pure $ KBigInt n
cgConst (Fl  x) = crashWith "no floats"
cgConst (Ch  i) = pure $ KInt (ord i)
cgConst (Str s) = pure $ KStr s
cgConst k       = crashWith $ "unimplemented constant " ++ show k
