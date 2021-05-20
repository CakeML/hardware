{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE TupleSections, LambdaCase, OverloadedStrings #-}

import Control.Monad.Reader

import Data.Maybe (isJust, isNothing, fromJust)
import Data.List (partition)
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M
import qualified Data.Text.IO as T

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO
import System.FilePath (takeBaseName)

import Prettyprinter
import Prettyprinter.Render.Text

import Verilog.Par (pProgram, myLexer)
import qualified Verilog.Abs as A

parse :: String -> IO A.Program
parse s = do
  case pProgram (myLexer s) of
    Left err -> do
      putStr "Syntax error: "
      putStrLn err
      exitFailure
    Right tree -> return tree

data Type = TLogic | TArray Integer

instance Show Type where
  show TLogic = "VBool_t"
  show (TArray len) = "VArray_t " ++ show len

--- Actually, since we will do actual type-checking later, do not need to keep track of array lengths for most of elaboration
data AbsType = ATLogic | ATArray deriving (Eq, Show)

absType :: Type -> AbsType
absType TLogic = ATLogic
absType TArray{} = ATArray

data VarData = ExtVar AbsType | IntVar AbsType
type Elaborate = ReaderT (M.Map String VarData) IO

buildType :: A.Type -> IO Type
buildType (A.TLogic A.TArrayEmpty) = return TLogic
buildType (A.TLogic (A.TArrayArray h l)) = if l == 0 then return $ TArray (h+1) else fail "lower bound must be 0!"

isInputDecl :: A.ExtDecl -> Bool
isInputDecl = \case (A.EDeclConst dir _ _ _) -> isInputDir dir
                    (A.EDeclX dir _ _) -> isInputDir dir
  where isInputDir A.InExt = True
        isInputDir A.OutExt = False

isFfBlock :: A.Always -> Bool
isFfBlock A.AlwaysFF{} = True
isFfBlock _ = False

data DeclType = Output | Internal
data Decl = Decl DeclType Type String (Maybe A.Const)
data InputDecl = InputDecl Type String -- special data type for input since inputs never have init

-- We should do elaboration inside the logic instead,
-- but we do it here right now for convenience...
elaborate :: String -> A.Module -> IO (Doc a)
elaborate name (A.Module (A.Id id) edecls idecls blocks) = do
 unless (id == name) $ fail $ "module id must, for now, be the same as filename (" ++ name ++ ")"
 let (inputs, outputs) = partition isInputDecl edecls
 -- TODO: Check for duplicates in both maps? (But this is anyway done in type checker later!)
 inputs' <- mapM elaborateInput inputs >>= removeClkInput
 decls <- (++) <$> (mapM elaborateOutput outputs) <*> (mapM elaborateDecl idecls)
 let input_pairs = M.fromList $ map (\(InputDecl t var) -> (var, absType t)) inputs'
 let decl_pairs = M.fromList $ map (\(Decl _ t var _) -> (var, absType t)) decls
 unless (M.disjoint input_pairs decl_pairs) $ fail "external and internal declarations not disjoint"
 blocks' <- runReaderT (mapM elaborateBlock blocks) $ M.merge (M.mapMissing $ \_ v -> ExtVar v)
                                                              (M.mapMissing $ \_ v -> IntVar v)
                                                              (M.zipWithMaybeMatched (\_ _ _ -> error "impossible"))
                                                              input_pairs decl_pairs

 let inputsP = holList $ map (\(InputDecl t id) -> pretty (show id, show t)) inputs'
 let declsP = holList $ map prettyDecl decls
 let (ffBlocks, combBlocks) = partition isFfBlock blocks'
 let ffBlocksP = holList $ map prettyAlways ffBlocks
 let combBlocksP = holList $ map prettyAlways combBlocks
 return $ holRecord [("fextty", inputsP), ("decls", declsP), ("ffs", ffBlocksP), ("combs", combBlocksP)]

prettyDecl :: Decl -> Doc a
prettyDecl (Decl dtype t id c) = tupled [pretty $ show id,
                                         holRecord [("output", case dtype of Output -> "T"; Internal -> "F"),
                                                    ("type", pretty $ show t),
                                                    ("init", holMaybe $ fmap prettyConst c)]]

elaborateInput :: A.ExtDecl -> IO InputDecl
elaborateInput (A.EDeclConst{}) = fail "Inputs cannot have inits"
elaborateInput (A.EDeclX _ t (A.Id id)) = do
  t' <- buildType t
  return $ InputDecl t' id

elaborateOutput :: A.ExtDecl -> IO Decl
elaborateOutput (A.EDeclConst _ t (A.Id id) c) = do
  t' <- buildType t
  return $ Decl Output t' id (Just c)
elaborateOutput (A.EDeclX _ t (A.Id id)) = do
  t' <- buildType t
  return $ Decl Output t' id Nothing

elaborateDecl :: A.IntDecl -> IO Decl
elaborateDecl (A.IDeclConst t (A.Id id) c) = do
  t' <- buildType t
  return $ Decl Internal t' id (Just c)
elaborateDecl (A.IDeclX t (A.Id id)) = do
  t' <- buildType t
  return $ Decl Internal t' id Nothing

holList :: [Doc a] -> Doc a
holList = encloseSep lbracket rbracket "; "

holRecord :: [(String, Doc a)] -> Doc a
holRecord = encloseSep "<|" "|>" "; " . map (\(f, v) -> sep [pretty f, ":=", v])

holMaybe :: Maybe (Doc a) -> Doc a
holMaybe Nothing = "NONE"
holMaybe (Just x) = "SOME" <+> (parens x)

--prettyType :: A.Type -> String
--prettyType (A.TLogic A.TArrayEmpty) = "VBool_t"
--prettyType (A.TLogic (A.TArrayArray h _)) = "VArray_t " ++ show (h+1)

prettyAlways :: A.Always -> Doc a
prettyAlways (A.AlwaysFF _ s) = prettyStm s
prettyAlways (A.AlwaysComb s) = prettyStm s
prettyAlways a = error $ "Internal error! The always block should have been processed away by now: " ++ show a

prettyStm :: A.Stm -> Doc a
prettyStm = \case
  A.SIf e s         -> "IfElse" <+> (parens $ prettyExp e) <> line <> (nest 2 $ sep [parens $ prettyStm s, "Skip"])
  A.SIfElse e s1 s2 -> "IfElse" <+> (parens $ prettyExp e) <> line <> (nest 2 $ sep [parens $ prettyStm s1, parens $ prettyStm s2])
  A.SCase e ss ds   -> "Case" <+> "VBool_t" <+> nest 2 (vsep [parens $ prettyExp e, holList $ map prettyCase ss, parens $ prettyStmOpt ds])
  A.SBlock [s]      -> prettyStm s
  A.SBlock ss       -> "verFromList" <+> (holList $ map prettyStm ss)
  A.SBAss e re      -> sep ["BlockingAssign", parens $ prettyAssnLhs e, parens $ prettyRExp re]
  A.SNBAss e re     -> sep ["NonBlockingAssign", parens $ prettyAssnLhs e, parens $ prettyRExp re]

prettyCase :: A.CaseItem -> Doc a
prettyCase (A.CItem e s) = tupled [prettyExp e, prettyStm s]

prettyStmOpt :: A.CaseDefault -> Doc a
prettyStmOpt (A.CDefault s) = "SOME" <+> (parens $ prettyStm s)
prettyStmOpt A.CDefaultEmpty = "NONE"

prettyAssnLhs :: A.Exp -> Doc a
prettyAssnLhs e = case e of
  A.EVar (A.IntVar (A.Id id))       -> "NoIndexing" <+> pretty (show id)
  A.EIndex (A.IntVar (A.Id id)) e   -> "Indexing" <+> pretty (show id) <+> pretty (0 :: Integer) <+> (parens $ prettyExp e)
  A.ESlice (A.IntVar (A.Id id)) h l -> "SliceIndexing" <+> pretty (show id) <+> pretty h <+> pretty l
  _ -> error ("Bad left-hand side: " ++ show e)

prettyRExp :: A.ARHS -> Doc a
prettyRExp (A.RExp e) = "SOME" <+> (parens $ prettyExp e)
prettyRExp A.RX = "NONE"

prettyVar :: A.Var -> Doc a
prettyVar (A.IntVar (A.Id id)) = "Var" <+> pretty (show id)
prettyVar (A.ExtVar (A.Id id)) = "InputVar" <+> pretty (show id)

prettyExp :: A.Exp -> Doc a
prettyExp = \case
  A.EConst c        -> "Const" <+> (parens $ prettyConst c)
  A.EVar var        -> prettyVar var
  A.EIndex var e    -> "ArrayIndex" <+> (parens $ prettyVar var) <+> (pretty (0 :: Integer)) <+> (parens $ prettyExp e)
  A.ESlice var h l  -> "ArraySlice" <+> (parens $ prettyVar var) <+> (pretty h) <+> (pretty l)
  A.ENot e          -> "BUOp" <+> "Not" <+> (parens $ prettyExp e)
  A.EAdd e1 e2      -> sep ["Arith", parens $ prettyExp e1, "Plus", parens $ prettyExp e2]
  A.EEq{}           -> error "impossible, EEq should not be in tree after elaboration!"
  A.EEq_bool e1 e2  -> sep ["BBOp", parens $ prettyExp e1, "Equal", parens $ prettyExp e2]
  A.EEq_array e1 e2 -> sep ["Cmp", parens $ prettyExp e1, "ArrayEqual", parens $ prettyExp e2]
  A.EAnd e1 e2      -> sep ["BBOp", parens $ prettyExp e1, "And", parens $ prettyExp e2]

prettyConst :: A.Const -> Doc a
prettyConst (A.CInt i) = "n2VArray" <+> pretty (32 :: Integer) <+> pretty i
prettyConst (A.CDecimal width i) = "n2VArray" <+> pretty width <+> pretty i
prettyConst (A.CBinary 1 i) = case i of
                                0 -> "VBool F"
                                1 -> "VBool T"
                                _ -> error "unexpected binary value!"
prettyConst (A.CBinary width i) = pretty $ "w2ver (0b" ++ show i ++ "w : " ++ show width ++ " word)"

removeClkInput :: [InputDecl] -> IO [InputDecl]
removeClkInput decls = do
 let (clks, not_clks) = partition (\(InputDecl _ id) -> id == "clk") decls
 case clks of
  []              -> fail "No clk input"
  [InputDecl t _] -> if is_logic t then return not_clks else fail "clk input must have type logic"
  _               -> fail "More than one clk input"

  where is_logic TLogic = True
        is_logic TArray{} = False

elaborateBlock :: A.Always -> Elaborate A.Always
elaborateBlock (A.AlwaysFF (A.Id clk) s) =
 if clk == "clk" then do
   s' <- elaborateStm s
   return (A.AlwaysFF (A.Id clk) s')
 else
   fail "Clock for block not clk!"
elaborateBlock (A.AlwaysComb s) = A.AlwaysComb <$> elaborateStm s
-- Hacks:
elaborateBlock (A.AlwaysContinuous lhs rhs) = do
  lhs' <- elaborateExp lhs
  rhs' <- elaborateRExp rhs
  return $ A.AlwaysComb (A.SBAss lhs' rhs')
elaborateBlock (A.AlwaysModule m _ args) = do
  A.AlwaysComb <$> (elaborateStm $ translateModule m args)

translateModule :: A.Id -> [A.Exp] -> A.Stm
translateModule (A.Id id) args = case (id, args) of
 ("not", [out, in1]) -> A.SBAss out (A.RExp $ A.ENot in1)
 ("and", [out, in1, in2]) -> A.SBAss out (A.RExp $ A.EAnd in1 in2)
 _ -> error $ "Unsupported module: " ++ id ++ " with arguments " ++ show args

elaborateStm :: A.Stm -> Elaborate A.Stm
elaborateStm = \case
  A.SIf e s         -> A.SIf <$> elaborateExp e <*> elaborateStm s
  A.SIfElse e s1 s2 -> A.SIfElse <$> elaborateExp e <*> elaborateStm s1 <*> elaborateStm s2
  A.SCase e ss ds   -> A.SCase <$> elaborateExp e <*> mapM elaborateCaseItem ss <*> elaborateCaseDefault ds
  A.SBlock ss       -> A.SBlock <$> mapM elaborateStm ss
  A.SBAss e re      -> A.SBAss <$> elaborateExp e <*> elaborateRExp re
  A.SNBAss e re     -> A.SNBAss <$> elaborateExp e <*> elaborateRExp re

elaborateCaseItem :: A.CaseItem -> Elaborate A.CaseItem
elaborateCaseItem (A.CItem e s) = A.CItem <$> elaborateExp e <*> elaborateStm s

elaborateCaseDefault :: A.CaseDefault -> Elaborate A.CaseDefault
elaborateCaseDefault (A.CDefault s) = A.CDefault <$> elaborateStm s
elaborateCaseDefault A.CDefaultEmpty = return A.CDefaultEmpty

elaborateRExp :: A.ARHS -> Elaborate A.ARHS
elaborateRExp (A.RExp e) = A.RExp <$> elaborateExp e
elaborateRExp A.RX = return A.RX

elaborateExp :: A.Exp -> Elaborate A.Exp
elaborateExp e = fst <$> inferExp e
--elaborateExp e = return e

inferExp :: A.Exp -> Elaborate (A.Exp, AbsType)
inferExp e = case e of
  A.EConst (A.CInt i) -> if i >= 0 then return (e, ATArray) else fail "Negative number!"
  A.EConst (A.CDecimal width i) -> if width >= 0 && i >= 0 then
                                     return (e, ATArray)
                                   else
                                     fail "Negative number!"
  A.EConst (A.CBinary width i) -> if width == 1 && i >= 0 && i <= 1 then
                                    return (e, ATLogic)
                                  else
                                    -- TODO: Add more error handling...
                                    return (e, ATArray)
  A.EVar var -> do
    (var', t) <- elaborateVar var
    return (A.EVar var', t)
  A.EIndex var e -> do
    (var', _) <- elaborateVar var
    e' <- elaborateExp e
    return (A.EIndex var' e', ATLogic)
  A.ESlice var i1 i2 -> do
    (var', _) <- elaborateVar var
    return (A.ESlice var' i1 i2, ATArray)
  A.ENot e -> (\e -> (A.ENot e, ATLogic)) <$> elaborateExp e
  A.EAdd e1 e2 -> (\e1 e2 -> (A.EAdd e1 e2, ATArray)) <$> elaborateExp e1 <*> elaborateExp e2
  A.EEq e1 e2 -> do
    (e1', t1) <- inferExp e1
    (e2', t2) <- inferExp e2
    unless (t1 == t2) $ fail $ "Different types for eq: " ++ show (t1, t2)
    return $ case t1 of
      ATLogic -> (A.EEq_bool e1' e2', ATLogic)
      ATArray -> (A.EEq_array e1' e2', ATLogic)
  A.EEq_bool{} -> fail "Impossible: Found EEq_bool"
  A.EEq_array{} -> fail "Impossible: Found EEq_array"
  A.EAnd e1 e2 -> do
    (e1', t1) <- inferExp e1
    (e2', t2) <- inferExp e2
    unless (t1 == ATLogic && t2 == ATLogic) $ fail $ "Only support Boolean and for now: " ++ show (t1, t2)
    return (A.EAnd e1' e2', ATLogic)

elaborateVar :: A.Var -> Elaborate (A.Var, AbsType)
elaborateVar (A.IntVar (A.Id id)) = do
  env <- ask
  case (M.lookup id env) of
    Nothing         -> fail $ "Unknown variable " ++ id
    Just (ExtVar t) -> return (A.ExtVar (A.Id id), t)
    Just (IntVar t) -> return (A.IntVar (A.Id id), t)
elaborateVar (A.ExtVar{}) = fail "Impossible: Found external var in input tree"

renderDoc :: Doc a -> SimpleDocStream a
renderDoc = layoutSmart (LayoutOptions {layoutPageWidth = AvailablePerLine 100 1.0})

putModuleStart :: Handle -> String -> IO ()
putModuleStart h name = do
 --hPutStrLn h "open HolKernel Parse boolLib;"
 hPutStrLn h "open hardwarePreamble;"
 hPutStrLn h ""
 hPutStrLn h "open verilogTheory fullCompilerTheory (*verilogTypeTheory verilogTypeCheckerTheory*);"
 hPutStrLn h ""
 hPutStrLn h "open compileLib RTLPrintLib;"
 hPutStrLn h ""
 hPutStrLn h ("val _ = new_theory \"" ++ name ++ "\";")
 hPutStrLn h ""
 hPutStrLn h ("Definition " ++ name ++ "_def:")
 hPutStrLn h (name ++ " =")

putModuleEnd :: Handle -> Maybe String -> TestKind -> String -> IO ()
putModuleEnd h expected kind name = do
 hPutStrLn h "End"

 hPutStrLn h ""
 hPutStrLn h $ "(* val _ = EVAL “typecheck " ++ name ++ "” |> concl |> rhs |> sumSyntax.dest_inr; *)"
 hPutStrLn h ""

 case kind of
   GoodTest -> do
     unless (isNothing expected) (fail "Expected error specified in good test case")
     hPutStrLn h $ "val (circuit, circuit_correct) = compile " ++ name ++ "_def;"
     hPutStrLn h ""
     hPutStrLn h $ "Theorem " ++ name ++ "_circuit_correct = circuit_correct;"
     hPutStrLn h ""
     hPutStrLn h "(* print_Circuit (circuit |> concl |> rhs) |> print *)"
   BadTest -> do
     unless (isJust expected) (fail "Missing expected error in bad test case")
     hPutStrLn h $ "val err = EVAL “fullCompiler$compile " ++ name ++ "” |> concl |> rhs |> sumSyntax.dest_inl |> fst;"
     hPutStrLn h $ ""
     hPutStrLn h $ "val _ = assert (fn err => err = " ++ (show . fromJust $ expected) ++ ") (err |> strip_comb |> fst |> dest_const |> fst);"

 hPutStrLn h ""
 hPutStrLn h "val _ = export_theory ();"

data TestKind = GoodTest | BadTest

extractExpected :: A.ExpectedErrorDecl -> Maybe String
extractExpected (A.ExpectedErrorDeclSome (A.Id id)) = Just id
extractExpected A.ExpectedErrorDeclNone = Nothing

main :: IO ()
main = do
  args <- getArgs
  case args of
    [kind, file] -> withFile (name ++ "Script.sml") WriteMode
                    (\h -> do
                        putModuleStart h name
                        (A.Program expected m) <- readFile file >>= parse
                        elaborate name m >>= (T.hPutStrLn h . renderStrict . renderDoc . nest 1)
                        putModuleEnd h (extractExpected expected) testKind name)
               where name = takeBaseName file
                     -- TODO: Better error handling here...
                     testKind = if kind == "--bad" then BadTest else GoodTest
    _      -> putStrLn "Usage: buildTree <input-file.sv>" >> exitFailure
