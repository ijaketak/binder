{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Binder3Spec where

import Control.Lens
import Control.Monad ((<=<))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.State.Strict (evalStateT, get, modify, StateT)
import Data.List (intersperse)
-- import qualified Data.Map.Lazy as M
import Data.Text (Text)
import qualified Data.Text as T (pack)
import GHC.Generics hiding (S, to)
import Test.Hspec

import Data.Binder

newtype S a = S { runS :: StateT Int IO a }
  deriving
  ( Generic
  , Generic1
  , Functor
  , Applicative
  , Monad
  , MonadIO
  )

instance MonadNumbering S where
  type Numbering S = Int
  numbering = do
    i <- S $ get
    S $ modify succ
    return i

-- This example is stolen from one example of bindlib.
-- https://github.com/rlepigre/ocaml-bindlib/blob/master/examples/pred2.ml

data Symbol = Symbol Text Int
  deriving (Eq, Show)

data Term
  = Term'Var (Var S Term)
  | Term'Fun Symbol [Term]

data Form
  = Form'Imply Form Form
  | Form'Univ1 (Binder Term S Form)
  | Form'Univ2 Int (Binder Pred S Form)
  | Form'FVari (Var S Pred) [Term]

newtype Pred = Pred { unPred :: BinderList Term S Form }

data Proof
  = Proof'ImplyI Form (Binder Proof S Proof)
  | Proof'ImplyE Proof Proof
  | Proof'Univ1I (Binder Term S Proof)
  | Proof'Univ1E Proof Term
  | Proof'Univ2I Int (Binder Pred S Proof)
  | Proof'Univ2E Proof Pred
  | Proof'Axiom Form (Var S Proof)

pred'Arity :: Getter Pred Int
pred'Arity = to unPred . binderList'Arity
pred'makeRaw :: Box S (BinderList Term S Form) -> Box S Pred
pred'makeRaw = fmap Pred
pred'make :: VarList S Term -> Box S Form -> Box S Pred
pred'make xs t = pred'makeRaw $ bindList xs t

term'mkFree :: Var S Term -> S Term
term'mkFree = return . Term'Var
pred'mkFree :: Int -> Var S Pred -> S Pred
pred'mkFree n vp = do
  let names = if n == 1 then ["x"]
                        else flip map [1..n] $ \i -> "x" <> T.pack (show i)
  xs <- newVarList names term'mkFree
  let ts = boxList $ map term'Var xs
      p = Form'FVari vp <$> ts
  fmap Pred $ unbox $ bindList xs p
proof'mkFree :: Form -> Var S Proof -> S Proof
proof'mkFree f = return . Proof'Axiom f

term'Var :: Var S Term -> Box S Term
term'Var = boxVar
term'Fun :: Symbol -> [Box S Term] -> Box S Term
term'Fun s ts = Term'Fun s <$> boxList ts
form'Imply :: Box S Form -> Box S Form -> Box S Form
form'Imply f g = Form'Imply <$> f <*> g
form'Univ1Raw :: Box S (Binder Term S Form) -> Box S Form
form'Univ1Raw = fmap Form'Univ1
form'Univ1 :: Var S Term -> Box S Form -> Box S Form
form'Univ1 x t = form'Univ1Raw $ bind x t
form'Univ2Raw :: Int -> Box S (Binder Pred S Form) -> Box S Form
form'Univ2Raw arity = fmap $ Form'Univ2 arity
form'Univ2 :: Int -> Var S Pred -> Box S Form -> Box S Form
form'Univ2 arity x t = form'Univ2Raw arity $ bind x t
form'FVari :: Var S Pred -> [Box S Term] -> Box S Form
form'FVari x ts = Form'FVari x <$> boxList ts
proof'ImplyIRaw :: Box S Form -> Box S (Binder Proof S Proof) -> Box S Proof
proof'ImplyIRaw p b = Proof'ImplyI <$> p <*> b
proof'ImplyI :: Box S Form -> Var S Proof -> Box S Proof -> Box S Proof
proof'ImplyI p x t = proof'ImplyIRaw p $ bind x t
proof'ImplyE :: Box S Proof -> Box S Proof -> Box S Proof
proof'ImplyE p q = Proof'ImplyE <$> p <*> q
proof'Univ1IRaw :: Box S (Binder Term S Proof) -> Box S Proof
proof'Univ1IRaw = fmap Proof'Univ1I
proof'Univ1I :: Var S Term -> Box S Proof -> Box S Proof
proof'Univ1I x t = proof'Univ1IRaw $ bind x t
proof'Univ1E :: Box S Proof -> Box S Term -> Box S Proof
proof'Univ1E p q = Proof'Univ1E <$> p <*> q
proof'Univ2IRaw :: Int -> Box S (Binder Pred S Proof) -> Box S Proof
proof'Univ2IRaw arity = fmap $ Proof'Univ2I arity
proof'Univ2I :: Int -> Var S Pred -> Box S Proof -> Box S Proof
proof'Univ2I arity x t = proof'Univ2IRaw arity $ bind x t
proof'Univ2E :: Box S Proof -> Box S Pred -> Box S Proof
proof'Univ2E p q = Proof'Univ2E <$> p <*> q
proof'Axiom :: Box S Form -> Var S Proof -> Box S Proof
proof'Axiom f v = (\g -> Proof'Axiom g v) <$> f

boxTerm :: Term -> S (Box S Term)
boxTerm (Term'Var x) = return $ term'Var x
boxTerm (Term'Fun s ts) = fmap (term'Fun s) $ sequenceA $ boxTerm <$> ts
boxForm :: Form -> S (Box S Form)
boxForm (Form'Imply a b) = form'Imply <$> boxForm a <*> boxForm b
boxForm (Form'Univ1 b) = form'Univ1Raw <$> boxBinder boxForm b
boxForm (Form'Univ2 a b) = form'Univ2Raw a <$> boxBinder boxForm b
boxForm (Form'FVari x ts) = do
  let arg1 = unPred <$> boxVar x
  arg2 <- fmap boxList $ sequenceA $ boxTerm <$> ts
  boxJoin $ substList <$> arg1 <*> arg2

showTerm :: Term -> Text
showTerm (Term'Var x) = nameOf x
showTerm (Term'Fun (Symbol s _) ts) =
  s <> "(" <> mconcat (intersperse ", " $ map showTerm ts) <> ")"
showForm :: Form -> S Text
showForm (Form'Imply a b) = do
  sha <- showForm a
  shb <- showForm b
  return $ "(" <> sha <> ") => (" <> shb <> ")"
showForm (Form'Univ1 b) = do
  (x, t) <- unbind b
  sht <- showForm t
  return $ "forall_1 " <> nameOf x <> ".(" <> sht <> ")"
showForm (Form'Univ2 _ b) = do
  (x, t) <- unbind b
  sht <- showForm t
  return $ "forall_2 " <> nameOf x <> ".(" <> sht <> ")"
showForm (Form'FVari x ts) = do
  return $ nameOf x <> "(" <> mconcat (intersperse ", " $ map showTerm ts) <> ")"

eqTerm :: Term -> Term -> Bool
eqTerm (Term'Var x) (Term'Var y) = x == y
eqTerm (Term'Fun s1 ts1) (Term'Fun s2 ts2) =
  s1 == s2 && and (map (uncurry eqTerm) $ zip ts1 ts2)
eqTerm _ _ = False
eqForm :: Form -> Form -> S Bool
eqForm (Form'Imply a1 b1) (Form'Imply a2 b2) = do
  ca <- eqForm a1 a2
  cb <- eqForm b1 b2
  return $ ca && cb
eqForm (Form'Univ1 b1) (Form'Univ1 b2) = eqBinder eqForm b1 b2
eqForm (Form'Univ2 a1 b1) (Form'Univ2 a2 b2) = do
  c <- eqBinder eqForm b1 b2
  return $ a1 == a2 && c
eqForm (Form'FVari x1 ts1) (Form'FVari x2 ts2) =
  return $ x1 == x2 && and (map (uncurry eqTerm) $ zip ts1 ts2)
eqForm _ _ = return False

data BadProof
  = BadProof'Imply
  | BadProof'ImplyDifferForm Form Form
  | BadProof'Univ1
  | BadProof'Univ2

showBadProof :: BadProof -> S Text
showBadProof BadProof'Imply = return "BadProof'Imply"
showBadProof (BadProof'ImplyDifferForm a b) = do
  sha <- showForm a
  shb <- showForm b
  return $ "BadProof'ImplyDifferForm (" <> sha <> ") (" <> shb <> ")"
showBadProof BadProof'Univ1 = return "BadProof'Univ1"
showBadProof BadProof'Univ2 = return "BadProof'Univ2"

typeInfer :: Proof -> S (Either BadProof Form)
typeInfer = unbox <=< fn
 where
  fn :: Proof -> S (Box S (Either BadProof Form))
  fn (Proof'ImplyI f p) = do
    ax <- newVar (p ^. binder'Name) $ proof'mkFree f
    tax <- proof'mkFree f ax
    pr <- subst p tax
    ber <- fn pr
    er <- unbox ber
    case er of
      Right r -> do
        bf <- boxForm f
        br <- boxForm r
        return $ Right <$> form'Imply bf br
      Left err -> return $ pure $ Left err
  fn (Proof'ImplyE p1 p2) = do
    mf1' <- unbox =<< fn p2
    mf2' <- unbox =<< fn p1
    case (mf1', mf2') of
      (Right f1', Right (Form'Imply f1 f2)) -> do
        b <- eqForm f1 f1'
        if b then fmap Right <$> boxForm f2
             else return $ pure $ Left $ BadProof'ImplyDifferForm f1 f1'
      _ -> return $ pure $ Left BadProof'Imply
  fn (Proof'Univ1I p) = do
    t <- newVar (p ^. binder'Name) term'mkFree
    te <- term'mkFree t
    pr <- subst p te
    ef <- unbox =<< fn pr
    case ef of
      Right f -> do
        bf <- boxForm f
        return $ Right <$> form'Univ1 t bf
      Left err -> return $ pure $ Left err
  fn (Proof'Univ1E p t) = do
    mf <- unbox =<< fn p
    case mf of
      Right (Form'Univ1 b) -> do
        f <- subst b t
        fmap Right <$> boxForm f
      Right _ -> return $ pure $ Left BadProof'Univ1
      Left err -> return $ pure $ Left err
  fn (Proof'Univ2I arity f) = do
    t <- newVar (f ^. binder'Name) $ pred'mkFree arity
    pr <- pred'mkFree arity t
    eg <- unbox =<< fn =<< subst f pr
    case eg of
      Right g -> do
        bg <- boxForm g
        return $ fmap Right $ form'Univ2 arity t bg
      Left err -> return $ pure $ Left err
  fn (Proof'Univ2E p p0) = do
    mf <- unbox =<< fn p
    case mf of
      Right (Form'Univ2 arity b) -> if arity == p0 ^. pred'Arity
        then do
          f <- subst b p0
          fmap Right <$> boxForm f
        else return $ pure $ Left BadProof'Univ2
      Right _ -> return $ pure $ Left BadProof'Univ2
      Left err -> return $ pure $ Left err
  fn (Proof'Axiom f _) = fmap Right <$> boxForm f

typeCheck :: Proof -> Form -> S Bool
typeCheck p f0 = do
  ef <- typeInfer p
  case ef of
    Right f -> eqForm f0 f
    _ -> return False


leq :: S (Box S Pred)
leq = do
  u <- newVar "u" term'mkFree
  v <- newVar "v" term'mkFree
  let bu = term'Var u
      bv = term'Var v
  x <- newVar "X" $ pred'mkFree 1
  let bl = unPred <$> boxVar x
  p1 <- bindListApply bl $ boxList [bu]
  p2 <- bindListApply bl $ boxList [bv]
  return $ fmap Pred $ bindList [u, v] $ form'Univ2 1 x $ form'Imply p1 p2

equalTransitive :: S Form
equalTransitive = do
  q <- leq
  x <- newVar "x" term'mkFree
  y <- newVar "y" term'mkFree
  z <- newVar "z" term'mkFree
  let bx = term'Var x
      by = term'Var y
      bz = term'Var z
      bl = fmap unPred q
  p1 <- bindListApply bl $ boxList [bx, by]
  p2 <- bindListApply bl $ boxList [by, bz]
  p3 <- bindListApply bl $ boxList [bx, bz]
  unbox $ form'Univ1 x $ form'Univ1 y $ form'Univ1 z $
    form'Imply p1 $ form'Imply p2 p3

equalTransitiveProof :: S Proof
equalTransitiveProof = do
  q <- leq
  x <- newVar "x" term'mkFree
  y <- newVar "y" term'mkFree
  z <- newVar "z" term'mkFree
  let bx = term'Var x
      by = term'Var y
      bz = term'Var z
      bl = fmap unPred q
  f <- bindListApply bl $ boxList [bx, by]
  uf <- unbox f
  h1 <- newVar "h1" $ proof'mkFree uf
  g <- bindListApply bl $ boxList [by, bz]
  ug <- unbox g
  h2 <- newVar "h2" $ proof'mkFree ug
  px <- newVar "X" $ pred'mkFree 1
  p <- bindListApply (unPred <$> boxVar px) $ boxList [bx]
  up <- unbox p
  h3 <- newVar "h3" $ proof'mkFree up
  unbox $ proof'Univ1I x $ proof'Univ1I y $ proof'Univ1I z $
    proof'ImplyI f h1 $ proof'ImplyI g h2 $
    proof'Univ2I 1 px $ proof'ImplyI p h3 $
    proof'ImplyE (proof'Univ2E (boxVar h2) (boxVar px)) $
    proof'ImplyE (proof'Univ2E (boxVar h1) (boxVar px)) (boxVar h3)

spec :: Spec
spec = describe "leq" $ do
  it "forms correctly" $ do
    let r = "forall_1 x.(forall_1 y.(forall_1 z.((forall_2 X.((X(x)) => (X(y)))) => ((forall_2 X.((X(y)) => (X(z)))) => (forall_2 X.((X(x)) => (X(z))))))))"
    flip shouldReturn r $ flip evalStateT 0 $ runS $ do
      f <- equalTransitive
      showForm f
  it "infers type soundly" $ do
    let r = "forall_1 x.(forall_1 y.(forall_1 z.((forall_2 X.((X(x)) => (X(y)))) => ((forall_2 X.((X(y)) => (X(z)))) => (forall_2 X.((X(x)) => (X(z))))))))"
    flip shouldReturn r $ flip evalStateT 0 $ runS $ do
      ef <- typeInfer =<< equalTransitiveProof
      case ef of
        Right f -> showForm f
        Left bp -> showBadProof bp
  it "checks correctly" $ do
    let r = True
    flip shouldReturn r $ flip evalStateT 0 $ runS $ do
      p <- equalTransitiveProof
      f <- equalTransitive
      typeCheck p f
