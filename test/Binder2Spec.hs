{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Binder2Spec where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.State.Strict (evalStateT, get, modify, StateT)
import qualified Data.Map.Lazy as M
import Data.Text (Text)
import GHC.Generics hiding (S)
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

-- This example is stolen from the paper
-- Abstract Representation of Binders in OCaml using the Bindlib Library.
-- https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?LFMTP2018.4

data Ty
  = Ty'Var (Var S Ty)
  | Ty'Arr Ty Ty
  | Ty'All (Binder Ty S Ty)

data Te
  = Te'Var (Var S Te)
  | Te'Abs Ty (Binder Te S Te)
  | Te'App Te Te
  | Te'Lam (Binder Ty S Te)
  | Te'Spe Te Ty

instance MkFree S Ty where
  mkFree = return . Ty'Var
instance MkFree S Te where
  mkFree = return . Te'Var

ty'Var :: Var S Ty -> Box S Ty
ty'Var = boxVar
ty'Arr :: Box S Ty -> Box S Ty -> Box S Ty
ty'Arr a b = Ty'Arr <$> a <*> b
ty'AllRaw :: Box S (Binder Ty S Ty) -> Box S Ty
ty'AllRaw = fmap Ty'All
ty'All :: Var S Ty -> Box S Ty -> Box S Ty
ty'All x t = ty'AllRaw $ bind x t

te'Var :: Var S Te -> Box S Te
te'Var = boxVar
te'AbsRaw :: Box S Ty -> Box S (Binder Te S Te) -> Box S Te
te'AbsRaw a f = Te'Abs <$> a <*> f
te'Abs :: Box S Ty -> Var S Te -> Box S Te -> Box S Te
te'Abs a x t = te'AbsRaw a $ bind x t
te'App :: Box S Te -> Box S Te -> Box S Te
te'App t u = Te'App <$> t <*> u
te'LamRaw :: Box S (Binder Ty S Te) -> Box S Te
te'LamRaw = fmap Te'Lam
te'Lam :: Var S Ty -> Box S Te -> Box S Te
te'Lam x t = te'LamRaw $ bind x t
te'Spe :: Box S Te -> Box S Ty -> Box S Te
te'Spe t a = Te'Spe <$> t <*> a

boxTy :: Ty -> S (Box S Ty)
boxTy (Ty'Var x) = return $ ty'Var x
boxTy (Ty'Arr a b) = ty'Arr <$> boxTy a <*> boxTy b
boxTy (Ty'All f) = ty'AllRaw <$> boxBinder boxTy f
boxTe :: Te -> S (Box S Te)
boxTe (Te'Var x) = return $ te'Var x
boxTe (Te'Abs a f) = te'AbsRaw <$> boxTy a <*> boxBinder boxTe f
boxTe (Te'App t u) = te'App <$> boxTe t <*> boxTe u
boxTe (Te'Lam f) = te'LamRaw <$> boxBinder boxTe f
boxTe (Te'Spe t a) = te'Spe <$> boxTe t <*> boxTy a

hnf :: Te -> S Te
hnf (Te'App t u) = do
  hu <- hnf u
  ht <- hnf t
  case ht of
    Te'Abs _ b -> hnf =<< subst b hu
    _ -> return $ Te'App ht hu
hnf (Te'Spe t a) = do
  ht <- hnf t
  case ht of
    Te'Lam b -> hnf =<< subst b a
    _ -> return $ Te'Spe ht a
hnf t = return t

nf :: Te -> S Te
nf (Te'Abs a f) = do
  (x, t) <- unbind f
  nt <- nf t
  bt <- boxTe nt
  fmap (Te'Abs a) $ unbox $ bind x bt
nf (Te'App t u) = do
  nt <- nf t
  nu <- nf u
  case nt of
    Te'Abs _ f -> nf =<< subst f u
    _ -> return $ Te'App nt nu
nf (Te'Lam f) = do
  (x, t) <- unbind f
  nt <- nf t
  bt <- boxTe nt
  fmap Te'Lam $ unbox $ bind x bt
nf (Te'Spe t a) = do
  nt <- nf t
  case nt of
    Te'Lam f -> nf =<< subst f a
    _ -> return $ Te'Spe nt a
nf t = return t

eqTy :: Ty -> Ty -> S Bool
eqTy (Ty'Var x1) (Ty'Var x2) = return $ x1 == x2
eqTy (Ty'Arr a1 b1) (Ty'Arr a2 b2) = do
  ca <- eqTy a1 a2
  cb <- eqTy b1 b2
  return $ ca && cb
eqTy (Ty'All f1) (Ty'All f2) = eqBinder eqTy f1 f2
eqTy _ _ = return False

type Ctxt = M.Map (Var S Te) Ty

infer :: Ctxt -> Te -> S (Maybe Ty)
infer ctxt (Te'Var x) = return $ M.lookup x ctxt
infer ctxt (Te'Abs a f) = do
  (x, t) <- unbind f
  mtyt <- infer (M.insert x a ctxt) t
  return $ Ty'Arr a <$> mtyt
infer ctxt (Te'App t u) = do
  mtyt <- infer ctxt t
  case mtyt of
    Just (Ty'Arr a b) -> do
      mtyu <- infer ctxt u
      case mtyu of
        Just tyu -> do
          e <- eqTy tyu a
          return $ if e then Just b else Nothing
        Nothing -> return Nothing
    _ -> return Nothing
infer ctxt (Te'Lam f) = do
  (x, t) <- unbind f
  mtyt <- infer ctxt t
  case mtyt of
    Just tyt -> do
      bt <- boxTy tyt
      fmap (Just . Ty'All) $ unbox $ bind x bt
    Nothing -> return Nothing
infer ctxt (Te'Spe t a) = do
  mtyt <- infer ctxt t
  case mtyt of
    Just (Ty'All f) -> Just <$> subst f a
    _ -> return Nothing

check :: Ctxt -> Te -> Ty -> S Bool
check ctxt t a = do
  mtyt <- infer ctxt t
  case mtyt of
    Just tyt -> eqTy tyt a
    Nothing -> return False

showTy :: Ty -> S Text
showTy (Ty'Var x) = return $ nameOf x
showTy (Ty'Arr a b) = do
  sha <- showTy a
  shb <- showTy b
  return $ "(" <> sha <> ") => (" <> shb <> ")"
showTy (Ty'All f) = do
  (x, t) <- unbind f
  sh <- showTy t
  return $ "\\" <> nameOf x <> "." <> sh

showTe :: Te -> S Text
showTe (Te'Var x) = return $ nameOf x
showTe (Te'Abs a f) = do
  sha <- showTy a
  (x, t) <- unbind f
  sht <- showTe t
  return $ "\\l " <> nameOf x <> ":" <> sha <> "." <> sht
showTe (Te'App t u) = do
  sht <- showTe t
  shu <- showTe u
  return $ "(" <> sht <> ") (" <> shu <> ")"
showTe (Te'Lam f) = do
  (x, t) <- unbind f
  sh <- showTe t
  return $ "\\L " <> nameOf x <> "." <> sh
showTe (Te'Spe t a) = do
  sht <- showTe t
  sha <- showTy a
  return $ "(" <> sht <> ") (" <> sha <> ")"

type1, type2 :: S Ty
term1 :: S Te
type1 = do
  x <- newVar "X"
  y <- newVar "Y"
  unbox $ ty'Arr (ty'Var x) (ty'Var y)
type2 = do
  x <- newVar "X"
  y <- newVar "Y"
  let arr = ty'Arr (ty'Var x) (ty'Var y)
  unbox $ ty'All x $ ty'All y $ ty'Arr arr arr
term1 = do
  x <- newVar "X"
  y <- newVar "Y"
  f <- newVar "f"
  a <- newVar "a"
  let arr = ty'Arr (ty'Var x) (ty'Var y)
  unbox $ te'Lam x $ te'Lam y $ te'Abs arr f $ te'Abs (ty'Var x) a $
    te'App (te'Var f) (te'Var a)

spec :: Spec
spec = do
  describe "type1" $ do
    it "should be shown the intended text" $ do
      let r = "(X) => (Y)"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- type1
        showTy t
  describe "type2" $ do
    it "should be shown the intended text" $ do
      let r = "\\X.\\Y.((X) => (Y)) => ((X) => (Y))"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- type2
        showTy t
  describe "term1" $ do
    it "should be shown the intended text" $ do
      let r = "\\L X.\\L Y.\\l f:(X) => (Y).\\l a:X.(f) (a)"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- term1
        showTe t
