{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Binder1Spec where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.State.Strict (evalStateT, get, modify, StateT)
import Data.Text (Text)
import GHC.Generics hiding (S)
import Prelude hiding (abs)
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

-- This example is stolen from the documentation of bindlib.
-- https://github.com/rlepigre/ocaml-bindlib/blob/master/lib/bindlib.mli

data Term
  = Term'Var (Var S Term)
  | Term'Abs (Binder Term S Term)
  | Term'App Term Term

instance MkFree S Term where
  mkFree = return . Term'Var

var :: Var S Term -> Box S Term
var = boxVar
absRaw :: Box S (Binder Term S Term) -> Box S Term
absRaw = fmap Term'Abs
abs :: Var S Term -> Box S Term -> Box S Term
abs x t = absRaw $ bind x t
app :: Box S Term -> Box S Term -> Box S Term
app t u = Term'App <$> t <*> u
boxTerm :: Term -> S (Box S Term)
boxTerm (Term'Var x) = return $ var x
boxTerm (Term'Abs b) = absRaw <$> boxBinder boxTerm b
boxTerm (Term'App t u) = app <$> boxTerm t <*> boxTerm u

eval :: Term -> S Term
eval t@(Term'App f a) = do
  ef <- eval f
  case ef of
    Term'Abs b -> eval =<< subst b a
    _ -> return t
eval t = return t

size :: Term -> S Int
size (Term'Var _) = return 0
size (Term'Abs b) = do
  (_, t) <- unbind b
  i <- size t
  return $ succ i
size (Term'App t u) = do
  i <- size t
  j <- size u
  return $ succ $ i + j

showTerm :: Term -> S Text
showTerm (Term'Var x) = return $ nameOf x
showTerm (Term'Abs b) = do
  (x, t) <- unbind b
  sh <- showTerm t
  return $ "\\" <> nameOf x <> "." <> sh
showTerm (Term'App t u) = do
  sht <- showTerm t
  shu <- showTerm u
  return $ "(" <> sht <> ") (" <> shu <> ")"

termIdentity, termFst, termDelta, termOmega :: S Term
termIdentity = do
  x <- newVar "x"
  unbox $ abs x $ var x
termFst = do
  x <- newVar "x"
  y <- newVar "y"
  unbox $ abs x $ abs y $ var x
termDelta = do
  x <- newVar "x"
  unbox $ abs x $ app (var x) (var x)
termOmega = do
  delta <- box <$> termDelta
  unbox $ app delta delta

spec :: Spec
spec = do
  describe "termIdentity" $ do
    it "should be size 1" $ do
      let r = 1
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termIdentity
        size t
    it "should be shown the intended text" $ do
      let r = "\\x.x"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termIdentity
        showTerm t
  describe "termFst" $ do
    it "should be size 2" $ do
      let r = 2
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termFst
        size t
    it "should be shown the intended text" $ do
      let r = "\\x.\\y.x"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termFst
        showTerm t
  describe "termDelta" $ do
    it "should be size 2" $ do
      let r = 2
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termDelta
        size t
    it "should be shown the intended text" $ do
      let r = "\\x.(x) (x)"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termDelta
        showTerm t
  describe "termOmega" $ do
    it "should be size 5" $ do
      let r = 5
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termOmega
        size t
    it "should be shown the intended text" $ do
      let r = "(\\x.(x) (x)) (\\x.(x) (x))"
      flip shouldReturn r $ flip evalStateT 0 $ runS $ do
        t <- termOmega
        showTerm t
