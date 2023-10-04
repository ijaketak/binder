{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Data.Binder
Description : Variable binding for abstract syntax tree
Copyright   : (c) 2023 Keito Kajitani
License     : MIT
Maintainer  : Keito Kajitani <ijaketak@gmail.com>

binder is purely functional implementation of Ocaml's bindlib.
It follows the style of higher-order abstract syntax,
and offers the representation of abstract syntax tree.
-}
module Data.Binder
-- * Preliminaries
  ( MonadNumbering(..)
-- * Variable and Box
  , Var
  , Box
  , MkFree(..)
-- ** Variable
  , var'Key
  , var'Name
  , var'Box
  , nameOf
  , boxVar
  , newVar
  , isClosed
  , occur
-- ** Box
  , unbox
  , box
  , apBox
  , boxApply
  , boxApply2
  , boxApply3
  , boxApply4
  , boxPair
  , boxTriple
  , boxT
-- * Variable binding
  , Binder
  , binder'Name
  , binder'Body
  , subst
  , buildBinder
  , bind
  , unbind
  , eqBinder
  , boxBinder
  ) where

import Control.Lens
import Data.Kind (Type)
import qualified Data.Map.Lazy as M
import Data.Maybe (fromJust)
import Data.Text (Text)
import Unsafe.Coerce

-- | Numbering monad.
class (Monad m, Ord (Numbering m)) => MonadNumbering m where
  type Numbering m :: Type
  numbering :: m (Numbering m)

-- | Representation of variable
--   for abstract syntax tree type @a@
--   with base numbering monad @m@.
data Var m a = Var
  { _var'Key :: !(Numbering m)
  , _var'Body :: VarBody m a
  }
data VarBody m a = VarBody
  { _varBody'Name :: Text
  , _varBody'Box :: Box m a
  }
-- | Representation of under-construction things
--   having type @a@ and containing variables.
data Box m a
  = Box'Closed a
  | Box'Env (EnvVar m) (Closure m a)

-- | Typeclass for free variable constructor.
class MkFree m a where
  mkFree :: Var m a -> m a

data AnyVar m = forall a. MkFree m a => AnyVar (Var m a)
type EnvVar m = M.Map (Numbering m) (AnyVar m)
data AnyMkFree m = forall a. MkFree m a => AnyMkFree a
type EnvMkFree m = M.Map (Numbering m) (AnyMkFree m)
newtype Closure m a = Closure { unClosure :: (EnvMkFree m) -> m a }

instance Functor m => Functor (Closure m) where
  fmap f cla = Closure $ fmap f . unClosure cla

instance Applicative m => Applicative (Closure m) where
  pure a = Closure $ const $ pure a
  clf <*> cla = Closure $ \env -> unClosure clf env <*> unClosure cla env

instance MonadNumbering m => Eq (Var m a) where
  Var x _ == Var y _ = x == y

instance MonadNumbering m => Ord (Var m a) where
  Var x _ `compare` Var y _ = x `compare` y

$(makeLenses ''Var)
$(makeLenses ''VarBody)


var'Name :: Lens' (Var m a) Text
var'Name = var'Body . varBody'Name
var'Box :: Lens' (Var m a) (Box m a)
var'Box = var'Body . varBody'Box

instance Show (Var m a) where
  showsPrec n x = showsPrec n $ x ^. var'Name
instance Show (VarBody m a) where
  showsPrec n x = showsPrec n $ x ^. varBody'Name
instance Show (AnyVar m) where
  showsPrec n (AnyVar x) = showsPrec n $ x ^. var'Name

-- | The name of variable.
nameOf :: Var m a -> Text
nameOf x = x ^. var'Name

-- | Smart constructor for 'Box'.
boxVar :: Var m a -> Box m a
boxVar x = x ^. var'Box

-- | Create a new variable with given name.
newVar :: forall m a. (MkFree m a, MonadNumbering m) => Text -> m (Var m a)
newVar name = do
  i <- numbering
  let x = let b = Box'Env
                (M.singleton i $ AnyVar x)
                (Closure $ \env ->
                  let f (AnyMkFree y) = pure $ unsafeCoerce y
                   in f $ fromJust $ M.lookup i env)
           in Var i $ VarBody name b
  return x


-- | 'Box' is closed if it exposes no free variables.
isClosed :: Box m a -> Bool
isClosed Box'Closed{} = True
isClosed Box'Env{} = False

-- | Check if the variable occurs in the box.
occur :: MonadNumbering m => Var m a -> Box m b -> Bool
occur _ (Box'Closed _) = False
occur v (Box'Env vs _) = M.member (v ^. var'Key) vs


instance Functor m => Functor (Box m) where
  fmap f (Box'Closed a) = Box'Closed (f a)
  fmap f (Box'Env vs ta) = Box'Env vs (f <$> ta)

instance (MonadNumbering m) => Applicative (Box m) where
  pure = Box'Closed
  Box'Closed f <*> Box'Closed a = Box'Closed (f a)
  Box'Closed f <*> Box'Env va ta = Box'Env va (f <$> ta)
  Box'Env vf tf <*> Box'Closed a = Box'Env vf (appClosure tf a)
   where
    appClosure clf x = Closure $ \env -> unClosure clf env <*> pure x
  Box'Env vf tf <*> Box'Env va ta = Box'Env (M.union vf va) (tf <*> ta)

-- | Pick out and complete the construction of @a@.
unbox :: forall m a. Monad m => Box m a -> m a
unbox (Box'Closed t) = pure t
unbox (Box'Env env cl) = unClosure cl =<< traverse f env
 where
  f (AnyVar x) = AnyMkFree @m <$> mkFree x

box :: MonadNumbering m => a -> Box m a
box = pure
apBox :: MonadNumbering m => Box m (a -> b) -> Box m a -> Box m b
apBox = (<*>)
boxApply :: Functor m => (a -> b) -> Box m a -> Box m b
boxApply = fmap
boxApply2 :: MonadNumbering m => (a -> b -> c) -> Box m a -> Box m b -> Box m c
boxApply2 f ta tb = f <$> ta <*> tb
boxApply3 :: MonadNumbering m => (a -> b -> c -> d) -> Box m a -> Box m b -> Box m c -> Box m d
boxApply3 f ta tb tc = f <$> ta <*> tb <*> tc
boxApply4 :: MonadNumbering m => (a -> b -> c -> d -> e) -> Box m a -> Box m b -> Box m c -> Box m d -> Box m e
boxApply4 f ta tb tc td = f <$> ta <*> tb <*> tc <*> td
boxPair :: MonadNumbering m => Box m a -> Box m b -> Box m (a, b)
boxPair = boxApply2 (,)
boxTriple :: MonadNumbering m => Box m a -> Box m b -> Box m c -> Box m (a, b, c)
boxTriple = boxApply3 (,,)
boxT :: (MonadNumbering m, Traversable t) => t (Box m a) -> Box m (t a)
boxT = sequenceA


-- | Variable binding.
--   Essentially, @Binder a m b@ means @a -> m b@.
data Binder a m b = Binder
  { _binder'Name :: Text
  , _binder'Body :: a -> m b
  }

$(makeLenses ''Binder)

-- | Variable substitution.
subst :: Binder a m b -> a -> m b
subst b = b ^. binder'Body

-- | unbinding
unbind :: (MkFree m a, MonadNumbering m) => Binder a m b -> m (Var m a, b)
unbind b = do
  x <- newVar $ b ^. binder'Name
  y <- subst b =<< mkFree x
  return (x, y)

unbind2 :: (MkFree m a, MonadNumbering m)
        => Binder a m b1 -> Binder a m b2 -> m (Var m a, b1, b2)
unbind2 b1 b2 = do
  x <- newVar $ b1 ^. binder'Name
  let v = mkFree x
  y1 <- subst b1 =<< v
  y2 <- subst b2 =<< v
  return (x, y1, y2)

-- | Check if two bindings are equal.
eqBinder :: (MkFree m a, MonadNumbering m)
         => (b -> b -> m Bool) -> Binder a m b -> Binder a m b -> m Bool
eqBinder eq f g = do
  (_, t, u) <- unbind2 f g
  eq t u


-- | Smart constructor for 'Binder'.
buildBinder :: Var m a -> (a -> m b) -> Binder a m b
buildBinder x body = Binder (x ^. var'Name) body

-- | binding
bind :: (MkFree m a, MonadNumbering m)
        => Var m a -> Box m b -> Box m (Binder a m b)
bind x (Box'Closed t) = Box'Closed $ buildBinder x $ const $ return t
bind x (Box'Env vs t) =
  let vs' = M.delete (x ^. var'Key) vs in if length vs' == 0
    then Box'Closed $ buildBinder x $
      \arg -> unClosure t $ M.singleton (x ^. var'Key) (AnyMkFree arg)
    else Box'Env vs' $ Closure $
      \ms -> return $ buildBinder x $
      \arg -> unClosure t $ M.insert (x ^. var'Key) (AnyMkFree arg) ms

boxBinder :: (MkFree m a, MonadNumbering m)
          => (b -> m (Box m b)) -> Binder a m b -> m (Box m (Binder a m b))
boxBinder f b = do
  (x, t) <- unbind b
  ft <- f t
  return $ bind x ft
