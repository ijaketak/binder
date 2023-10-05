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
-- ** Variable
  , var'Key
  , var'Name
  , var'mkFree
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
  , boxList
  , boxJoin
-- * Variable binding
  , Binder
  , binder'Name
  , binder'mkFree
  , binder'Body
  , subst
  , buildBinder
  , bind
  , unbind
  , eqBinder
  , boxBinder
  , bindApply
-- * List
-- * Variable list
  , VarList
  , varList'Keys
  , varList'Names
  , varList'Boxes
  , namesOf
  , boxVarList
  , newVarList
-- * Binder for list
  , BinderList
  , binderList'Names
  , binderList'Body
  , binderList'mkFree
  , binderList'Arity
  , substList
  , eqBinderList
  , bindList
  , unbindList
  , boxBinderList
  , bindListApply
  ) where

import Control.Lens
import Control.Monad (join)
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
  , _varBody'mkFree :: Var m a -> m a
  , _varBody'Box :: Box m a
  }
-- | Representation of under-construction things
--   having type @a@ and containing variables.
data Box m a
  = Box'Closed a
  | Box'Env (EnvVar m) (Closure m a)

data AnyVar m = forall a. AnyVar (Var m a)
type EnvVar m = M.Map (Numbering m) (AnyVar m)
data AnyOne = forall a. AnyOne a
type EnvOne m = M.Map (Numbering m) AnyOne
newtype Closure m a = Closure { unClosure :: (EnvOne m) -> m a }

instance Functor m => Functor (Closure m) where
  fmap f cla = Closure $ fmap f . unClosure cla

instance Applicative m => Applicative (Closure m) where
  pure a = Closure $ const $ pure a
  clf <*> cla = Closure $ \env -> unClosure clf env <*> unClosure cla env

closureJoin :: Monad m => Closure m (m a) -> Closure m a
closureJoin cl = Closure $ \env -> join $ unClosure cl env

instance MonadNumbering m => Eq (Var m a) where
  Var x _ == Var y _ = x == y

instance MonadNumbering m => Ord (Var m a) where
  Var x _ `compare` Var y _ = x `compare` y

$(makeLenses ''Var)
$(makeLenses ''VarBody)


var'Name :: Lens' (Var m a) Text
var'Name = var'Body . varBody'Name
var'mkFree :: Lens' (Var m a) (Var m a -> m a)
var'mkFree = var'Body . varBody'mkFree
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
newVar :: forall m a. MonadNumbering m => Text -> (Var m a -> m a) -> m (Var m a)
newVar name mkFree = do
  i <- numbering
  let x = let b = Box'Env
                (M.singleton i $ AnyVar x)
                (Closure $ \env ->
                  let f (AnyOne y) = pure $ unsafeCoerce y
                   in f $ fromJust $ M.lookup i env)
           in Var i $ VarBody name mkFree b
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

instance MonadNumbering m => Applicative (Box m) where
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
  f (AnyVar x) = fmap AnyOne $ x ^. var'mkFree $ x

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
boxList :: MonadNumbering m => [Box m a] -> Box m [a]
boxList = sequenceA
boxJoin :: MonadNumbering m => Box m (m a) -> m (Box m a)
boxJoin (Box'Closed ma) = return . Box'Closed =<< ma
boxJoin (Box'Env env cl) = return $ Box'Env env $ closureJoin cl


-- | Variable binding.
--   Essentially, @Binder a m b@ means @a -> m b@.
data Binder a m b = Binder
  { _binder'Name :: Text
  , _binder'mkFree :: Var m a -> m a
  , _binder'Body :: a -> m b
  }

$(makeLenses ''Binder)

-- | Variable substitution.
subst :: Binder a m b -> a -> m b
subst b = b ^. binder'Body

-- | unbinding
unbind :: MonadNumbering m => Binder a m b -> m (Var m a, b)
unbind b = do
  let mkFree = b ^. binder'mkFree
  x <- newVar (b ^. binder'Name) mkFree
  y <- subst b =<< mkFree x
  return (x, y)

unbind2 :: MonadNumbering m
        => Binder a m b1 -> Binder a m b2 -> m (Var m a, b1, b2)
unbind2 b1 b2 = do
  let mkFree = b1 ^. binder'mkFree
  x <- newVar (b1 ^. binder'Name) mkFree
  v <- mkFree x
  y1 <- subst b1 v
  y2 <- subst b2 v
  return (x, y1, y2)

-- | Check if two bindings are equal.
eqBinder :: MonadNumbering m
         => (b -> b -> m Bool) -> Binder a m b -> Binder a m b -> m Bool
eqBinder eq f g = do
  (_, t, u) <- unbind2 f g
  eq t u


-- | Smart constructor for 'Binder'.
buildBinder :: Var m a -> (a -> m b) -> Binder a m b
buildBinder x body = Binder (x ^. var'Name) (x ^. var'mkFree) body

-- | binding
bind :: MonadNumbering m => Var m a -> Box m b -> Box m (Binder a m b)
bind x (Box'Closed t) = Box'Closed $ buildBinder x $ const $ return t
bind x (Box'Env vs t) =
  let vs' = M.delete (x ^. var'Key) vs in if length vs' == 0
    then Box'Closed $ buildBinder x $
      \arg -> unClosure t $ M.singleton (x ^. var'Key) (AnyOne arg)
    else Box'Env vs' $ Closure $
      \ms -> return $ buildBinder x $
      \arg -> unClosure t $ M.insert (x ^. var'Key) (AnyOne arg) ms

boxBinder :: MonadNumbering m
          => (b -> m (Box m b)) -> Binder a m b -> m (Box m (Binder a m b))
boxBinder f b = do
  (x, t) <- unbind b
  ft <- f t
  return $ bind x ft

bindApply :: MonadNumbering m => Box m (Binder a m b) -> Box m a -> m (Box m b)
bindApply b arg = boxJoin $ subst <$> b <*> arg


type VarList m a = [Var m a]

varList'Keys :: Getter (VarList m a) [Numbering m]
varList'Keys = to $ fmap $ view var'Key
varList'Names :: Getter (VarList m a) [Text]
varList'Names = to $ fmap $ view var'Name
varList'Boxes :: Getter (VarList m a) [Box m a]
varList'Boxes = to $ fmap $ view var'Box

-- | The names of variables.
namesOf :: VarList m a -> [Text]
namesOf = fmap $ view var'Name

-- | Smart constructor for a list of 'Box'.
boxVarList :: VarList m a -> [Box m a]
boxVarList = fmap $ view var'Box

-- | Create new variables with given names.
newVarList :: MonadNumbering m => [Text] -> (Var m a -> m a) -> m (VarList m a)
newVarList names mkFree = sequence $ flip fmap names $ \name -> newVar name mkFree


-- | Essentially, @BinderList a m b@ means @[a] -> m b@.
data BinderList a m b = BinderList
  { _binderList'Names :: [Text]
  , _binderList'mkFree :: Var m a -> m a
  , _binderList'Body :: [a] -> m b
  }

$(makeLenses ''BinderList)

binderList'Arity :: Getter (BinderList a m b) Int
binderList'Arity = binderList'Names . to length

-- | Variable substitution.
substList :: BinderList a m b -> [a] -> m b
substList ba = ba ^. binderList'Body

-- | unbinding
unbindList :: MonadNumbering m => BinderList a m b -> m (VarList m a, b)
unbindList ba = do
  let mkFree = ba ^. binderList'mkFree
  xs <- newVarList (ba ^. binderList'Names) mkFree
  y <- substList ba =<< traverse mkFree xs
  return (xs, y)

unbind2List :: MonadNumbering m
             => BinderList a m b1 -> BinderList a m b2
             -> m (VarList m a, b1, b2)
unbind2List ba1 ba2 = do
  let mkFree = ba1 ^. binderList'mkFree
  xs <- newVarList (ba1 ^. binderList'Names) mkFree
  vs <- traverse mkFree xs
  y1 <- substList ba1 vs
  y2 <- substList ba2 vs
  return (xs, y1, y2)

-- | Check if two bindings are equal.
eqBinderList :: MonadNumbering m
              => (b -> b -> m Bool)
              -> BinderList a m b -> BinderList a m b -> m Bool
eqBinderList eq f g =
  if f ^. binderList'Arity /= g ^. binderList'Arity
    then return False
    else do
      (_, t, u) <- unbind2List f g
      eq t u

-- | Smart constructor for 'BinderList.
buildBinderList :: VarList m a -> ([a] -> m b) -> BinderList a m b
buildBinderList xs body =
  BinderList (xs ^. varList'Names) (head xs ^. var'mkFree) body

deleteList :: Ord k => [k] -> M.Map k a -> M.Map k a
deleteList = flip $ foldl $ \m k -> M.delete k m
insertList :: Ord k => [k] -> [a] -> M.Map k a -> M.Map k a
insertList ks xs m = foldl f m $ zip ks xs
 where
  f n (k, x) = M.insert k x n
zipList :: Ord k => [k] -> [a] -> M.Map k a
zipList ks xs = insertList ks xs M.empty

-- | binding
bindList :: MonadNumbering m
          => VarList m a -> Box m b -> Box m (BinderList a m b)
bindList xs (Box'Closed t) = Box'Closed $ buildBinderList xs $ const $ return t
bindList xs (Box'Env vs t) =
  let vs' = deleteList (xs ^. varList'Keys) vs in if length vs' == 0
    then Box'Closed $ buildBinderList xs $
      \args -> unClosure t $
      zipList (xs ^. varList'Keys) (AnyOne <$> args)
    else Box'Env vs' $ Closure $
      \ms -> return $ buildBinderList xs $
      \args -> unClosure t $
      insertList (xs ^. varList'Keys) (AnyOne <$> args) ms

boxBinderList :: MonadNumbering m
               => (b -> m (Box m b)) -> BinderList a m b
               -> m (Box m (BinderList a m b))
boxBinderList f b = do
  (xs, t) <- unbindList b
  ft <- f t
  return $ bindList xs ft

bindListApply :: MonadNumbering m
              => Box m (BinderList a m b) -> Box m [a] -> m (Box m b)
bindListApply b args = boxJoin $ substList <$> b <*> args
