module Control.Monad.Freer where

import Brat.Syntax.Port (End)
import Brat.Syntax.Value (Val)
import Hasochism (N(..))

import Control.Monad ((>=>))
import Data.Kind (Type)
import qualified Data.Map as M
import qualified Data.Set as S

-- A mapping of metavars to metavars, for a single problem:
--  * e -> Unstuck means e has been solved
--  * e -> Awaiting es means the problem's been transferred
--  * e not in news means no change to e
newtype News = News (M.Map End Stuck)

updateEnd :: News -> End -> Stuck
updateEnd (News m) e = case M.lookup e m of
  Nothing ->  AwaitingAny (S.singleton e)
  Just s -> s

-- The RHS of the operation is the newer news
-- Invariant: The domains of these Newses are disjoint
instance Semigroup News where
  (News m1) <> n2@(News m2) = News (m2 `M.union` (M.map (/// n2) m1))

instance Monoid News where
  mempty = News M.empty

data Stuck
 = Unstuck
 | AwaitingAny (S.Set End)
 deriving Show

instance Semigroup Stuck where
  (AwaitingAny es1) <> (AwaitingAny es2) = AwaitingAny (S.union es1 es2)
  _ <> _ = Unstuck

instance Monoid Stuck where
  mempty = AwaitingAny S.empty

data Free (sig :: Type -> Type) (v :: Type) where
  Ret :: v -> Free sig v
  Req ::  sig t -> (t -> Free sig v) -> Free sig v
  Define :: String -> End -> Val Z -> (News -> Free sig v) -> Free sig v
  Yield :: Stuck -> (News -> Free sig v) -> Free sig v
  Fork :: String -> Free sig () -> Free sig v -> Free sig v

instance Functor (Free sig) where
  fmap f (Ret v) = Ret (f v)
  fmap f (Req sig k) = Req sig (fmap f . k)
  fmap f (Define lbl e v k) = Define lbl e v (fmap f . k)
  fmap f (Yield st k) = Yield st (fmap f . k)
  fmap f (Fork d par c) = Fork d par (fmap f c)

class NewsWatcher t where
  (///) :: t -> News -> t

instance NewsWatcher Stuck where
  Unstuck /// _ = Unstuck
  (AwaitingAny es) /// n = foldMap (updateEnd n) es

instance NewsWatcher (News -> t) where
  f /// n = f . (n <>)

instance NewsWatcher (Free sig v) where
  Ret v /// _ = Ret v
  Req sig k /// n = Req sig $ \v -> k v /// n
  Define lbl e v k /// n = Define lbl e v (k /// n)
  Yield st k /// n = Yield (st /// n) (k /// n)
  Fork d par c /// n = Fork d (par /// n) (c /// n)

instance Applicative (Free sig) where
  pure = Ret

  -- Left biased scheduling of commands:
  -- First, get rid of Yield Unstuck
  Yield Unstuck k <*> a = k mempty <*> a
  f <*> Yield Unstuck k = f <*> k mempty

  -- Aggressively forward Forks
  Fork d par c <*> ma = Fork d par (c <*> ma)
  ma <*> Fork d par c = Fork d par (ma <*> c)

  -- Make progress on the left
  Ret f <*> ma = fmap f ma
  Req sig k <*> ma = Req sig ((<*> ma) . k)
  Define lbl e v k1 <*> ma = Define lbl e v $ \n -> (k1 n) <*> (ma /// n)

  -- What happens when Yield is on the left
  y <*> Ret v = fmap ($ v) y
  y <*> Req sig k = Req sig $ \v -> y <*> k v
  y1@(Yield st1 _) <*> y2@(Yield st2 _) = Yield (st1 <> st2) $
    \n -> (y1 /// n) <*> (y2 /// n)
  y <*> Define lbl e v k = Define lbl e v $ \n -> (y /// n) <*> k n

instance Monad (Free sig) where
  Ret v >>= k = k v
  Req r j >>= k = Req r (j >=> k)
  Define lbl e v k1 >>= k2 = Define lbl e v (k1 >=> k2)
  Yield st k1 >>= k2 = Yield st (k1 >=> k2)
  --- equivalent to
  -- Yield st k1 >>= k2 = Yield st (\n -> (k1 n) >>= k2)
  Fork d par k1 >>= k2 = Fork d par (k1 >>= k2)

req :: sig t -> Free sig t
req s = Req s Ret
