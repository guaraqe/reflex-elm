{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}

module Reflex.Elm
  (
  -- * Update
    Update
  , makeUpdate
  , simpleUpdate
  , changeUpdate
  -- * View
  , View
  , getView
  , makeView
  , simpleView
  , changeView
  , changeViewUniq
  , decorateView
  , dynView
  , monadView
  , traceViewIn
  , traceViewOut
  -- * Elm
  , Elm
  , makeElm
  , finalElm
  , simpleElm
  , simpleFinalElm
  , rawElm
  , runElm
  , elmToView
  -- * Extra
  , arrMay
  ) where

import Prelude hiding ((.), id)

import Reflex
import Reflex.Dom

import Data.Semigroup

import Data.Void
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Data.Profunctor
import Data.Profunctor.Product

import Control.Arrow
import Control.Category

import Control.Applicative (liftA2)
import Control.Monad
import Control.Monad.Fix

import Control.Lens

--------------------------------------------------------------------------------
-- Update
--------------------------------------------------------------------------------

newtype Update model action = Update (action -> model -> model)

instance Contravariant (Update model) where
  contramap f (Update g) = Update (g . f)
  {-# INLINE contramap #-}

instance Decidable (Update model) where
  lose f = Update $ absurd . f
  {-# INLINE lose #-}
  choose f (Update g) (Update h) = Update $ either g h . f
  {-# INLINE choose #-}

instance Divisible (Update model) where
  divide f (Update g) (Update h) = Update $ \a -> case f a of
    (b, c) -> g b . h c
  conquer = Update $ const id

makeUpdate :: (action -> model -> model) -> Update model action
makeUpdate = Update
{-# INLINE makeUpdate #-}

simpleUpdate :: Update model (model -> model)
simpleUpdate = Update id
{-# INLINE simpleUpdate #-}

changeUpdate :: Setter' b a -> Update a action -> Update b action
changeUpdate l (Update f) = Update (\action -> over l (f action))
{-# INLINE changeUpdate #-}

--------------------------------------------------------------------------------
-- View
--------------------------------------------------------------------------------

newtype View t m model = View (Dynamic t model -> m (Event t (model -> model)))

getView :: View t m model -> Dynamic t model -> m (Event t (model -> model))
getView (View f) = f
{-# INLINE getView #-}

makeView ::
  (Reflex t, Functor m) =>
  Update model action ->
  (Dynamic t model -> m (Event t action)) ->
  View t m model
makeView (Update f) g = View (fmap (fmap f) . g)
{-# INLINE makeView #-}

runView ::
  (Reflex t, MonadFix m, MonadHold t m) =>
  View t m model -> model -> m (Dynamic t model)
runView (View view) initial = do
  rec modelDyn <- foldDyn ($) initial updates
      updates <- view $ modelDyn
  return modelDyn
{-# INLINE runView #-}

finalView ::
  (Reflex t, MonadFix m, MonadHold t m) =>
  View t m model -> model -> m (Dynamic t ())
finalView (View view) initial = do
  rec modelDyn <- foldDyn ($) initial updates
      updates <- view $ modelDyn
  return $ pure ()
{-# INLINE finalView #-}

simpleView ::
  (Dynamic t model -> m (Event t (model -> model))) -> View t m model
simpleView f = View f
{-# INLINE simpleView #-}

decorateView ::
  MonadWidget t m =>
  View t m b ->
  (forall a . MonadWidget t m => m a -> m a) ->
  View t m b
decorateView (View g) f = View (f . g)

changeView ::
  (Reflex t, Functor m) => Lens' b a -> View t m a -> View t m b
changeView l (View f) = View $ fmap (fmap (over l)) . f . fmap (view l)
{-# INLINE changeView #-}

changeViewUniq ::
  (Reflex t, MonadHold t m, MonadFix m, Eq a) => Lens' b a -> View t m a -> View t m b
changeViewUniq l (View f) = View $ \d -> do
  u <- holdUniqDyn $ fmap (view l) d
  fmap (over l) <$> f u
{-# INLINE changeViewUniq #-}

dynView ::
  MonadWidget t m =>
  Dynamic t (View t m model) -> View t m model
dynView d = View $ \a -> do
  e <- dyn $ fmap (\v -> getView v a) d
  switchPromptly never e
{-# INLINE dynView #-}

monadView ::
  Monad m =>
  m (View t m model) -> View t m model
monadView d = View $ \a -> do
  d' <- d
  getView d' a
{-# INLINE monadView #-}

traceViewIn :: (Reflex t, Show a) => String -> View t m a -> View t m a
traceViewIn s (View f) = View $ \x -> f (traceDyn s x)
{-# INLINE traceViewIn #-}

traceViewOut ::
  (Reflex t, Functor m, Show a) =>
  String -> View t m a -> View t m a
traceViewOut s (View f) = View $ fmap (traceEventWith (const s)) . f
{-# INLINE traceViewOut #-}

--------------------------------------------------------------------------------
-- Semigroup and Monoid

instance (Reflex t, Applicative m) => Semigroup (View t m model) where
  (<>) = mappend
  {-# INLINE (<>) #-}

instance (Reflex t, Applicative m) => Monoid (View t m model) where
  mempty = View (\_ -> pure never)
  {-# INLINE mempty #-}
  mappend (View f) (View g) = View (mergeView f g)
  {-# INLINE mappend #-}

mergeView ::
  (Reflex t, Applicative m) =>
  (Dynamic t model -> m (Event t (model -> model))) ->
  (Dynamic t model -> m (Event t (model -> model))) ->
  (Dynamic t model -> m (Event t (model -> model)))
mergeView f g x =
  liftA2 (\ev1 ev2 -> fmap appEndo (fmap Endo ev1 <> fmap Endo ev2)) (f x) (g x)
{-# INLINE mergeView #-}

--------------------------------------------------------------------------------
-- Elm
--------------------------------------------------------------------------------

newtype Elm t m a b = Elm (a -> m (Dynamic t b))

makeElm ::
  (Reflex t, MonadFix m, MonadHold t m) =>
  (a -> model) -> View t m model -> (model -> b) -> Elm t m a b
makeElm f view g = Elm (fmap (fmap g) . runView view . f)
{-# INLINE makeElm #-}

finalElm ::
  (Reflex t, MonadFix m, MonadHold t m) =>
  (a -> model) -> View t m model -> Elm t m a ()
finalElm f view = Elm (finalView view . f)
{-# INLINE finalElm #-}

simpleElm ::
  (Reflex t, MonadFix m, MonadHold t m) =>
  View t m model -> Elm t m model model
simpleElm view = Elm (runView view)
{-# INLINE simpleElm #-}

simpleFinalElm ::
  (Reflex t, MonadFix m, MonadHold t m) =>
  View t m model -> Elm t m model ()
simpleFinalElm view = Elm (finalView view)
{-# INLINE simpleFinalElm #-}

runElm :: Elm t m a b -> a -> m (Dynamic t b)
runElm (Elm f) = f
{-# INLINE runElm #-}

rawElm :: (a -> m (Dynamic t b)) -> Elm t m a b
rawElm = Elm
{-# INLINE rawElm #-}

elmToView ::
  (MonadWidget t m, Eq a) =>
  (model -> a) -> Elm t m a b -> Update model b -> View t m model
elmToView f (Elm elm) up = makeView up $  \d -> do
  a <- holdUniqDyn (fmap f d)
  fmap updated $ bindDyn elm a
{-# INLINE elmToView #-}

--------------------------------------------------------------------------------
-- Functor, Applicative, Monad

instance (Reflex t, Functor m) => Functor (Elm t m a) where
  fmap f (Elm elm) = Elm (fmap (fmap f) . elm)
  {-# INLINE fmap #-}

instance (Reflex t, Applicative m) => Applicative (Elm t m a) where
  pure x = Elm (\_ -> pure (pure x))
  {-# INLINE pure #-}
  (<*>) = apElm
  {-# INLINE (<*>) #-}

apElm ::
  (Reflex t, Applicative m) =>
  Elm t m a (b -> c) -> Elm t m a b -> Elm t m a c
apElm (Elm elm1) (Elm elm2) =
  Elm $ \x -> liftA2 (<*>) (elm1 x) (elm2 x)
{-# INLINE apElm #-}

instance MonadWidget t m => Monad (Elm t m a) where
  return = pure
  {-# INLINE return #-}
  (>>=) = bindElm
  {-# INLINE (>>=) #-}

bindElm ::
  MonadWidget t m =>
  Elm t m a b -> (b -> Elm t m a c) -> Elm t m a c
bindElm (Elm elm) f = Elm $ \a -> do
  b <- elm a
  let e = fmap (($ a) . runElm . f) b
  fmap join $ widgetHold (join $ sample (current e)) (updated e)
{-# INLINE bindElm #-}

--------------------------------------------------------------------------------
-- Category

instance MonadWidget t m => Category (Elm t m) where
  id = Elm (pure . pure)
  {-# INLINE id #-}
  (.) = composeElm
  {-# INLINE (.) #-}

composeElm :: MonadWidget t m => Elm t m b c -> Elm t m a b -> Elm t m a c
composeElm (Elm elm2) (Elm elm1) =
  Elm $ \x -> do
    a <- elm1 x
    bindDyn elm2 a
{-# INLINE composeElm #-}

bindDyn ::
  MonadWidget t m =>
  (a -> m (Dynamic t b)) -> Dynamic t a -> m (Dynamic t b)
bindDyn f x =
  fmap join $ widgetHold start (fmap f (updated x))
  where start = sample (current x) >>= f
{-# INLINE bindDyn #-}

--------------------------------------------------------------------------------
-- Profunctor

instance (Reflex t, Functor m) => Profunctor (Elm t m) where
  dimap f g (Elm elm) = Elm (fmap (fmap g) . elm . f)
  {-# INLINE dimap #-}

--instance (Reflex t, Monad m) => ProductProfunctor (Elm t m) where
instance MonadWidget t m => ProductProfunctor (Elm t m) where
  --purePP = pure
  --(****) = (<*>)
  (***!) = (***)
  {-# INLINE (***!) #-}
  empty = arr id
  {-# INLINE empty #-}

--------------------------------------------------------------------------------
-- Arrow

instance MonadWidget t m => Arrow (Elm t m) where
  arr f = Elm (pure . pure . f)
  {-# INLINE arr #-}
  (***) = parElm
  {-# INLINE (***) #-}
  (&&&) = fanoutElm
  {-# INLINE (&&&) #-}

parElm ::
  (Reflex t, Applicative m) =>
  Elm t m a b -> Elm t m c d -> Elm t m (a,c) (b,d)
parElm (Elm elm1) (Elm elm2) =
  Elm $ \(a,c) -> liftA2 (liftA2 (,)) (elm1 a) (elm2 c)
{-# INLINE parElm #-}

fanoutElm ::
  (Reflex t, Applicative m) =>
  Elm t m a b -> Elm t m a c -> Elm t m a (b,c)
fanoutElm f g = apElm (fmap (\b -> \c -> (b,c)) f) g
{-# INLINE fanoutElm #-}

--------------------------------------------------------------------------------
-- ArrowChoice

instance MonadWidget t m => ArrowChoice (Elm t m) where
  (+++) = choiceElm
  {-# INLINE (+++) #-}

choiceElm ::
  (Reflex t, Monad m) =>
  Elm t m a b -> Elm t m c d -> Elm t m (Either a c) (Either b d)
choiceElm (Elm elm1) (Elm elm2) =
  Elm $ \case
    Left a -> fmap (fmap Left) (elm1 a)
    Right c -> fmap (fmap Right) (elm2 c)
{-# INLINE choiceElm #-}

arrMay :: (Profunctor a, ArrowChoice a) => a b c -> a (Maybe b) (Maybe c)
arrMay a =
  dimap (maybe (Left ()) Right) (either (const Nothing) Just) (arr id +++ a)
{-# INLINE arrMay #-}

--------------------------------------------------------------------------------

instance MonadWidget t m => ArrowApply (Elm t m) where
  app = Elm $ \(Elm f, a) -> f a
  {-# INLINE app #-}
