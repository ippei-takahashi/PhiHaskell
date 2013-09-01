{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeFamilies, TypeOperators #-}
module Phi where

import Data.List

bot = undefined

-- Prod
infixr 6 :*:
data (:*:) a b = a :*: b 
  deriving (Ord, Eq, Show, Read)

exl (x :*: y) = x
exr (x :*: y) = y

prod :: (a -> b -> c) -> a :*: b -> c
prod f (x :*: y) = f x y

pzip :: [a] :*: [b] -> [a :*: b]
pzip = unfoldr f where
  f ([] :*: _)          = Nothing
  f (_ :*: [])          = Nothing
  f ((x:xs) :*: (y:ys)) = Just (x :*: y, xs :*: ys)

unprod :: (a :*: b -> c) -> a -> b -> c
unprod f x y = f (x :*: y)

unpzip :: [a :*: b] -> [a] :*: [b]
unpzip = map exl /\ map exr

infixr 7 /\
(/\) :: (a -> b) -> (a -> c) -> a -> b :*: c
(f /\ g) x = f x :*: g x 

infixr 8 ><
(><) :: (a -> c) -> (b -> d) -> a :*: b -> c :*: d
f >< g = f . exl /\ g . exr

-- Coprod
infixr 4 :+:
data (:+:) a b = Inl a | Inr b
  deriving (Ord, Eq, Show, Read)

(?) :: (a -> Bool) -> a -> a :+: a
p ? x = if p x
  then Inl x
  else Inr x

infixr 5 \/
(\/) :: (a -> c) -> (b -> c) -> a :+: b -> c
(f \/ g) (Inl x)  = f x
(f \/ g) (Inr x)  = g x

infixr 6 -|-
(-|-) :: (a -> c) -> (b -> d) -> a :+: b -> c :+: d
f -|- g = Inl . f \/ Inr . g

type family F t :: * -> *
data family D t :: * -> *

class Functor (F t) => InitialAlgebra t where
  out :: t -> F t t
  
  cata :: (F t a -> a) -> t -> a
  cata phi = h where
    h = phi . fmap h . out
  
  para :: (F t (a :*: t) -> a) -> t -> a
  para phi = h where
    h = phi . fmap (h /\ id) . out

class Functor (F t) => FinalCoalgebra t where
  inn :: F t t -> t
  
  ana :: (a -> F t a) -> a -> t
  ana psi = h where
    h = inn . fmap h . psi

  apo :: (a -> F t (a :+: t)) -> a -> t
  apo psi = h where
    h = inn . fmap (h \/ id) . psi

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo phi psi = h where
  h = phi . fmap h . psi

newtype instance D [a] b = FList {unFList :: () :+: a :*: b}
  deriving (Ord, Eq, Show, Read)
type instance F [a] = D [a]

instance Functor (D [a]) where
  fmap f = FList . (id -|- id >< f) . unFList

instance InitialAlgebra [a] where
  out []     = FList $ Inl ()
  out (x:xs) = FList $ Inr (x :*: xs)
  
instance FinalCoalgebra [a] where
  inn = (f \/ g) . unFList where
    f = const []
    g (x :*: xs) = x : xs

