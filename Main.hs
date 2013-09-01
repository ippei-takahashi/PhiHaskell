{-# Language RankNTypes, FlexibleInstances, TemplateHaskell, TypeFamilies, TypeOperators#-}
module Main where

import Control.Monad
import Language.Haskell.TH
import System.Random(randomRs, mkStdGen)
import PhiTH
import Phi

data BinTree a = Tip | Branch (BinTree a) a (BinTree a)
  deriving (Eq, Ord, Show, Read)

data LeafTree a = Leaf a | Split (LeafTree a) (LeafTree a)
  deriving (Eq, Ord, Show, Read)

data RoseTree a = RoseTree [a] [RoseTree a]
  deriving (Eq, Ord, Show, Read)

instance Functor BinTree where
  fmap f = h where
    h Tip         = Tip
    h (Branch l v r) = Branch (h l) (f v) $ h r


deriveAlg ''BinTree
deriveAlg ''LeafTree
deriveAlg ''RoseTree

tree = Branch (Branch (Branch Tip 3 (Branch Tip 4 Tip)) 2 Tip) 1 (Branch Tip 2 Tip)
rtree = RoseTree [1, 2, 3] [RoseTree [2, 3, 4] [], RoseTree [3, 4, 5] [RoseTree [5, 6, 7] []]]

randomSeq :: Int -> [Double]
randomSeq = randomRs (0, 1) . mkStdGen

cataL z f = cata ((const z \/ f) . unFList)
paraL z f = para ((const z \/ f) . unFList)

cataT z f = cata ((const z \/ f) . unFBinTree)
paraT z f = para ((const z \/ f) . unFBinTree)

cataPT f g = cata ((f \/ g) . unFLeafTree)
paraPT f g = para ((f \/ g) . unFLeafTree)

depth :: BinTree a -> Integer
depth = cataT 0 phi where
  phi (l :*: _ :*: r) = 1 + max l r
  
fib :: Integer :*: Integer -> [Integer]
fib = ana (FList . psi) where
  psi (n1 :*: n2) = Inr $ n1 :*: n2 :*: (n1 + n2)

tails :: [a] -> [[a]]
tails = paraL [[]] phi where
  phi (x :*: tls :*: xs) = (x:xs) : tls

inits :: [a] -> [[a]]
inits = cataL [[]] phi where
  phi (x :*: xs) = [] : map (x:) xs

segs :: [a] -> [[a]]
segs = paraL [[]] phi where
  phi (x :*: sgs :*: xs) = inits (x:xs) ++ sgs

{-
segs = concat . map inits . tails
     = cataL [] f . map (inits) . paraL [[]] g  where
         f (xs :*: ys) = xs ++ ys
         g (x :*: tls :*: xs) = (x:xs) : tls
     = cataL [[]] h . paraL [[]] g where
         h (xs :*: ys) = inits xs ++ ys
     = paraL [[]] phi where
         phi (x :*: sgs :*: xs) = inits (x:xs) ++ sgs
-}


merge :: (a -> a -> Bool) -> [a] :*: [a] -> [a]
merge pred = apo (FList . psi) where
  psi ([] :*: [])     = Inl ()
  psi ((x:xs) :*: []) = Inr (x :*: Inr xs)  
  psi ([] :*: (y:ys)) = Inr (y :*: Inr ys)
  psi (xss@(x:xs) :*: yss@(y:ys)) 
    | pred x y        = Inr (x :*: Inl (xs :*: yss))
    | otherwise       = Inr (y :*: Inl (xss :*: ys))

split :: [a] -> [a] :*: [a]
split = cataL ([] :*: []) phi where
  phi (x :*: ys :*: zs) = (x:zs) :*: ys

merges :: (Ord a) => LeafTree a -> [a]
merges = cataPT one phi where
  one x   = [x]
  phi     = merge (<)

splits :: [a] -> LeafTree a
splits = ana (FLeafTree . psi) where
  psi []  = bot
  psi [x] = Inl x
  psi xs  = Inr $ split xs

mergeSort :: (Ord a) => [a] -> [a]
mergeSort [] = []
mergeSort xs = merges $ splits xs

insert :: (a -> a -> Bool) -> a :*: [a] -> [a]
insert pred = apo (FList . psi) where
  psi (x :*: []) = Inr (x :*: Inr [])
  psi (x :*: zs@(y:ys))
    | pred x y     = Inr (x :*: Inr zs)
    | otherwise  = Inr (y :*: Inl (x :*: ys))

insertSort :: (Ord a) => [a] -> [a]
insertSort = cataL [] (insert (<))

pfilter :: (a -> Bool) -> [a] -> [a] :*: [a]
pfilter p = cata ((const ([] :*: []) \/ step) . unFList) where
  step (x :*: ys :*: zs) = if p x
    then (x:ys) :*: zs
    else ys :*: (x:zs)

partition :: (Ord a) => [a] -> [a] :*: [a]
partition (x:xs) = pfilter (< x) $ xs

quickSort :: (Ord a) => [a] -> [a]
quickSort = hylo (phi . unFBinTree) (FBinTree . psi) where
  phi = const [] \/ glue
  glue (l :*: v :*: r) = l ++ (v:r)
  psi [] = Inl ()
  psi xs@(x:_) = Inr (l :*: x :*: r) where
    l :*: r = partition xs

mss :: [Int] -> Int
mss = exl . cataL (0 :*: 0) (phi1 /\ phi2) where
        phi1 (x :*: y :*: z) = max (max 0 (x + z)) y
        phi2 (x :*: y :*: z) = max 0 (x + z)
{-
mss = maxL . map sum . segs
    = cataL 0 f . map sum . paraL [[]] g where
        f (x :*: y) = max x y
        g (x :*: sgs :*: xs) = inits (x:xs) ++ sgs
    = cataL 0 f . map sum . exl . cataL ([[]] :*: [[]]) (g1 /\ g2) where
        g1 (x :*: ys :*: zs) = ([] : map (x:) zs) ++ ys
        g2 (x :*: ys :*: zs) = [] : map (x:) zs
        {
            map sum (([] : map (x:) zs) ++ ys)
          = map sum ([] : map (x:) zs) ++ map sum ys
          = (0 : map (x+) (map sum zs)) ++ map sum ys
        }
    = cataL 0 f . exl . cataL ([0] :*: [0]) (h1 /\ h2) where
        h1 (x :*: ys :*: zs) = (0 : map (x+) zs) ++ ys
        h2 (x :*: ys :*: zs) = 0 : map (x+) zs
        {
            maxL ((0 : map (x+) zs) ++ ys)
          = max (max 0 (maxL (map (x+) zs))) (maxL ys)
          = max (max 0 (x + maxL zs)) (maxL ys)    
        }
    = exl . cataL (0 :*: 0) (phi1 /\ phi2) where
        phi1 (x :*: y :*: z) = max (max 0 (x + z)) y
        phi2 (x :*: y :*: z) = max 0 (x + z)
-}


test :: (Num a) => RoseTree a -> a
test = cata (phi . unFRoseTree) where
  phi (xs :*: []) = sum xs
  phi (xs :*: ys) = sum xs + sum ys
