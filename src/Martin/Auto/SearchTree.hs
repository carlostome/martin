{-| This module contains an implementation of a search tree together with
- suitable search combinators to traverse it.
-}
module Martin.Auto.SearchTree where

import Data.Either

-- | A tree that only stores data in the leaves.
data SearchTree a = Leaf a | Node [SearchTree a]
  deriving (Eq, Ord, Show, Read)

instance Functor SearchTree where
  fmap f (Leaf x)  = Leaf (f x)
  fmap f (Node xs) = Node (map (fmap f) xs)

instance Applicative SearchTree where
  pure = Leaf
  (Leaf f) <*> x = fmap f x
  (Node xs) <*> x = Node $ map (<*> x) xs

-- | Quadratic complexity when using left associated binds, use with caution.
instance Monad SearchTree where
  Leaf x >>= f = f x
  Node xs >>= f = Node $ map (>>= f) xs

-- | Cuts a search tree at the given level, always resulting in a finite tree.
cutoff :: Int -> SearchTree a -> SearchTree a
cutoff n st
  | n <= 0 = Node []
  | otherwise = case st of
      l@Leaf{} -> l
      Node xs  -> Node $ map (cutoff (n - 1)) xs

-- | Depth-first search of a 'SearchTree'. Combine with 'cutoff' to achieve bounding behavior.
dfs :: SearchTree a -> [a]
dfs (Leaf x) = [x]
dfs (Node xs) = concatMap dfs xs

-- | Only retains leaves if they occur exactly at the given level, where the root is at level 1.
level :: Int -> SearchTree a -> Maybe (SearchTree a)
level n st
  | n <= 0 = Just $ Node []
  | n == 1 = case st of
      l@Leaf{} -> Just l  -- leaf at exactly the right level
      Node _   -> Just $ Node [] -- cutoff, but there's still stuff to come
  | otherwise = case st of
      Leaf _ -> Nothing   -- leaf too early
      Node xs -> Node <$> foldMap (fmap return . level (n - 1)) xs

-- | Performs an iterative deepening depth-first search on a search tree.
iddfs :: SearchTree a -> [a]
iddfs st = go 1 where
  go lvl = case dfs <$> level lvl st of
    Nothing -> []
    Just xs -> xs ++ go (lvl + 1)

-- | Performs a breadth-first search of a tree.
bfs :: SearchTree a -> [a]
bfs st = go [st] where
  go lvl =
    let (now, later) = partitionEithers $ map next lvl
    in now ++ concatMap go later
  next (Leaf x) = Left x
  next (Node xs) = Right xs
