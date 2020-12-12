module Radix where
  
data Tree a = Empty | Leaf a | Node a (Tree a) (Tree a)
            deriving (Eq, Show)

type IntTree = Tree Int

type RadixTree = Tree Bool

type BitString = [Int]

--------------------------------------------------------------------------

buildIntTree :: [Int] -> IntTree
buildIntTree
  = foldr add Empty
  where
    add x Empty
      = Leaf x
    add x (Leaf y)
      = add x (Node y Empty Empty)
    add x t@(Node y l r)
      | x == y    = t
      | x < y     = Node y (add x l) r
      | otherwise = Node y l (add x r)

--------------------------------------------------------------------------

a, m :: Integer
m = 1073741824
a = 16387

rand :: Integer -> [Double]
rand s
  = fromInteger s / fromInteger m : rand s' where s' = (s * a) `mod` m

randomInts :: Int -> Int -> Integer -> [Int]
randomInts m n s
  = take m (map (round . (+1) . (* (fromIntegral n))) (rand s))

rs :: [Int]
rs = randomInts 1000 500 765539

--------------------------------------------------------------------------
-- Pre (universal): all integers are non-negative

size :: IntTree -> Int
size Empty = 1
size (Leaf _) = 5
size (Node _ t t') = 13 + size t + size t'

size' :: RadixTree -> Int
size' Empty = 0
size' (Leaf _) = 1
size' (Node _ t t') = 9 + size' t + size' t'

binary :: Int -> BitString
binary 0 = [0]
binary 1 = [1]
binary d = binary n ++ [ns]
  where
    (n, ns) = quotRem d 2
    


insert :: BitString -> RadixTree -> RadixTree
insert [] (Node _ t t') = Node True t t'
insert [] (Leaf _) = Leaf True
insert (b:bs) (Leaf a)
  | b == 0    = Node a (insert bs (Leaf False)) (Leaf False)
  | otherwise = Node a (Leaf False) (insert bs (Leaf False))
insert (b:bs) (Node a t t')
  | b == 0    = Node a (insert bs t) t'
  | otherwise = Node a t (insert bs t')

buildRadixTree :: [Int] -> RadixTree
buildRadixTree = buildhelper (Leaf False)
  where
    buildhelper :: RadixTree -> [Int] -> RadixTree
    buildhelper t [] = t
    buildhelper t (b:bs) = buildhelper (insert (binary b) t) bs

member :: Int -> RadixTree -> Bool
member = traverse . binary
  where
    traverse :: [Int] -> RadixTree -> Bool
    traverse [] (Node True _ _) = True
    traverse [] (Leaf True) = True
    traverse (b:bs) (Node _ t t')
      | b == 0 = traverse bs t
      | otherwise = traverse bs t'
    traverse _ _ = False

union :: RadixTree -> RadixTree -> RadixTree
union (Leaf v) (Leaf v') = Leaf (v||v')
union (Node v1 t1 t1') (Node v2 t2 t2') = Node (v1||v2) (union t1 t2) (union t1' t2')
union (Node v t t') (Leaf v') = Node (v||v') t t'
union (Leaf v') (Node v t t') = Node (v||v') t t'

intersection :: RadixTree -> RadixTree -> RadixTree
intersection (Leaf v) (Leaf v') = Leaf (v && v')
intersection (Node v1 t1 t1') (Node v2 t2 t2') = Node (v1&&v2) (intersection t1 t2) (intersection t1' t2')
intersection (Node v _ _) (Leaf v') = Leaf (v && v')
intersection (Leaf v) (Node v' _ _) = Leaf (v && v')



-- CONCLUSION: The break-even point is 205.

-----------------------------------------------------------------------------
-- Some test trees...

figure :: RadixTree
figure
  = Node False (Leaf True)
               (Node True (Leaf False)
                          (Node True (Node False (Leaf True)
                                                 (Leaf False))
                                     (Leaf True)))

t1 :: IntTree
t1 = Node 20 (Node 8 Empty
                     (Node 12 Empty
                              Empty))
             Empty

t2 :: RadixTree
t2 = Node False (Node False (Leaf True)
                            (Node True (Leaf False) (Leaf True)))
                (Leaf True)

