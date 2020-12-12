module Tries where
import Data.List hiding (insert)
import Data.Bits
import Types
import HashFunctions
import Examples 

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes 0 = 0
countOnes n = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]!!bs + countOnes quot
  where
    (quot, bs) = quotRem n 16


countOnesFrom :: Int -> Int -> Int
countOnesFrom i n
  = countOnes $ n .&.  (2^i-1)

getIndex :: Int -> Int -> Int -> Int
getIndex n ind bsize = (n .&. (2^(bsize * (ind+1))-1)) `div` 2^(ind*bsize)

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace i ls l
  = take i ls ++ [l] ++ drop (i+1) ls

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt i l ls 
  = take i ls ++ [l] ++ drop i ls

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie _ f (Leaf ns) = f ns
sumTrie f f' (Node _ nodes) = sum $ map sumnodes nodes
  where
    sumnodes :: SubNode -> Int
    sumnodes (Term n) = f n
    sumnodes (SubTrie t) = sumTrie f f' t

--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)


member :: Int -> Hash -> Trie -> Int -> Bool
member n h t bsize = traverse 0 t
  where
    traverse :: Int -> Trie -> Bool
    traverse _ (Leaf ns) = n `elem` ns
    traverse d (Node bvc subN) 
      | not (testBit bvc select) = False
      | otherwise 
        = case subN!!(countOnesFrom select bvc) of
          Term a    -> a == n
          SubTrie t -> traverse (d+1) t
        where
          select = getIndex h d bsize


--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert hash maxd bsize n t
  = inserter n 0 t
    where
      inserter :: Int -> Int -> Trie -> Trie
      inserter v _ (Leaf ns)
        | v `elem` ns = Leaf ns
        | otherwise   = Leaf (v:ns)
      inserter v d (Node bvc subN)
        | d + 1 == maxd      = Leaf [v]
        | testBit bvc select = Node bvc (replace index subN subn')
        | otherwise          = Node (setBit bvc select) (insertAt index (Term v) subN)
          where
            select = getIndex (hash v) d bsize
            index  = countOnesFrom select bvc
            subn'  = 
              case subN!!index of
                SubTrie t -> SubTrie (inserter v (d+1) t)
                Term v'   -> if v==v' then Term v' 
                             else          SubTrie (inserter v' (d+1) (inserter v (d+1) empty))



buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hash maxd bsize ns
  = foldl' (flip (insert hash maxd bsize)) empty ns