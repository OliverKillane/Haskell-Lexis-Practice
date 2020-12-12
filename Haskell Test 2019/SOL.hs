module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp n ns
  = snd $ head $ filter (\(i,_) -> i == n) ns

-- 3 marks
vars :: Formula -> [Id]
vars = sort . nub . getids
  where
    getids :: Formula -> [Id]
    getids f
      = case f of
        Var id   -> [id]
        Not f    -> vars f
        And f f' -> vars f ++ vars f'
        Or f f'  -> vars f ++ vars f'


-- 1 mark
idMap :: Formula -> IdMap
idMap f
  = zip (vars f) [1..] 

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF f 
  = case f of 
    Not (Not a)   -> toNNF a
    Not (Or a b)  -> toNNF (And (Not a) (Not b))
    Not (And a b) -> toNNF (Or (Not a) (Not b))
    Or a b        -> Or (toNNF a) (toNNF b)
    And a b       -> And (toNNF a) (toNNF b)
    Var id        -> Var id
    Not a         -> Not (toNNF a)

-- 3 marks
toCNF :: Formula -> CNF
toCNF = dist.toNNF
  where
    dist :: Formula -> CNF
    dist f = case f of
      Or a (And b c) -> And (dist (Or a b)) (dist (Or a c))
      Or (And a b) c -> And (dist (Or a c)) (dist(Or b c))
      Or a b -> Or (dist a) (dist b)
      And a b -> And (dist a) (dist b)
      a -> a

-- 4 marks
flatten :: CNF -> CNFRep
flatten cnf
  = forClause cnf
  where
    ids = idMap cnf
    forClause :: CNF -> CNFRep
    forClause f 
      = case f of
        And a b -> forClause a ++ forClause b
        a       -> [forAtom a]
    forAtom :: CNF -> [Int]
    forAtom f 
      = case f of
        Or a b -> forAtom a ++ forAtom b
        Var a -> [lookUp a ids]
        Not (Var a) -> [ - (lookUp a ids)]

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits cnf
  | uts == [] = (cnf, [])
  | otherwise = (cnf', uts ++ uts')
    where
      uts          = concat $ filter ((1 ==).length) cnf
      (cnf', uts') = propUnits $ foldl' (propagate) cnf uts

      remove :: Int -> [Int] -> [Int]
      remove _ [] = []
      remove n (x:xs)
        | n == x    = xs
        | otherwise = x:remove n xs 

      propagate :: CNFRep -> Int -> CNFRep
      propagate cnf ut = map (remove (-ut)) $ filter (ut `notElem`) cnf

-- 4 marks
dp :: CNFRep -> [[Int]]
dp cnf
  | any (==True) ([x == -x' | x <- uts', x'<- uts']) = []
  | cnf' == []                                       = [uts']
  | filter ([]/=) cnf' == []                         = []
  | otherwise                                        = sat1 ++ sat2
  where
    (cnf', uts') = propUnits cnf
    t            = cnf'!!0!!0
    sat1         = dp ([t]:cnf)
    sat2         = dp ([-t]:cnf)

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = map (sort . map (\x -> (find x ids, x == (abs x)))) $ (dp.flatten.toCNF.toNNF) f
  where
    ids = idMap f

    find n ns
      = fst $ head $ filter (\(_,v) -> v == n) ns

