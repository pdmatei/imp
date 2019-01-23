{-# LANGUAGE ForeignFunctionInterface, 
             CPP, 
             DeriveFunctor, 
             MultiParamTypeClasses,
             TypeSynonymInstances,
             FlexibleInstances,
             ScopedTypeVariables,
             ExistentialQuantification,
             RankNTypes,
             ImpredicativeTypes,
             UndecidableInstances
 #-}

-- -XScopedTypeVariables

import qualified Data.Map.Strict as Map
import Control.Monad
import Control.Applicative

import qualified Data.Traversable as T

import System.IO.Unsafe

import Data.SBV
import Data.SBV.Control

-- from this project
import qualified Constraints as C

module Imp where

-- Fix :: (* => *) => *
newtype Fix f = Fix (f (Fix f) (Fix f)) -- deriving Show

-- type Lists = [a]

-- KItem :: (* => *)
data KItemF b a = AVal Integer |
               Var String |
               Plus b b |
               BVal Bool |
               Leq b b |
               And b b |
               Not b |
               Eq b b |
               Eqq String b |
               Assign String b |
               If b a a |
               While b a |
               Seq a a |
               Nil |
               Pgm [String] a deriving (Show,Functor)

{- algebraic defs -}

type KItem = Fix KItemF

type Algebra t a = t a -> a

unFix :: Fix f -> f (Fix f) (Fix f)
unFix (Fix x) = x

cata :: Functor (f (Fix f)) => Algebra (f (Fix f)) a -> Fix f -> a
cata f = f . (fmap (cata f)) . unFix




{-
    We need this signature if we want to ensure that the monadic
    type is parametric. Not immediately useful here
-}

type MAlgebra m f a  = f (m a) -> m a

sumimp = Fix (Pgm ["s","n"] (Fix (Seq (Fix (Assign "n" (Fix (AVal 1000000))))
                          (Fix (While (Fix (Leq (Fix (AVal 0)) (Fix (Var "n"))))
                            (Fix (Seq (Fix (Assign "s" (Fix (Plus (Fix (Var "s")) (Fix (Var "n"))))))
                                 (Fix (Assign "n" (Fix (Plus (Fix (Var "n")) (Fix (AVal (-1)))))))
                            )))))))


salg :: Algebra (KItemF (Fix KItemF)) String 
salg (AVal v) = show v
salg (Var s) = s
salg (Plus s s') = (show s)++" + "++(show s')
salg (BVal b) = show b
salg (Leq s s') = (show s)++ " <= "++(show s')
salg (Not s) = "~("++(show s)++")"
salg (Eq s s') = (show s)++"=="++(show s')
salg (And s s') = (show s)++ " && "++(show s')
salg (Assign s s') = s++" := "++(show s')
salg (If c s' s'') = "if ("++(show c)++") \n {"++s'++"} \n else {"++s''++"}\n"
salg (While c s') = "while ("++(show c)++") {"++s'++"}\n"
salg (Seq s s') = s++";\n"++s'
salg (Pgm l s) = "int "++(foldr (\x acc->x++","++acc) "" l)++";\n"++s
salg Nil = "."

instance Show KItem where
  show = cata salg


---------------------------------------
--- A nice way to write programs
---------------------------------------

int :: Integer -> Integer
int x = x

{-
p = ini [x,y] $ sec [assign x (int 5), 
                 assign y (x `plus` (y `plus` (int 1))), 
                 iff (x `leq` (int 0)) [assign x (int 10)] [assign y (int 10)]]
                  where x = "x"
                        y = "y"
-}
ini :: [String] -> KItem -> KItem
ini l p = Fix $ Pgm l p                        

class Lift a where
  lift :: a -> (Fix KItemF)

instance Lift Integer where
  lift i = Fix $ AVal i

instance Lift String where
  lift s = Fix $ Var s

instance Lift KItem where
  lift x = x

assign :: (Lift a) => String -> a -> KItem
assign v i = Fix $ Assign v (lift i)

plus :: (Lift a, Lift b) => a -> b -> KItem
plus x y = Fix $ Plus (lift x) (lift y)

leq :: (Lift a, Lift b) => a -> b -> KItem
leq x y = Fix $ (Leq (lift x) (lift y))

eqq :: (Lift a, Lift b) => a -> b -> KItem
eqq x y = Fix $ (Eq (lift x) (lift y))

sec :: [KItem] -> KItem
sec [x] = x
sec (x:xs) = Fix $ Seq x (sec xs) 

iff :: KItem -> [KItem] -> [KItem] -> KItem
iff c t e = Fix $ If c (sec t) (sec e)





---------------------------------------
--- Symbolic execution
---------------------------------------




data Var = V String Integer deriving Show
type Val = Integer

-- type SESt = (Map.Map String Integer, [KItem], [Expr])
type SESt = forall a b.(Map.Map String Integer,[KItem])

{-
   - first convert the expression, by adding each apropriate occurrence from the map
   - then combine the constraint(s) to the list of current constraints
-}

bigbang l = (map (++"0") l, [])

-- voidState = ([], [])

{-
    pushc adds the constraint p to the set of constraints on this branch;
    the constraint is converted to the ad-hoc constraint-form and then added
    conversion is achieved using cata 
-}


pushc p = S () $ \(vars,consts) -> [(vars,p:consts)]

{-
    let 
      
        tterm (Var s) = [C.Var (s++(show (vars Map.! s)))] -- var s is converted to s0
        tterm (AVal i) = [C.Val i ]
        tsum (Plus e@(Plus _ _) e'@(Plus _ _)) = (tsum e)++(tsum e')
        tsum (Plus e@(Plus _ _) v) = (tsum e)++(tterm v)
        tsum (Plus v e@(Plus _ _)) = (tterm v)++(tsum e)
        tsum (Plus v v') = (tterm v)++(tterm v')

        --alg :: KItem -> Z3 AST
        --alg (AVal i) = [EVal i]
        --alg (Var s) = snd (mapp Map.! s)
        --alg (Plus x y) = let (e,e') = (convert x, convert y) in mkAdd =<< T.sequence [e,e']
        --alg (Leq x y) = let (e:_,e':_) = (convert x, convert y) in [e :< e']
        --alg (And x y) = convert x ++ convert y
        
        alg (Eqq v y) = (tterm v) `Eq` (tsum y)
        --alg (Not x) = map LNot (convert x)
        
    in [(vars,(alg p):consts)]
-}

{-
    newOcc increments the occurrence counter for variable s
-}


newOcc :: String -> S ()
newOcc s = S () $ \(m,constr) -> 
            let (i,_) = (m Map.! s) 
            in [(Map.insert s (i+1) m, constr)]
                     




data S a = S a (SESt -> [SESt]) deriving Functor
run (S a f) s = f s
{-

-- i don't care how functions work!!!
instance Monad S where
  (S v f1) >>= f = let (S v' f2) = f v
                   in S v' $ \s -> let xs = f1 s 
                                   in foldr (++) [] (map f2 xs)
  -- erase history
  return v = S v (\(m,_,_)->[(m,[],[])])

-- emptyHistory = return ()

instance Applicative S where
  pure x = return x
  (S f _) <*> (S o _) = S (f o) (\s -> [])

instance Alternative S where
  (S x p) <|> (S _ p') = S x (\s -> (p s) ++ (p' s))

-}




-- sealg :: Algebra (KItemF (Fix KItemF)) (S ())
{- 
sealg (Seq p p') = do {p ; p'}
sealg (If c p p') = do {pushc c; p} <|> do {pushc (Fix (Not c)); p'}
sealg (Assign v e) = do {newOcc v; pushc (eqq v e)}
sealg (Pgm l p) = do {bigbang l; p}

symbex = cata sealg
-}

{-
      Z3 stuff - really basic and inefficient



-}
{-
    solve calls the solver on the current state
    it returns the same state if there is a solution,
    otherwise it returns []
-}
{- 
solve :: S ()
solve = S () $ \(m,_,cx) -> 
          let 
              seq (m:mx) = m >>= (seq mx)
              seq [] = 
-}


p = ini [x,y] $ sec [assign x (int 5), 
                  assign y (x `plus` (y `plus` (int 1)))]
                  where x = "x"
                        y = "y"





