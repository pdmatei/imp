-----------------------------------------------------------------------------
-- This module defines a contraint types to be held during 
-- symbolic execution, as well as appropriate calls to the Z3 solver
-----------------------------------------------------------------------------

module Constraints where

import Data.SBV
import Data.SBV.Control
import qualified Data.Map.Strict as Map
import Control.Monad.Trans.Class

import KItem

{-
data BCtr a b = 
    Leq (ACtr a b) (ACtr a b) | 
    Le (ACtr a b) (ACtr a b) | 
    Ge (ACtr a b) (ACtr a b) | 
    Geq (ACtr a b) (ACtr a b) | 
    Eq (ACtr a b) (ACtr a b)

type ACtr a b = [Atom a b]
data Atom a b = Var a | Val b


convert h b 
        | (Leq le ri) <- b = f le .<= f ri
        | (Le le ri) <- b = f le .< f ri
        | (Geq le ri) <- b = f le .>= f ri
        | (Ge le ri) <- b = f le .> f ri
        | (Eq le ri) <- b = f le .== f ri
            where f l = foldr1 (+) $ map g l
                          where g x = case x of
                                    Var s -> h Map.! s
                                    Val i -> i
-}

--convert :: (Map.Map String t) -> KItem -> SBool
convert h b
        | Fix (Leq le ri) <- b = tsum le .<= tsum ri
        | Fix (Eq le ri) <- b = tsum le .== tsum ri
          where 
                tsum :: KItem -> SInteger
                tsum (Fix (Plus e@(Fix (Plus _ _)) e'@(Fix (Plus _ _)))) = (tsum e) + (tsum e')
                tsum (Fix (Plus e@(Fix (Plus _ _)) v)) = (tsum e) + (tterm v)
                tsum (Fix (Plus v e@(Fix (Plus _ _)))) = (tterm v) + (tsum e)
                tsum (Fix (Plus v v')) = (tterm v) + (tterm v')
                --tterm :: KItem -> SInteger
                tterm (Fix (Var s)) = (h Map.! s) :: SInteger -- var s is converted to s0
                tterm (Fix (AVal i)) = i


{-
Var String |
               Plus b b |
               BVal Bool |
               
-}

{-
-- build the constraints
prepareZ3 vars constraints =
  do
    lx <- sIntegers vars
    let h = Map.fromList $ zipWith (,) vars lx
        f (x:xs) = do constrain $ convert h $ x
                      f xs
        f [] = solve []
      in f constraints
-}


{-
test = prepareZ3 ["x","y","z"] 
        [
          [Var "x", Var "y"] `Eq` [Val 10],
          [Var "x"] `Eq` [Var "y"],
          [Var "x"] `Eq` [Var "z"]
        ] 
-}


satz3 m = do val <- sat m
             case val of 
                SatResult (Satisfiable _ _) -> putStrLn "True"
                _ -> putStrLn "False"

{-								
tee = do 
        val <- sat te
        case val of
            SatResult (Satisfiable _ _) -> putStrLn "True"
            _ -> putStrLn "False"
-}








