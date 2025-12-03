{-# LANGUAGE StrictData #-}
module Test2 where
import Data.Either (isRight)
import Prelude

    -- eval fn that returns a "normal form" (e.g. a right-biased tree)
    -- only restrict oneself to a right-biased tree?
    -- TODO try to measure proof size?

fixpointify f x = if f x == x then x else fixpointify f (f x)

data RingAst =  Zero 
            | One 
            | Plus RingAst RingAst 
            | Neg RingAst
            | Mult RingAst RingAst
    deriving (Show, Eq)

data Sign = P | M deriving Show

newtype RightBiased a = RightBiased a deriving Show

type RbRing = RightBiased RingAst

isRightBiased :: RingAst -> Bool
isRightBiased x = case x of 
    Zero -> True
    One -> True
    (Plus One x) -> irbHelper P x 
    (Plus (Neg One) x) -> irbHelper M x
    _ -> False
    where 
        irbHelper :: Sign -> RingAst -> Bool
        irbHelper P One = True 
        irbHelper M (Neg One) = True
        irbHelper P (Plus One x) = irbHelper P x
        irbHelper M (Plus (Neg One) x) = irbHelper M x
        irbHelper _ _ = False

evalRing :: RingAst -> RbRing
evalRing Zero = RightBiased Zero
evalRing One = RightBiased One
evalRing (Plus a b) = evalPlus (evalRing a) (evalRing b)
evalRing (Neg a)    = evalNeg   (evalRing a)
evalRing (Mult a b) = evalMult  (evalRing a) (evalRing b)


-- rightbiased invariant: either zero, a sequence of ones, or a sequence of -1s
evalPlus :: RbRing -> RbRing -> RbRing
evalPlus (RightBiased Zero) x = x
evalPlus x (RightBiased Zero) = x
-- 1 + x if x is rightbiased
evalPlus (RightBiased One) (RightBiased x) = case x of 
    One    -> RightBiased (Plus One One)
    Neg One -> RightBiased Zero
    Plus One x -> RightBiased (Plus One (Plus One x))
    Plus (Neg One) x -> RightBiased x
    _ -> error "Violates right-biased invariant"
evalPlus (RightBiased x) (RightBiased One) = evalPlus (RightBiased One) (RightBiased x)
-- create helper lemmas for base cases and use RightSubst for inductive cases
evalPlus (RightBiased (Neg One)) (RightBiased x) = case x of 
    -- One -> RightBiased Zero
    Neg One -> RightBiased (Plus (Neg One) (Neg One))
    Plus One x -> RightBiased x
    Plus (Neg One) x -> RightBiased (Plus (Neg One) (Plus (Neg One) x))
    _ -> error "Violates right-biased invariant"
evalPlus (RightBiased x) (RightBiased (Neg One)) = evalPlus (RightBiased (Neg One)) (RightBiased x)
evalPlus (RightBiased (Plus o1 x)) (RightBiased (Plus o2 y)) = case (o1, o2) of 
    (One, Neg One) -> evalPlus (RightBiased x) (RightBiased y)
    (Neg One, One) -> evalPlus (RightBiased x) (RightBiased y)
    (One, One) -> evalPlus (RightBiased x) (RightBiased (Plus One (Plus One y)))
    (Neg One, Neg One) -> evalPlus (RightBiased x) (RightBiased (Plus (Neg One) (Plus (Neg One) y)))
    _ -> error "Violates right-biased invariant"
evalPlus _ _ = error "Violates right-biased invariant"

evalNeg :: RbRing -> RbRing
evalNeg (RightBiased Zero) = RightBiased Zero
evalNeg (RightBiased One) = RightBiased (Neg One)
evalNeg (RightBiased (Plus a b)) = case a of 
            One -> RightBiased (evalNegHelper P (Plus a b))
            Neg One -> RightBiased (evalNegHelper M (Plus a b))
            _ -> error "Violates right-biased invariant"
    where 
        evalNegHelper :: Sign -> RingAst -> RingAst
        evalNegHelper P One = Neg One
        evalNegHelper P (Plus One x) = Plus (Neg One) (evalNegHelper P x)
        evalNegHelper M (Neg One) = One
        evalNegHelper M (Plus (Neg One) x) = Plus One (evalNegHelper M x)
        evalNegHelper _ _ = error "Violates right-biased invariant"
evalNeg _ = error "Violates right-biased invariant"
          
evalMult :: RbRing -> RbRing -> RbRing
evalMult (RightBiased Zero) x = RightBiased Zero
evalMult x (RightBiased Zero) = RightBiased Zero
evalMult (RightBiased One) x  = x
evalMult x (RightBiased One)  = x
evalMult (RightBiased (Neg One)) x = evalNeg x
evalMult x (RightBiased (Neg One)) = evalNeg x
evalMult (RightBiased (Plus a b)) c = evalPlus (evalMult (RightBiased a) c) (evalMult (RightBiased b) c)
evalMult _ _ = error "Violates right-biased invariant"


-- evalRing :: RingAst -> RingAst
-- evalRing i @ (RightBiased x) = i
-- evalRing Zero =  RightBiased Zero
-- evalRing One =   RightBiased (Plus One Zero)

-- some addition on rightBiased rings
-- e.g. a helper function
-- "call by name" -- functions that only need to deal with "normalized trees"
-- check if I'm triggering bugs in lisa

-- evalRing (Plus a b) = (evalRing a) + (evalRing b)
-- evalRing (Neg a)    = -(evalInt a)
-- evalRing (Mult a b) = (evalInt a) * (evalInt b)

evalInt :: RingAst -> Integer
evalInt Zero = 0
evalInt One = 1
evalInt (Plus a b) = (evalInt a) + (evalInt b)
evalInt (Neg a)    = -(evalInt a)
evalInt (Mult a b) = (evalInt a) * (evalInt b)

-- isRightBiased 

-- only remove zeros

removeZeros Zero = Zero
removeZeros One = One
removeZeros (Plus x Zero) = removeZeros x
removeZeros (Plus Zero x) = removeZeros x
removeZeros (Plus x y) = Plus (removeZeros x) (removeZeros y) 
removeZeros (Neg x) = Neg (removeZeros x)
removeZeros (Mult x y) = Mult (removeZeros x) (removeZeros y) 

-- right bias a tree
rightBias :: RingAst -> RingAst
rightBias (Plus (Plus x y) z) = rightBias (Plus  (rightBias x) (Plus(rightBias y) (rightBias z)))
rightBias (Plus x z) = Plus (rightBias x) (rightBias z) -- x should be One, Zero or Neg One here
rightBias x = x

-- eliminate negations
negElim (Neg Zero) = Zero
negElim (Neg (Neg x)) = negElim x
negElim (Neg (Plus x y)) = Plus (negElim (Neg x)) (negElim (Neg y))
negElim (Neg (Mult x y)) =  Mult (negElim (Neg x)) (negElim y)
negElim (Mult (Neg x) (Neg y)) = negElim (Mult x y)
negElim (Plus x y) = Plus (negElim x) (negElim y)
negElim (Mult x y) = Mult (negElim x) (negElim y)

negElim x = x

-- x + 1 - 1 in any order is 0
cancellation (Plus (Neg One) One) = Zero
cancellation (Plus One (Neg One)) = Zero
cancellation (Plus x (Plus y z)) = case (x, y, z) of 
    (One, Neg One, z) -> cancellation z
    (One, y, Neg One) -> cancellation y
    (Neg One, One, z) -> cancellation z
    (Neg One, y, One) -> cancellation y
    (x, One, Neg One) -> cancellation x
    (x, Neg One, One) -> cancellation x
    (x, y, z) -> Plus (cancellation x) (cancellation (Plus y z))
cancellation x = x

pushDownMult :: RingAst -> RingAst
pushDownMult (Mult x Zero) = Zero 
pushDownMult (Mult Zero x) = Zero
pushDownMult (Mult x One) = pushDownMult x
pushDownMult (Mult One x) = pushDownMult x 
pushDownMult (Mult x (Plus y z)) = Plus (pushDownMult (Mult x y)) (pushDownMult (Mult x z))
pushDownMult (Mult (Plus y z) x) = Plus (pushDownMult (Mult x y)) (pushDownMult (Mult x z))
pushDownMult (Plus x y) = Plus (pushDownMult x) (pushDownMult y)
pushDownMult (Mult x y) = Mult (pushDownMult x) (pushDownMult y)
pushDownMult (Neg x) = Neg (pushDownMult x)
pushDownMult x = x

allFns = pushDownMult . cancellation. negElim . rightBias. removeZeros

ultimateOpt = fixpointify allFns

i :: Integer -> RingAst
i 0 = Zero
i x = if x > 0 then Plus One (i (x - 1)) else Neg(i(-x))
