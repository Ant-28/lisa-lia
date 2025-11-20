module Test2 where
    data RingAst =  Zero 
                | One 
                | Plus RingAst RingAst 
                | Neg RingAst
                | Mult RingAst RingAst
        deriving (Show, Eq)


    fixpointify f x = if f x == x then x else fixpointify f (f x)


    -- only remove zeros
    removeZeros Zero = Zero
    removeZeros One = One
    removeZeros (Plus x Zero) = removeZeros x
    removeZeros (Plus Zero x) = removeZeros x
    removeZeros (Plus x y) = Plus (removeZeros x) (removeZeros y) 
    removeZeros (Neg x) = Neg (removeZeros x)
    removeZeros (Mult x y) = Mult (removeZeros x) (removeZeros y) 

    -- right bias a tree
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
