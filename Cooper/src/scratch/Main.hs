module Main (main) where
import Prelude
import GHC.IO (unsafePerformIO)
import System.Random
import Data.Char (chr)
import Control.Monad
-- {-# LANGUAGE FlexibleContexts #-}
data RingAst =  Zero
            | One
            | Plus RingAst RingAst
            | Neg RingAst
            | Mult RingAst RingAst
            | Var String -- -- don't 
    deriving (Show, Eq)

prettyPrint :: RingAst -> String
prettyPrint Zero = "0"
prettyPrint One = "1"
prettyPrint (Plus a b) = "(" ++ prettyPrint a ++ " + " ++ prettyPrint b ++ ")"
prettyPrint (Mult a b) = "(" ++ prettyPrint a ++ " * " ++ prettyPrint b ++ ")"
prettyPrint (Neg a) = "-(" ++ prettyPrint a ++ ")"
prettyPrint (Var x) = x

getVars :: RingAst -> String 
getVars (Var x) = x
getVars (Neg (Var x)) = x 
getVars _ = error "called with invalid input"
data Sign = P | M deriving Show

newtype RB a = RB a deriving Show

type RbRing = RB RingAst

isRB :: RingAst -> Bool
isRB x = case x of
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

isVarOrNegation :: RingAst -> Bool
isVarOrNegation (Var x) = True
isVarOrNegation (Neg (Var x)) = True
isVarOrNegation _  = False

isOne x = x == One
isNegOne x = x == Neg One
isOneOrNegOne x = isOne x || isNegOne x
isZero x = x == Zero
isVar (Var x) = True
isVar _ = False
isNegVar (Neg (Var x)) = True
isNegVar _ = False

evalRing :: RingAst -> RbRing
evalRing Zero = RB Zero
evalRing One = RB One
evalRing (Var x) = RB (Var x)
evalRing (Plus a b) = evalPlus (evalRing a) (evalRing b)
evalRing (Neg a)    = evalNeg   (evalRing a)
evalRing (Mult a b) = evalMult  (evalRing a) (evalRing b)


-- key invariants: right-biasing and sorting
-- should evaluation handle both? 
evalPlus :: RbRing -> RbRing -> RbRing
evalPlus (RB Zero) x = x
evalPlus x (RB Zero) = x
-- incrs
evalPlus (RB One) (RB x) = evalIncr (RB x)
evalPlus (RB x) (RB One) = evalPlus (RB One) (RB x)
-- decrs
evalPlus (RB (Neg One)) (RB x) = evalDecr (RB x)
evalPlus (RB x) (RB (Neg One)) = evalPlus (RB (Neg One)) (RB x)
-- vars
evalPlus (RB x) (RB y) | isVarOrNegation x = evalInsert x y
evalPlus (RB x) (RB y) | isVarOrNegation y = evalInsert y x
-- evalPlus (RB y) (RB (Var x)) = evalInsert (Var x) y
-- evalPlus (RB (Neg (Var x))) (RB y) = evalInsert (Var x) y
-- evalPlus (RB y) (RB (Neg (Var x))) = evalInsert (Var x) y
-- recursive cases
evalPlus (RB (Plus x xs))  (RB (Plus y ys)) = case (x, y) of
    -- 1 + x
    (One, Neg One) -> evalPlus (RB xs) (RB ys)
    (Neg One, One) -> evalPlus (RB xs) (RB ys)


    (x, y) | isOneOrNegOne x -> evalPlus (RB xs) (RB (Plus x (Plus y ys)))
    (x, y) | isVarOrNegation x -> evalPlus (RB xs) (evalInsert x (Plus y ys))

    -- (One, s@One) -> evalPlus (RB xs) (RB (Plus One (Plus s ys)))
    -- (One, s@(Var z)) -> evalPlus (RB xs) (RB (Plus One (Plus s ys)))
    -- (One, s@(Neg(Var z))) -> evalPlus (RB xs) (RB (Plus One (Plus s ys)))
    -- (Neg One, Neg One) -> evalPlus (RB xs) (RB (Plus (Neg One) (Plus (Neg One) ys)))
    -- (Neg One, Var z) -> evalPlus (RB xs) (RB (Plus (Neg One) (Plus (Var z) ys)))
    -- (Neg One, s@(Neg(Var z))) -> evalPlus (RB xs) (RB (Plus (Neg One) (Plus s ys)))

    -- -1 + x
    -- 
    -- (Var z, Neg One) -> evalPlus (RB xs) (evalInsert (Var z) (Plus y ys))
    -- (Var z, Var a) -> evalPlus (RB xs) (evalInsert (Var z) (Plus y ys))
    -- (Var z, Neg (Var a)) -> evalPlus (RB xs) (evalInsert (Var z) (Plus y ys))

    -- (Neg (Var z), One) -> evalPlus (RB xs) (evalInsert (Neg (Var z)) (Plus y ys))
    -- (Neg (Var z), Neg One) -> evalPlus (RB xs) (evalInsert (Neg (Var z)) (Plus y ys))
    -- (Neg (Var z), Var a) -> evalPlus (RB xs) (evalInsert (Neg (Var z)) (Plus y ys))
    -- (Neg (Var z), Neg (Var a)) -> evalPlus (RB xs) (evalInsert (Neg (Var z)) (Plus y ys))
evalPlus _ _ = error "Violated right-biased invariant"




u :: RbRing -> RingAst
u (RB x) = x


-- var or nvar : ringast -> Bool
evalInsert :: RingAst -> RingAst -> RbRing
evalInsert (Var z) Zero = RB (Var z)
evalInsert x y | isVarOrNegation x && isOneOrNegOne y = RB (Plus y x)
evalInsert x y | all isVar [x, y] || all isNegVar [x, y] =     
    let z = getVars x in 
    let a = getVars y in    
    if z < a then RB (Plus x y) else RB (Plus y x)
-- evalInsert (Var z) One  = RB (Plus One (Var z))
-- evalInsert (Var z) (Neg One)  = RB (Plus (Neg One) (Var z))
-- evalInsert (Neg (Var z)) Zero = RB (Var z)
-- evalInsert (Neg (Var z)) (Neg One)  = RB (Plus (Neg One) (Var z))
evalInsert x y | isVar x && isNegVar y = 
    let z = getVars x in
    let a = getVars y in 
    case (z, a) of
    (z, a) |  z == a -> RB Zero
    (z, a) |  z < a  -> RB (Plus x y)
    (z, a) -> RB (Plus y x)
evalInsert x@(Neg (Var z)) y@(Var a) = evalInsert y x
evalInsert x (Plus y ys) | isVarOrNegation x && isOneOrNegOne y = RB (Plus y (u (evalInsert x ys)))
evalInsert x (Plus y ys)  | all isVar [x, y] || all isNegVar [x, y] = 
    let z = getVars x in 
    let a = getVars y in    
    if z < a
    then RB (Plus x y)
    else RB (Plus y (u (evalInsert x ys)))
evalInsert x (Plus y ys) | (isVar x && isNegVar y) ||(isNegVar x && isVar y) = 
    let z = getVars x in
    let a = getVars y in 
    case (z, a) of 
    (z, a) | z == a    -> RB ys
    (z, a) | z < a     -> RB (Plus x (Plus y ys))
    (z, a)             -> RB (Plus y (u (evalInsert x ys)))
-- evalInsert x@(Neg (Var z)) y@(Neg (Var a)) = if z < a then RB (Plus x y) else RB (Plus y x)
-- evalInsert x@(Var z) y@(Plus av@One ys) = RB (Plus av (u (evalInsert x ys)))
-- evalInsert x@(Var z) y@(Plus av@(Neg One) ys) = RB (Plus av (u (evalInsert x ys)))
-- evalInsert x@(Neg (Var z)) y@(Plus av@One ys) = RB (Plus av (u (evalInsert x ys)))
-- evalInsert x@(Neg (Var z)) y@(Plus av@(Neg One) ys) = RB (Plus av (u (evalInsert x ys)))
-- evalInsert x@(Neg (Var z)) y@(Plus av@(Var a) ys)
--     | z == a    = RB ys
--     | z < a     = RB (Plus x Plus())
--     | otherwise = RB (Plus av (u (evalInsert x ys)))
-- evalInsert x@(Neg (Var z)) y@(Plus av@(Neg (Var a)) ys) = if z < a
--     then RB (Plus x y)
--     else RB (Plus av (u (evalInsert x ys)))


evalInsert _ _ = error "invariant violation"






evalIncr :: RbRing -> RbRing
evalIncr (RB x) = case x of
    One -> RB (Plus One One)
    (Neg One) -> RB Zero
    (Plus (Neg One) xs) -> RB xs
    x -> RB (Plus One x)
    -- (Plus One xs) -> RB (Plus One (Plus One xs))
    -- Var xs -> RB (Plus One (Var xs))
    -- (Neg (Var xs)) -> RB (Plus One (Neg (Var xs)))
    -- a@(Plus _ _) -> RB (Plus One a)
    -- _ -> error "violates right-biased invariant"

evalDecr :: RbRing -> RbRing
evalDecr (RB x) = case x of
    One -> RB Zero
    (Plus One xs) -> RB xs
    x -> RB (Plus (Neg One) x)
    -- (Neg One) -> RB (Plus (Neg One) (Neg One))
    -- Var xs -> RB (Plus (Neg One) (Var xs))
    -- (Neg (Var xs)) -> RB (Plus (Neg One) (Neg (Var xs)))
    -- (Plus (Neg One) xs) -> RB (Plus (Neg One) (Plus (Neg One) xs))
    -- a@(Plus _ _) -> RB (Plus (Neg One) a)
    -- _ -> error "violates right-biased invariant"

-- "-((((p * 1) + -(t)) + -(-(1))))"

evalNeg :: RbRing -> RbRing
evalNeg (RB Zero) = RB Zero
evalNeg (RB One) = RB (Neg One)
evalNeg (RB (Neg One)) = RB One
evalNeg (RB (Var x)) = RB (Neg (Var x))
evalNeg (RB (Neg (Var x))) = RB (Var x)
evalNeg (RB (Plus a b)) = case a of
            One -> RB (evalNegHelper P (Plus a b))
            Neg One -> RB (evalNegHelper M (Plus a b))
            x | isVarOrNegation x -> RB (evalNegHelper P (Plus a b))
            --  -> RB (evalNegHelper P (Plus a b))
            _ -> error "Violates right-biased invariant"
    where
        evalNegHelper :: Sign -> RingAst -> RingAst
        evalNegHelper _ (Var x) = Neg (Var x)
        evalNegHelper _ (Neg (Var x)) = Var x
        evalNegHelper _ (Plus (Var x) xs) = Plus (Neg (Var x)) (evalNegHelper P xs)
        evalNegHelper _ (Plus (Neg (Var x)) xs) = Plus (Var x) (evalNegHelper P xs)
        evalNegHelper P One = Neg One
        evalNegHelper P (Plus One x) = Plus (Neg One) (evalNegHelper P x)
        evalNegHelper M (Neg One) = One
        evalNegHelper M (Plus (Neg One) x) = Plus One (evalNegHelper M x)
        evalNegHelper _ _ = error "Violates right-biased invariant"
evalNeg _ = error "Violates right-biased invariant"

evalMult :: RbRing -> RbRing -> RbRing
evalMult (RB Zero) x = RB Zero
evalMult x (RB Zero) = RB Zero
evalMult (RB One) x  = x
evalMult x (RB One)  = x
evalMult (RB (Neg One)) x = evalNeg x
evalMult x (RB (Neg One)) = evalNeg x
-- evalMult (RB (Var x)) (RB (Var y))  = RB (Mult (Var x) (Var y))
-- evalMult (RB (Neg (Var x))) (RB (Var y)) = RB (Mult (Neg (Var x)) (Var y))
-- evalMult (RB (Var x)) (RB (Neg (Var y))) = RB (Mult (Neg (Var x)) (Var y))
-- evalMult (RB (Neg (Var x))) (RB (Neg (Var y))) = RB (Mult (Var x) (Var y))
evalMult (RB (Plus a b)) c = evalPlus (evalMult (RB a) c) (evalMult (RB b) c)
evalMult _ _ = error "Violates right-biased invariant"

-- make a random expression


build :: Int -> RingAst
build n = buildHelper n True
    where
        buildHelper :: Int -> Bool -> RingAst
        buildHelper 0 t
            | r <  3 = Zero
            | r <= 6 = One
            | r <= 10 = if t then Var [chr r2] else if r < 5 then Zero else One
            where
            r = rand 10
            r2 = rand 26 + 97
        buildHelper n t
            | r < 3   = Plus (buildHelper (n - 1) t) (buildHelper (n - 1) t)
            | r <= 6  = Neg (buildHelper (n - 1) t)
            | r <= 10 = if t then Mult (buildHelper (n - 1) False) (buildHelper (n - 1) True) else
                        Mult (buildHelper (n - 1) t) (buildHelper (n - 1) t)
            where r = rand 10

i :: Int -> RingAst
i 0 = Zero
i x
    | x > 0 = Plus One (i (x - 1))
    | x < 0 = Plus (Neg One) (i (x + 1))

buildExpr :: Int -> [RingAst]
buildExpr 0 = [i (rand 10)]
buildExpr n
    | n < 0 = error "don't call me with negative ints kthx"
    | n > 0 = Mult (i ((-10) + rand 20)) randVar  : buildExpr (n - 1)
    where
        randVar :: RingAst
        randVar  = Var [chr (97 + rand 26)]
buildExprFinal :: [RingAst] -> RingAst
buildExprFinal = foldl Plus Zero
build2 = buildExprFinal . buildExpr


rand :: Int -> Int
rand n = unsafePerformIO $ do
    v <- randomIO
    return (v `mod` n)

-- -((((p * 1) + -(t)) + -(-(1))))"

getFreeVars :: RingAst -> [String]
getFreeVars (Var x) = [x]
getFreeVars (Plus a b) = getFreeVars a ++ getFreeVars b
getFreeVars (Mult a b) = getFreeVars a ++ getFreeVars b
getFreeVars (Neg a) = getFreeVars a
getFreeVars _ = []

gfv :: [String] -> String
gfv = foldl (\ x y -> x ++ " " ++ y) ""

foo :: IO ()
foo = do
    let x = build2 7
    print ("syms " ++ gfv (getFreeVars x))
    print x
    print (prettyPrint x)
    print (evalRing x)
main :: IO ()
main = do
    -- how does this work
    -- TODO: read lipovača
    -- forM_ [1..2000] $ const foo
    foo






-- (-(-((o + z))) + (-((a + w)) * -((1 + y))))

unl :: RingAst -> RingAst
unr :: RingAst -> RingAst
unl (Plus a b) = a
unl (Neg a) = a
unl (Mult a b) = a
unl x = x

unr (Plus a b) = b
unr (Neg a) = a
unr (Mult a b) = b
unr x = x


testval :: RingAst = Plus
        (Plus (Neg (Neg (Neg Zero)))
        (Mult
            (Mult (Mult Zero One) (Neg One))
            (Plus (Mult Zero One) (Mult Zero Zero))))
        (Neg (Plus (Plus (Neg (Var "a")) (Neg (Var "z"))) (Neg (Neg (Var "b")))))

testval2 = Neg (Neg (Neg (Plus (Plus (Neg (Neg (Plus (Plus (Mult One Zero) (Neg One)) (Plus (Plus Zero One) (Mult One Zero))))) (Mult (Mult (Neg (Plus (Neg One) (Plus One One))) (Neg (Neg (Mult One One)))) (Mult (Neg (Plus (Mult One One) (Mult Zero Zero))) (Plus (Plus (Mult One One) (Mult Zero Zero)) (Plus (Neg (Var "g")) (Neg One)))))) (Plus (Plus (Mult (Neg (Plus (Neg One) (Plus One Zero))) (Mult (Plus (Neg One) (Plus One One)) (Mult (Plus Zero One) (Neg One)))) (Neg (Neg (Mult (Plus One One) (Plus (Var "x") Zero))))) (Plus (Neg (Mult (Mult (Neg One) (Plus One One)) (Mult (Neg One) (Plus One (Var "g"))))) (Mult (Plus (Neg (Neg Zero)) (Neg (Mult One Zero))) (Mult (Mult (Neg Zero) (Plus One One)) (Neg (Plus (Var "d") Zero)))))))))