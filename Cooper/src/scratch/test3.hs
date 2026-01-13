module Main where
import Prelude

data RingAst =  Zero 
            | One 
            | Plus RingAst RingAst 
            | Neg RingAst
            | Mult RingAst RingAst
            | Var String -- -- don't 
    deriving (Show, Eq)

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
evalPlus (RB (Var x)) (RB y) = evalInsert (Var x) y
evalPlus (RB y) (RB (Var x)) = evalInsert (Var x) y
-- recursive cases
evalPlus (RB (Plus x xs))  (RB (Plus y ys)) = case (x, y) of
    -- 1 + x
    (One, Neg One) -> evalPlus (RB xs) (RB ys)
    (One, s@One) -> evalPlus (RB xs) (RB (Plus One (Plus s ys)))
    (One, s@(Var z)) -> evalPlus (RB xs) (RB (Plus One (Plus s ys)))
    (One, s@(Neg(Var z))) -> evalPlus (RB xs) (RB (Plus One (Plus s ys)))
    
    -- -1 + x
    (Neg One, One) -> evalPlus (RB xs) (RB ys)
    (Neg One, Neg One) -> evalPlus (RB xs) (RB (Plus (Neg One) (Plus (Neg One) ys)))
    (Neg One, Var z) -> evalPlus (RB xs) (RB (Plus (Neg One) (Plus (Var z) ys)))
    (Neg One, s@(Neg(Var z))) -> evalPlus (RB xs) (RB (Plus (Neg One) (Plus s ys)))
    -- 
    (Var z, One) -> evalPlus (RB (Plus y ys)) (RB (Plus x xs)) 
    (Var z, Neg One) -> evalPlus (RB (Plus y ys)) (RB (Plus x xs)) 
    (Var z, Var a) -> evalPlus (RB xs) (evalInsert (Var z) (Plus y ys))
    (Var z, Neg (Var a)) -> evalPlus (RB xs) (evalInsert (Var z) (Plus y ys))

    (Neg (Var z), One) -> evalPlus (RB (Plus y ys)) (RB (Plus x xs)) 
    (Neg (Var z), Neg One) -> evalPlus (RB (Plus y ys)) (RB (Plus x xs)) 
    (Neg (Var z), Var a) -> evalPlus (RB xs) (evalInsert (Neg (Var z)) (Plus y ys))
    (Neg (Var z), Neg (Var a)) -> evalPlus (RB xs) (evalInsert (Neg (Var z)) (Plus y ys))
evalPlus _ _ = error "Violated right-biased invariant"




u :: RbRing -> RingAst
u (RB x) = x


-- var or nvar : ringast -> Bool
evalInsert :: RingAst -> RingAst -> RbRing
evalInsert x@(Var z) y@(Var a) = if z < a then RB (Plus x y) else RB (Plus y x)
evalInsert x@(Var z) y@(Neg (Var a)) = if z < a then RB (Plus x y) else RB (Plus y x)
evalInsert x@(Neg (Var z)) y@(Var a) = if z < a then RB (Plus x y) else RB (Plus y x)
evalInsert x@(Neg (Var z)) y@(Neg (Var a)) = if z < a then RB (Plus x y) else RB (Plus y x)
evalInsert x@(Var z) y@(Plus av@One ys) = RB (Plus av (u (evalInsert x ys)))
evalInsert x@(Var z) y@(Plus av@(Neg One) ys) = RB (Plus av (u (evalInsert x ys)))
evalInsert x@(Neg (Var z)) y@(Plus av@One ys) = RB (Plus av (u (evalInsert x ys)))
evalInsert x@(Neg (Var z)) y@(Plus av@(Neg One) ys) = RB (Plus av (u (evalInsert x ys)))

evalInsert x@(Var z) y@(Plus av@(Var a) ys) = if z < a 
    then RB (Plus x y) 
    else RB (Plus av (u (evalInsert x ys)))
evalInsert x@(Var z) y@(Plus (Neg (Var a)) ys) = if z < a 
    then RB (Plus x y) 
    else RB (Plus x (u (evalInsert x ys)))
evalInsert x@(Neg (Var z)) y@(Plus (Var a) ys) = if z < a 
    then RB (Plus x y) 
    else RB (Plus x (u (evalInsert x ys)))
evalInsert x@(Neg (Var z)) y@(Plus (Neg (Var a)) ys) = if z < a 
    then RB (Plus x y) 
    else RB (Plus x (u (evalInsert x ys)))
    

evalInsert _ _ = error "invariant violation"
    
    




evalIncr :: RbRing -> RbRing 
evalIncr (RB x) = case x of
    One -> RB (Plus One One)
    (Neg One) -> RB Zero
    (Plus One xs) -> RB (Plus One (Plus One xs))
    (Plus (Neg One) xs) -> RB xs
    Var xs -> RB (Plus One (Var xs))
    _ -> error "violates right-biased invariant"

evalDecr :: RbRing -> RbRing 
evalDecr (RB x) = case x of
    One -> RB Zero
    (Neg One) -> RB (Plus (Neg One) (Neg One))
    Var xs -> RB (Plus (Neg One) (Var xs))
    (Plus One xs) -> RB xs
    (Plus (Neg One) xs) -> RB (Plus (Neg One) (Plus (Neg One) xs))
    _ -> error "violates right-biased invariant"


evalNeg :: RbRing -> RbRing
evalNeg (RB Zero) = RB Zero
evalNeg (RB One) = RB (Neg One)
evalNeg (RB (Neg One)) = RB One
evalNeg (RB (Var x)) = RB (Neg (Var x))
evalNeg (RB (Neg (Var x))) = RB (Var x)
evalNeg (RB (Plus a b)) = case a of 
            One -> RB (evalNegHelper P (Plus a b))
            Neg One -> RB (evalNegHelper M (Plus a b))
            Var x -> RB (evalNegHelper P (Plus a b))
            _ -> error "Violates right-biased invariant"
    where 
        evalNegHelper :: Sign -> RingAst -> RingAst
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
evalMult (RB (Plus a b)) c = evalPlus (evalMult (RB a) c) (evalMult (RB b) c)
evalMult _ _ = error "Violates right-biased invariant"

main :: IO ()
main = print (evalPlus (RB (Plus One (Var "x"))) (RB (Plus One (Var "y")))) 