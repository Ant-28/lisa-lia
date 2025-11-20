


-- data Nat = Zero | Succ Nat deriving Show



-- plus :: Nat -> Nat -> Nat
-- plus Zero n2 = n2
-- plus n1 Zero = n1
-- plus (Succ n1) n2 = Succ (plus n1 n2)

-- show two arbitrary trees are equal to each other


data RingAst =  Zero 
              | One 
              | Plus RingAst RingAst 
              | Neg RingAst
              | Mult RingAst RingAst
    deriving (Show, Eq)

-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-}

simplify :: RingAst -> RingAst
simplify Zero = Zero -- refl
simplify One = One -- refl
-- simplify (Plus One (Neg One)) = Zero -- add_inv
-- simplify (Plus (Neg One) One) = Zero -- add_inv
simplify (Plus Zero x) = simplify x -- plus zero
simplify (Plus x Zero) = simplify x -- plus zero
simplify (Plus (Plus x y) One) = Plus One (Plus x y)
-- simplify (Plus (Plus x y) (Neg One)) = Plus (Neg One) (Plus x y)
simplify (Plus (Plus x y) z) = simplify (Plus (simplify x) (simplify (Plus y z))) -- you will stop rotating when you hit a base case, I guess
simplify (Plus One a2 ) = Plus One (simplify a2) -- catch 1 + x?
-- simplify (Plus One (Plus (Neg One) y)) = simplify y

-- negation hell
simplify (Neg Zero) = Zero
simplify (Neg One)  = Neg One
simplify (Neg (Neg x)) = simplify x
simplify (Neg (Plus x y)) = simplify (Plus (simplify (Neg x)) (simplify (Neg y)))
simplify (Plus x (Neg y)) = (Plus (simplify x) (simplify (Neg y))) -- simplify makes this an infinite loop
simplify (Plus (Neg x) y) = (Plus (simplify (Neg x)) (simplify y))

simplify (Mult x (Plus a b)) = (Plus (simplify (Mult a x)) (simplify (Mult b x)))
simplify (Mult (Plus a b) x) = (Plus (simplify (Mult a x)) (simplify (Mult b x)))
simplify (Mult x Zero) = Zero
simplify (Mult Zero x) = Zero
simplify (Mult One x) = simplify x
simplify (Mult x One) = simplify x
simplify (Neg (Mult x y)) = Mult (simplify (Neg x)) (simplify y)
simplify ((Mult (Neg x) (Neg y))) = simplify (Mult (simplify x) (simplify y))
simplify x = x
-- simplify (Plus x y)         = (Plus (simplify x) (simplify y))
-- simplify (Plus (Neg x) y) =  Plus (simplify y) (simplify (Neg x))

simploop x = if x == (simplify x) then x else simploop (simplify x)
sn x = simplify (simplify x)

negationRemove :: RingAst -> RingAst
negationRemove (Plus One (Neg One)) = Zero
negationRemove (Plus (Neg One) One) = Zero
negationRemove (Plus One (Plus One x)) = Plus One (negationRemove (Plus (One) x))
negationRemove (Plus (Neg One) (Plus (Neg One) x)) = Plus (Neg One) (negationRemove (Plus (Neg One) x))
negationRemove (Plus (One) (Plus (Neg One) x)) = negationRemove x
negationRemove (Plus (Neg One) (Plus (One) x)) = negationRemove x
negationRemove x = x

negationFixpoint x = if x == negationRemove x then x else negationFixpoint (negationRemove x)

i :: Integer -> RingAst
i 0 = Zero
i x = if x > 0 then Plus One (i (x - 1)) else Neg(i(-x))

