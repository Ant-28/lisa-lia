# Linear Integer Arithmetic in LISA

This implements the following tactics in LISA:

- `evalRingEq` $x \equiv y$ 
- `disEquality`  $x \not\equiv y$  
- `inEquality`   $x < y, x \le y$
- `divInts`   $x \mid y$
- `inDivInts`   $x \not \mid y$
- `liaByWitness`  Conjuncts and Disjuncts in NNF, provided a list of witnesses

- `Cooper/src` contains the main code
- `progress` contains progress proofs for the term rewrite system (WIP) in Stainless
- `Cooper/src/scratch` is a draft of the TRS in Haskell


To run the proofs, call `make`. 

If you run out of memory due to LSPs, call `make cleanlsp`.


`