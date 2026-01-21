// import scala.collection.immutable.{Set => SSet}
// import scala.collection.immutable.{List => LList, :: => Cons}
// import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, P => _, | => _, given, _}
// import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
// import lisa.maths.SetTheory.Base.Pair.{pair, given}
// import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
// import lisa.automation.Substitution.Apply as Substitution
// import Base.{IBinFun, IUnFun, IRel, infixBinaryFunction, infixUnaryFunction}
// import lisa.utils.prooflib.ProofTacticLib.ProofTactic
// import lisa.utils.prooflib.Library

// import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}

// // object RingEqReasoning extends lisa.Main
// trait RingEqReasoning { self: Rings.type =>
//   import self.*
//   // import RingStructure.{*}

//   sealed trait Biased
//   case class RB(x: Expr[Ind]) extends Biased
//   case class NRB(x: Expr[Ind]) extends Biased

//   def unapply(x: Biased): Expr[Ind] = {
//     x match
//       case RB(xs)  => xs
//       case NRB(xs) => xs
//   }

//   object evalRingEq extends ProofTactic:
//     // FIXME: Try to use collect
    

//     def apply(using proof: library.Proof)(
//         goal: Sequent
//     ): proof.ProofTacticJudgement = {
//       if (goal.right.size != 1) then
//         proof.InvalidProofTactic("I can't prove more than one sequent!")
//       else
//         val goalElem = goal.right.toList(0)
//         TacticSubproof:
//           assume(ring(R, <=, +, *, -, |, `0`, `1`))
//           if (!is_eq(goalElem)) then
//             proof.InvalidProofTactic(
//               "I can't prove anything other than equality!"
//             )
//           else
//             val sol = simplify(goalElem)

//             // println(have(sol).bot)
//             if !sol.isValid then
//               proof.InvalidProofTactic("Checking sums failed!")
//             else
//               val typing =
//                 typeChecking(getTypingVarsInAnte(have(sol).bot.left))
//               val seqs = typing + have(sol)
//               // 
//               // have(goal) by Congruence.from(seqs.toSeq*)
//               have(goal) by Tautology.from(seqs.toSeq*)

//     }

//     // allFns = pushDownMult . cancellation. negElim . rightBias. removeZeros
//     // fixpointify f x = if f x == x then x else fixpointify f (f x)
//     // need to check for any invalidProoftactic when returning fixpointified
//     // ultimateOpt = fixpointify allFns
//     /** returns canonical form of ex, as i(n) for some n ∈ ℕ
//       *
//       * and a proof that ring(...), ex ∈ R, i(n) ∈ R |- ex === i(n)
//       *
//       * @param ex
//       * @example
//       */

//     /*
//       evalRing
//       prove that some integer expression is equivalent to its canonical form

//       evalRing :: RingAst -> RbRing
//       evalRing One = RightBiased One
//       evalRing (Plus a b) = evalPlus (evalRing a) (evalRing b)
//       evalRing (Neg a)    = evalNeg   (evalRing a)
//       evalRing (Mult a b) = evalMult  (evalRing a) (evalRing b)

//      */
//     // TODO: write TacticSubproofWithResult s.t. it doesn't need a mutable variable
//     def isRightBiased(x: Expr[Ind]): Boolean = {
//       def irbHelper(x: Expr[Ind], s: Sign): Boolean = {
//         (x, s) match {
//           case (`0`, _) => false
//           case (`1`, P) => true
//           case (-(`1`), M) => true
//           case (`1` + xs, P) => irbHelper(xs, P)
//           case (-(`1`) + xs, M) => irbHelper(xs, M)
//           case _ => false
//         }
//       }
//       x match {
//         case `0` => true
//         case `1` => true
//         case -(`1`) => true
//         case `1` + xs => irbHelper(x, P)
//         case (-(`1`) + xs) => irbHelper(x, M)
//         case _ => false
 
//       }
//     }
//     def evalRing(using proof: library.Proof)(
//         int: Expr[Ind]
//     ): (Biased, proof.ProofTacticJudgement) = {
//       assume(ring(R, <=, +, *, -, |, `0`, `1`))
//       println(int)
//       println(isRightBiased(int))
//       var res: Biased = NRB(`0`)
//       TacticSubproofWithResult[Biased] {
//         int match {
//           // evalRing Zero = RightBiased Zero
//           case `0` => {
//             // proof
//             have(`0` ∈ R |- `0` === `0`) by Tautology
//             // result
//             res = RB(`0`)
//           }
//           // evalRing One = RightBiased One
//           case `1` => {
//             // proof
//             have(`1` ∈ R |- `1` === `1`) by Tautology
//             // result
//             res = RB(`1`)
//           }
//           case _ if isRightBiased(int) => {
//             have(int ∈ R |- int === int) by Restate
//             res = RB(int)
//           }
//           // evalRing (Plus a b) = evalPlus (evalRing a) (evalRing b)
//           case x + y => {
//             val (lr, lp) = evalRing(x)
//             val (rr, rp) = evalRing(y)
//             println("FAHH")
//             println(lr)
//             println(rr)
//             val (sum, proof) = evalPlus(lr, rr)
//             println("FAHH 2")
//             val lru = unapply(lr)
//             val rru = unapply(rr)
//             val sumu = unapply(sum)

//             val eqs = SSet(have(proof).bot, have(lp).bot, have(rp).bot).map(x =>
//               x.firstElemR
//             )
//             have(eqs |- x + y === x + y) by Restate // should be rightsubsteq
//             thenHave(eqs |- x + y === lru + rru) by RightSubstEq.withParameters(
//               Seq((x, lru), (y, rru)),
//               (Seq(a, b), x + y === a + b)
//             )
//             val step = thenHave(eqs |- x + y === sumu) by RightSubstEq.withParameters(
//               Seq((lru + rru, sumu)),
//               (Seq(a), x + y === a)
//             )
//             // println("left and right proofs")
//             // println(have(lp).bot)
//             // println(have(rp).bot)
//             // println(have(proof).bot)
//             // println(x)
//             // println(y)
//             // println(sumu)
//             val typings = SSet(x ∈ R, y ∈ R) ++ getTypings(have(lp).bot.left) ++ getTypings(have(rp).bot.left) ++ getTypings(have(proof).bot.left)
//             // println(typings |- x + y === sumu)
//             have(typings |- x + y === sumu) by Tautology.from(
//               step,
//               have(lp),
//               have(rp),
//               have(proof)
//             )
//             res = sum
//             println("FAHH3")
//           }
//         }
//       }(res)
//     }

//     // for the love of god ant, don't name your parameters the same as your axiom variables
//     def evalPlus(using
//         lib: library.type,
//         proof: lib.Proof
//     )(ex: Biased, ey: Biased): (Biased, proof.ProofTacticJudgement) = {
//       assume(ring(R, <=, +, *, -, |, `0`, `1`))
//       var res: Biased = NRB(
//         `0`
//       ) // easier to throw an invalid proof state if res is invalid
//       TacticSubproofWithResult[Biased] {
//         (ex, ey) match {
//           // evalPlus (RightBiased Zero) x = x
//           case (RB(`0`), RB(ys)) => {
//             // val newstmt = ((`0` ∈ R, y ∈ R) |- ((`0` + y) === y))
//             have((`0` ∈ R, ys ∈ R) |- ((`0` + ys) === ys)) by Tautology.from(
//               zero_x_x of (x := ys)
//             ) // value := is not a member of Rings.Biased
//             res = RB(ys)
//           }
//           // evalPlus x (RightBiased Zero) = x
//           case (RB(xs), RB(`0`)) => {
//             have((`0` ∈ R, xs ∈ R) |- ((xs + `0`) === xs)) by Tautology.from(
//               x_zero_x of (x := xs)
//             ) // value := is not a member of Rings.Biased
//             res = RB(xs)
//           }
//           // -- 1 + x if x is rightbiased
//           case (RB(`1`), RB(xs)) => {
//             // evalPlus (RightBiased One) (RightBiased x) = case x of
//             xs match {
//               // One    -> RightBiased (Plus One One)
//               case `1` => {
//                 have((`1` + `1`) ∈ R |- `1` + `1` === `1` + `1`) by Restate
//                 res = RB(`1` + `1`)
//               }
//               // Neg One -> RightBiased Zero
//               case -(`1`) => {
//                 have(
//                   (`1` + -(`1`)) ∈ R |- `1` + -(`1`) === `0`
//                 ) by Tautology.from(add_inv of (x := `1`))
//                 res = RB(`0`)
//               }
//               // Plus One x -> RightBiased (Plus One (Plus One x))
//               case (`1` + xss) => {
//                 have(
//                   (
//                     `1` ∈ R,
//                     (`1` + xss) ∈ R
//                   ) |- (`1` + (`1` + xss)) === (`1` + (`1` + xss))
//                 ) by Restate
//                 res = RB((`1` + (`1` + xss)))
//               }
//               // Plus (Neg One) x -> RightBiased x
//               case ((-(`1`)) + xss) => {
//                 have(
//                   (
//                     `1` ∈ R,
//                     -(`1`) ∈ R,
//                     xss ∈ R
//                   ) |- (`1` + ((-(`1`)) + xss)) === xss
//                 ) by Tautology.from(one_mone_xs_xs of (x := xss))
//                 res = RB(xss)
//               }
//               // _ -> error "Violates right-biased invariant"
//               case y => {
//                 res = NRB(y)
//                 return (
//                   res,
//                   proof.InvalidProofTactic("Violates Right-biased invariant")
//                 )
//               }
//             }
//           }
//           // evalPlus (RightBiased x) (RightBiased One) = evalPlus (RightBiased One) (RightBiased x)
//           case (RB(xs), RB(`1`)) => {
//             val temp = evalPlus(RB(`1`), RB(xs))
//             val prf = temp._2
//             res = temp._1
//             val ures = unapply(res)
//             val h0 = have(`1` + xs === ures) by Tautology.from(have(prf))
//             val h1 = have(
//               (xs ∈ R, `1` ∈ R) |- xs + `1` === `1` + xs
//             ) by Tautology.from(add_comm of (x := `1`, y := xs))
//             val eqs = Set(h1.bot, h0.bot).map(_.firstElemR)

//             have(eqs |- `1` + xs === `1` + xs) by Restate
//             thenHave(eqs |- `1` + xs === ures) by RightSubstEq.withParameters(
//               Seq(((`1` + xs), ures)),
//               (Seq(a), `1` + xs === a)
//             )
//             thenHave(eqs |- xs + `1` === ures) by RightSubstEq.withParameters(
//               Seq(((`1` + xs), (xs + `1`))),
//               (Seq(a), a === ures)
//             )
//             have((xs ∈ R, `1` ∈ R)  |- xs + `1` === ures) by Tautology.from(lastStep, h0, h1)
//           }
//           // evalPlus (RightBiased (Neg One)) (RightBiased x) = case x of
//           case (RB(-(`1`)), RB(xs)) => {
//             xs match {
//               //     Neg One -> RightBiased (Plus (Neg One) (Neg One))
//               case (-(`1`)) => {
//                 have(
//                   (-(`1`) + -(`1`)) ∈ R |- -(`1`) + -(`1`) === -(`1`) + -(`1`)
//                 ) by Restate
//                 res = RB(-(`1`) + -(`1`))
//               }
//               //     Plus One x -> RightBiased x
//               case (`1` + xss) => {
//                 have(
//                   (
//                     `1` ∈ R,
//                     -(`1`) ∈ R,
//                     xss ∈ R
//                   ) |- (-(`1`) + ((`1`) + xss)) === xss
//                 ) by Tautology.from(mone_one_xs_xs of (x := xss))
//                 res = RB(xss)
//               }
//               //     Plus (Neg One) x -> RightBiased (Plus (Neg One) (Plus (Neg One) x))
//               case (-(`1`) + xss) => {
//                 have(
//                   (
//                     -(`1`) ∈ R,
//                     (-(`1`) + xss) ∈ R
//                   ) |- (-(`1`) + (-(`1`) + xss)) === (-(`1`) + (-(`1`) + xss))
//                 ) by Restate
//                 res = RB((-(`1`) + (-(`1`) + xss)))
//               }
//               //     _ -> error "Violates right-biased invariant"
//               case y => {
//                 res = NRB(y)
//                 return (
//                   res,
//                   proof.InvalidProofTactic("Violates Right-biased invariant")
//                 )
//               }
//             }
//           }
//           // evalPlus (RightBiased x) (RightBiased (Neg One)) = evalPlus (RightBiased (Neg One)) (RightBiased x)
//           case (RB(xs), RB(-(`1`))) => {
//             val temp = evalPlus(RB(-(`1`)), RB(xs))
//             val prf = temp._2
//             res = temp._1
//             val ures = unapply(res)
//             val h0 = have(-(`1`) + xs === ures) by Tautology.from(have(prf))
//             val h1 = have(
//               (xs ∈ R, -(`1`) ∈ R) |- xs + -(`1`) === -(`1`) + xs
//             ) by Tautology.from(add_comm of (x := -(`1`), y := xs))
//             val eqs = Set(h1.bot, h0.bot).map(_.firstElemR)

//             have(eqs |- -(`1`) + xs === -(`1`) + xs) by Restate
//             thenHave(eqs |- -(`1`) + xs === ures) by RightSubstEq
//               .withParameters(
//                 Seq(((-(`1`) + xs), ures)),
//                 (Seq(a), -(`1`) + xs === a)
//               )
//             thenHave(eqs |- xs + -(`1`) === ures) by RightSubstEq
//               .withParameters(
//                 Seq(((-(`1`) + xs), (xs + -(`1`)))),
//                 (Seq(a), a === ures)
//               )
//             have((xs ∈ R, -(`1`) ∈ R) |- xs + -(`1`) === ures) by Tautology.from(lastStep, h0, h1)
//           }
//           // evalPlus (RightBiased (Plus o1 x)) (RightBiased (Plus o2 y)) = case (o1, o2) of
//           case (RB(o1 + xs), RB(o2 + ys)) => {
//             (o1, o2) match {
//               //     (One, Neg One) -> evalPlus (RightBiased x) (RightBiased y)
//               case (-(`1`), `1`) => {
//                 val temp = evalPlus(RB(xs), RB(ys))
//                 val prf = temp._2
//                 res = temp._1
//                 val ures = unapply(res)
//                 val h0 = have(xs + ys === ures) by Tautology.from(have(prf))
//                 val h1 = have(
//                   (xs ∈ R, ys ∈ R) |- (-(`1`) + xs) + (`1` + ys) === xs + ys
//                 ) by Tautology.from(addPlusHelper2 of (x := xs, y := ys))
//                 val eqs = Set(h1.bot, h0.bot).map(_.firstElemR)

//                 have(
//                   eqs |- (-(`1`) + xs) + (`1` + ys) === (-(`1`) + xs) + (`1` + ys)
//                 ) by Restate
//                 thenHave(
//                   eqs |- (-(`1`) + xs) + (`1` + ys) === xs + ys
//                 ) by RightSubstEq.withParameters(
//                   Seq((((-(`1`) + xs) + (`1` + ys)), (xs + ys))),
//                   (Seq(a), (-(`1`) + xs) + (`1` + ys) === a)
//                 )
//                 thenHave(
//                   eqs |- (-(`1`) + xs) + (`1` + ys) === ures
//                 ) by RightSubstEq.withParameters(
//                   Seq(((xs + ys), ures)),
//                   (Seq(a), (-(`1`) + xs) + (`1` + ys) === a)
//                 )
//                 have((xs ∈ R, ys ∈ R) |- (-(`1`) + xs) + (`1` + ys) === ures) by Tautology.from(
//                   lastStep, h0, h1
//                 )
//               }
//               //     (Neg One, One) -> evalPlus (RightBiased x) (RightBiased y)
//               case (`1`, -(`1`)) => {
//                 val temp = evalPlus(RB(xs), RB(ys))
//                 val prf = temp._2
//                 res = temp._1
//                 val ures = unapply(res)
//                 val h0 = have(xs + ys === ures) by Tautology.from(have(prf))
//                 val h1 = have(
//                   (xs ∈ R, ys ∈ R) |- (`1` + xs) + (-(`1`) + ys) === xs + ys
//                 ) by Tautology.from(addPlusHelper1 of (x := xs, y := ys))
//                 val eqs = Set(h1.bot, h0.bot).map(_.firstElemR)

//                 have(
//                   eqs |- (`1` + xs) + (-(`1`) + ys) === (`1` + xs) + (-(`1`) + ys)
//                 ) by Restate
//                 thenHave(
//                   eqs |- (`1` + xs) + (-(`1`) + ys) === xs + ys
//                 ) by RightSubstEq.withParameters(
//                   Seq((((`1` + xs) + (-(`1`) + ys)), (xs + ys))),
//                   (Seq(a), (`1` + xs) + (-(`1`) + ys) === a)
//                 )
//                 thenHave(
//                   eqs |- (`1` + xs) + (-(`1`) + ys) === ures
//                 ) by RightSubstEq.withParameters(
//                   Seq(((xs + ys), ures)),
//                   (Seq(a), (`1` + xs) + (-(`1`) + ys) === a)
//                 )
//                 have((xs ∈ R, ys ∈ R) |- (`1` + xs) + (-(`1`) + ys) === ures) by Tautology.from(
//                   lastStep, h0, h1
//                 )
//               }
//               //     (One, One) -> evalPlus (RightBiased x) (RightBiased (Plus One (Plus One y)))
//               case (`1`, `1`) => {
                
//                 val temp = evalPlus(RB(xs), RB(`1` + (`1` + ys)))
//                 val prf = temp._2
//                 res = temp._1
//                 val ures = unapply(res)
                
//                 val h0 = have(prf)
//                 val h1 = have((xs ∈ R, ys ∈ R) |- (`1` + xs) + (`1` + ys) === xs + (`1` + (`1` + ys))) by Tautology.from(addPlusHelper3 of (x := xs, y := ys))
//                 val stmt = 
//                   val newStatement =((xs ∈ R, ys ∈ R) |- (`1` + xs) + (`1` + ys) === ures)
//                   newStatement ++<< h0.bot ++<< h1.bot
//                 println("h0 and h1")
//                 println(h0.bot.toString)
//                 println(h1.bot.toString)
//                 println(ures)
//                 val eqs = Set(h1.bot, h0.bot).map(_.firstElemR)
//                 val typings = getTypings(h0.bot.left) ++ getTypings(h1.bot.left)
//                 have(
//                   eqs |- (`1` + xs) + (`1` + ys) === (`1` + xs) + (`1` + ys)
//                 ) by Restate
//                 thenHave(
//                   eqs |- (`1` + xs) + (`1` + ys) === xs + (`1` + (`1` + ys)) 
//                 ) by RightSubstEq.withParameters(
//                   Seq((((`1` + xs) + (`1` + ys)), xs + (`1` + (`1` + ys)) )),
//                   (Seq(a), (`1` + xs) + (`1` + ys) === a)
//                 )
//                 thenHave(
//                   eqs |- (`1` + xs) + (`1` + ys) === ures
//                 ) by RightSubstEq.withParameters(
//                   Seq((xs + (`1` + (`1` + ys)) , ures)),
//                   (Seq(a), (`1` + xs) + (`1` + ys) === a)
//                 )
//                 println("here")
//                 val fin = have(stmt) by Tautology.from(
//                   lastStep,
//                   h0,
//                   h1
//                 )
//                 println(fin.bot)
//                 // println("here 3")
//               }
//               //     (Neg One, Neg One) -> evalPlus (RightBiased x) (RightBiased (Plus (Neg One) (Plus (Neg One) y)))
//               case (-(`1`), -(`1`)) => { 
//                 val temp = evalPlus(RB(xs), RB(-(`1`) + (-(`1`) + ys)))
//                 val prf = temp._2
//                 res = temp._1
//                 val ures = unapply(res)
            
//                 val h0 = have(prf)
//                 val h1 = have((xs ∈ R, ys ∈ R) |- (-(`1`) + xs) + (-(`1`) + ys) === xs + (-(`1`) + (-(`1`) + ys))) by Tautology.from(addPlusHelper4 of (x := xs, y := ys))
//                 val stmt = 
//                   val newStatement =((xs ∈ R, ys ∈ R) |- (-(`1`) + xs) + (-(`1`) + ys) === ures)
//                   newStatement ++<< h0.bot ++<< h1.bot
//                 println("h0 and h1")
//                 println(h0.bot.toString)
//                 println(h1.bot.toString)
//                 println(ures)
//                 val eqs = Set(h1.bot, h0.bot).map(_.firstElemR)
//                 val typings = getTypings(h0.bot.left) ++ getTypings(h1.bot.left)
//                 have(
//                   eqs |- (`1` + xs) + (`1` + ys) === (`1` + xs) + (`1` + ys)
//                 ) by Restate
//                 thenHave(
//                   eqs |- (`1` + xs) + (`1` + ys) === xs + (`1` + (`1` + ys)) 
//                 ) by RightSubstEq.withParameters(
//                   Seq((((`1` + xs) + (`1` + ys)), xs + (`1` + (`1` + ys)) )),
//                   (Seq(a), (`1` + xs) + (`1` + ys) === a)
//                 )
//                 thenHave(
//                   eqs |- (`1` + xs) + (`1` + ys) === ures
//                 ) by RightSubstEq.withParameters(
//                   Seq((xs + (`1` + (`1` + ys)) , ures)),
//                   (Seq(a), (`1` + xs) + (`1` + ys) === a)
//                 )
//                 println("here")
//                 val fin = have(stmt) by Tautology.from(
//                   lastStep,
//                   h0,
//                   h1
//                 )
//                 println(fin.bot)
//               }
//               //     _ -> error "Violates right-biased invariant"
//               case (o1, _) => {
//                 res = NRB(o1)
//                 return (
//                   res,
//                   proof.InvalidProofTactic("Violates right-biased invariant")
//                 )
//               }
//             }
//           }

//           // evalPlus _ _ = error "Violates right-biased invariant"
//           case (x, _) => {
//             res = NRB(unapply(x))
//             return (
//               res,
//               proof.InvalidProofTactic("Violates right-biased invariant")
//             )
//           }

//         }
//       }(res)
//     }

    
//     def simplify(using proof: library.Proof)(
//         goal: Expr[Prop]
//     ): (proof.ProofTacticJudgement) = {
//       assume(ring(R, <=, +, *, -, |, `0`, `1`))
//       val w = TacticSubproof {
//         goal match
//           case x `equality` y if canonicalInt(x) && canonicalInt(y) => {
//             have(x === y) by Tautology

//           }
//           case x `equality` y => {
//             val (lval, lprf) = evalRingEq.evalRing(x)
//             val (rval, rprf) = evalRingEq.evalRing(y)
//             val ulval = unapply(lval)
//             val urval = unapply(rval)
//             println("blerg")
//             val lprfseq = have(lprf)
//             val rprfseq = have(rprf)
//             val typingAssumptions = typeChecking(
//               getTypingVarsInAnte(lprfseq.bot.left) ++
//               getTypingVarsInAnte(rprfseq.bot.left)
//             )
//             println(typingAssumptions.size)
//             println("blerg2")
            
//             val eqs = SSet(lprfseq.bot, rprfseq.bot).map(_.firstElemR)
//             // println(eqs.)
//             println(eqs.size)
//             println("blerg3")
//             have(eqs |- ulval === urval) by Restate
//             println("blerg4")
//             thenHave(eqs |- ulval === y) by RightSubstEq.withParameters(
//                   Seq((y , urval)),
//                   (Seq(a), ulval === a)
//                 )
//             println("blerg5")
//             thenHave(eqs |- x === y) by RightSubstEq.withParameters(
//                   Seq((x , ulval)),
//                   (Seq(a), a === y)
//                 )
//             println("blerg6")
//             // and you may ask yourself, why are you not using the scala debugger? 
//             // and you may ask yourself, why are there all of these print statements? 
//             // and you my ask yourself, why is it stuck on Tautology?
//             println(lprfseq.bot.left.size)
//             println(rprfseq.bot.left.size)
//             val seqs1 = typingAssumptions + lprfseq
//             val seqs  = seqs1 + rprfseq
//             println("blerg7")
//             println(lprfseq.bot)
//             println(rprfseq.bot)
//             println(lastStep.bot)
//             // val typingAssumptions: SSet[contextual$4.InstantiatedFact | contextual$4.ProofStep]
//             typingAssumptions.map(x => 
//                 println(x.getClass())
//                 x match
//                     case x : Library#Proof#InnerProof#InstantiatedFact => println(x.result)
//                     case x : Library#Proof#InnerProof#ProofStep        => println(x.bot)

//                     // case x : proof.iP
//             )
//             // FIXME, maybe
//             // this gives you a compile time error
//             // typingAssumptions.foreach: x => println(proof.getSequent(x))
//             // case x : proof.iP
            
//             scala.Console.flush()
//             println(((seqs + lastStep).toSeq).size)
//             // TODO: replace with cuts
//             have(goal) by Tautology.from((seqs + lastStep).toSeq*)
//             println("blerg8")

//             // val leftCongruence = have(x === simplify(x)) by Tautology
//             // val rightCongruence = have(y === simplify(y)) by Tautology
//           }

//           case _ =>
//             proof.InvalidProofTactic("incomplete")

//       }
//       println("blerg9")
//       w
//       // TODO: Tautology by sorry
//     }

//     //   {???}
//     // }

//   import BigIntToRingElem.i

//   val evalAdd_test1 = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(2) === i(2)){
//     have(thesis) by evalRingEq.apply
//   }

//   // val evalTest2 = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(10) + i(5) === i(15)){
//   //   have(thesis) by evalRingEq.apply
//   // }

//   val evalAdd_test2 = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(2) + i(2) === i(4)){
//     have(thesis) by evalRingEq.apply
//   }
//   val evalAdd_test3 = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(2) + i(3) === i(5)){
//     have(thesis) by evalRingEq.apply
//   }
// //   val evalAdd_test4 = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(4) + i(3) === i(7)){
// //     have(thesis) by evalRingEq.apply
// //   }
// //   val evalAdd_test5 = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(5) + i(5) === i(10)){
// //     have(thesis) by evalRingEq.apply
// //   }
//   // val two_two_four = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- i(2) + i(2) === i(4)){
//   //   sorry
//   // }

//   inline def bigIntShorthand(x: BigInt): Expr[Ind] = {
//     Variable(s"$x")
//   }
//   // inline def shorthandToBigInt(x: Expr[Ind]): BigInt = {
//   //   x.
//   // }

//   inline def bigIntEmbed(x: BigInt): Expr[Prop] = {
//     i(x) ∈ R
//   }

//   // println(Rings.ring.definition.statement)
//   // println(order_refl.statement.left.getClass)
//   // println(order_refl.statement.right)
//   val test: Expr[Prop] = ∀(x, x ∈ R ==> x <= x)
//   // println(test.getClass)
// }
// // end RingEqReasoning
