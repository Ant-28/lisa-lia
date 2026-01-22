import scala.collection.immutable.{Set => SSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, P => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution
import Base.{IBinFun, IUnFun, IRel, infixBinaryFunction, infixUnaryFunction}
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}
import Utils.*

// proves ring(R, <=, <, +, *, -, |, `0`, `1`) |- tx ∈ R
object TypeChecker extends lisa.Main {
  import RingStructure.*
    object typeCheck extends ProofTactic {
      def apply(using proof: library.Proof)(goal: Sequent)(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
        if (goal.right.size != 1) then
          proof.InvalidProofTactic("I can't prove more than one sequent!")
        else
          val goalElem = goal.right.head
          TacticSubproof{
            assume(ring(R, <=, <, +, *, -, |, 0, 1))
            val sol = simplifyTC(goalElem)
            if !sol.isValid then return proof.InvalidProofTactic("Typechecking failed!")
            have(sol)
            have(goal) by Restate.from(lastStep)
          }
      }
    }
    def simplifyTC(using proof: library.Proof)(goalElem: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      goalElem match {
        case tx ∈ R => {
          // collect subexprs is useful here. not used in eqreasoning because we always bottom out at 0 or 1 or x. 
          TacticSubproof{
            tx match {
              case `0` => have(`0` ∈ R) by Tautology.from(add_id_closure)
              case `1` => have(`1` ∈ R) by Tautology.from(mul_id_closure)
              case tx1 if isVariable(tx) => have(tx1 ∈ R |- tx1 ∈ R) by Restate 
              case tx1 + tx2 => {
                val prfx1 = simplifyTC(tx1 ∈ R)
                if !prfx1.isValid then return proof.InvalidProofTactic("Typechecking failed!")
                val prfx2 = simplifyTC(tx2 ∈ R)
                if !prfx2.isValid then return proof.InvalidProofTactic("Typechecking failed!")
                val (prf1, prf2) = (have(prfx1), have(prfx2))
                val step1 = have((ring(R, <=, <, +, *, -, |, `0`, `1`), tx1 ∈ R, tx2 ∈ R) |- (tx1 + tx2) ∈ R) by Tautology.from(add_closure of (x := tx1, y := tx2))
                val typings = SSet(prf1, prf2).map(_.sRightHead)
                var temp = evalRingCutHelper(prf1, tx ∈ R, typings, lastStep)
                have(temp._2)
                temp = evalRingCutHelper(prf2, tx ∈ R, temp._1, lastStep)
                have(temp._2)
              }
              case tx1 * tx2 => {
                val prfx1 = simplifyTC(tx1 ∈ R)
                if !prfx1.isValid then return proof.InvalidProofTactic("Typechecking failed!")
                val prfx2 = simplifyTC(tx2 ∈ R)
                if !prfx2.isValid then return proof.InvalidProofTactic("Typechecking failed!")
                val (prf1, prf2) = (have(prfx1), have(prfx2))
                val step1 = have((ring(R, <=, <, +, *, -, |, `0`, `1`), tx1 ∈ R, tx2 ∈ R) |- (tx1 * tx2) ∈ R) by Tautology.from(mul_closure of (x := tx1, y := tx2))
                val typings = SSet(prf1, prf2).map(_.sRightHead)
                var temp = evalRingCutHelper(prf1, tx ∈ R, typings, lastStep)
                have(temp._2)
                temp = evalRingCutHelper(prf2, tx ∈ R, temp._1, lastStep)
                have(temp._2)
              }
              case -(tx1) => {
                val prfx1 = simplifyTC(tx1 ∈ R)
                if !prfx1.isValid then return proof.InvalidProofTactic("Typechecking failed!")
                val prf1 = have(prfx1)
                val step1 = have((ring(R, <=, <, +, *, -, |, `0`, `1`), tx1 ∈ R) |- -tx1 ∈ R) by Tautology.from(neg_closure of (x := tx1))
                val typings = SSet(prf1).map(_.sRightHead)
                var temp = evalRingCutHelper(prf1, tx ∈ R, typings, lastStep)
                have(temp._2)
              }
              case _ => return proof.InvalidProofTactic("Typechecking failed!")
            }
          }
        }
        case _ => return proof.InvalidProofTactic("I am but a mere typechecker!")
      }  
    }
}
