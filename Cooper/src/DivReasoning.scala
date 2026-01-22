import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import SubProofWithRes.TacticSubproofWithResult
import scala.collection.immutable.{Set => SSet}
import lisa.maths.SetTheory.Base.Predef.{c => _, x => _, y => _, z => _, P => _, ∈ => _, have => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
import scala.quoted.quotes
import scala.quoted.{Expr => EExpr, Quotes  }
import scala.math.Ordering
import lisa.utils.prooflib.Library
import scala.collection.SortedSet
import scala.collection.SeqView.Sorted
import RingStructure.{*}
import Utils.{*, given Ordering[?]}
import EqReasoning.evalRingEq
import TypeChecker.typeCheck


object DivReasoning extends lisa.Main {
    import RingElemConversions.*
    object divInts extends ProofTactic {
    def apply(using proof: library.Proof)(goal: Sequent)(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          assume(ring(R, <=, +, *, -, |, 0, 1))
          if (!is_div(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than divisibility!")
          else if (exprHasVariables(goalElem)) return proof.InvalidProofTactic("I am a lazy tactic, use <NAME> instead! I only work on numbers!")
          else
            val sol = simplifyDiv(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking divisibility failed!")
            have(sol)
        }
    }
    }

    def simplifyDiv(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {

        TacticSubproof{
      
        goal match {
          case RingStructure.`|`(ty, tx) => {
            // ty | tx <=> ∃c. tx = c*ty
            val tyv = ci(ty)
            val txv = ci(tx)
            if ((txv % tyv) != 0) then return proof.InvalidProofTactic("Is not divisible")
            val tcv = txv/tyv
            val tc  = ic(tcv)
            val left = have(tx === ty * tc) by evalRingEq.apply
            val right = have(tc ∈ R) by typeCheck.apply
            val txr = have(tx ∈ R) by typeCheck.apply
            val tyr = have(ty ∈ R) by typeCheck.apply
            have(tc ∈ R /\ (tx === ty * tc)) by RightAnd(left, right) // is this right?
            thenHave(∃(c, c ∈ R /\ (tx === ty * c))) by RightExists
            have((ring(R, <=, +, *, -, |, `0`, `1`),tx ∈ R, ty ∈ R) |- ∃(c, c ∈ R /\ (tx === ty * c))) by Tautology.from(lastStep, txr, tyr)
            have(goal) by Tautology.from(div_qe of (x := tx, y := ty), lastStep, txr, tyr)
          }
          case _ => return proof.InvalidProofTactic("Can only solve inequalities")
            

        
      }
    }
  }

}
