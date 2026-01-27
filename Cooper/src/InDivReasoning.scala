import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import SubProofWithRes.TacticSubproofWithResult
import scala.collection.immutable.{Set => SSet}
import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, c => _, P => _, ∈ => _, have => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
import scala.quoted.quotes
import scala.quoted.{Expr => EExpr, Quotes  }
import scala.math.Ordering
import lisa.utils.prooflib.Library
import scala.collection.SortedSet
import scala.collection.SeqView.Sorted
import RingStructure.{*}
import Utils.{*, given Ordering[?]}
import InEqReasoning.inEquality
import DivReasoning.divInts

object InDivReasoning extends lisa.Main {
  import RingElemConversions.*
  import EqReasoning.*
  import TypeChecker.*
    object inDivInts extends ProofTactic {
    def apply(using proof: library.Proof)(goal: Sequent)(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          goal.left.map(xs => assume(xs))
          if (!is_indiv(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than indivisibility!")
          else if (exprHasVariables(goalElem)) return proof.InvalidProofTactic("I am a lazy tactic! I only work on numbers (mostly)!")
          else
            val sol = simplifyInDiv(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking divisibility failed!")
            have(sol)
        }
    }
    }

    def simplifyInDiv(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {

        TacticSubproof{
      
        goal match {
          case !(RingStructure.`|`(ty, tx)) => {
            // ty | tx <=> ∃c. tx = c*ty
            // BigInts are used as an oracle.
            val tyv = ci(ty)
            val txv = ci(tx)
            if ((txv % tyv) == 0) then return proof.InvalidProofTactic("Is divisible, use DivReasoning instead")
            
            val tcv = txv/tyv
            val ddiv = tyv * tcv
            val diff = txv - (ddiv)
            val tc  = ic(tcv)
            val tdiff = ic(diff)
            val tddiv = ic(ddiv)
            
            val l = have(0 < diff) by inEquality.apply
            val r = have(diff < ty) by inEquality.apply
            val leq = have(tx === tddiv + tdiff) by evalRingEq.apply
            val c = have(ty | tddiv) by divInts.apply
            
            val txr = have(tddiv ∈ R) by typeCheck.apply
            val tyr = have(ty ∈ R) by typeCheck.apply
            val tdr = have(tdiff ∈ R) by typeCheck.apply

            val vs = have(!(ty | (tddiv + tdiff))) by Tautology.from(does_not_divide of (x := tddiv, y := tdiff, z := ty), txr, tyr, tdr, l, r, c)
            have(!(ty | (tx))) by Congruence.from(vs, leq)
            
          }
          case _ => return proof.InvalidProofTactic("Can only solve indivs")
            

        
      }
    }
  }
}
