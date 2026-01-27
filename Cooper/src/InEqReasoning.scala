import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import SubProofWithRes.TacticSubproofWithResult
import scala.collection.immutable.{Set => SSet}
import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, P => _, ∈ => _, have => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
import scala.quoted.quotes
import scala.quoted.{Expr => EExpr, Quotes  }
import scala.math.Ordering
import lisa.utils.prooflib.Library
import scala.collection.SortedSet
import scala.collection.SeqView.Sorted
import RingStructure.{*}
import RingDivOrdering.{*}
import Utils.{*, given Ordering[?]}
import EqReasoning.evalRingEq.evalRing

object InEqReasoning extends lisa.Main {
    import RingElemConversions.*
    import EqReasoning.*
    import TypeChecker.*
    object inEquality extends ProofTactic {
    def apply(using proof: library.Proof)(goal: Sequent)(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          assume(ring(R, <=, <, +, *, -, |, 0, 1))
          if (!is_ineq(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than inequalities!")
          else
            val sol = simplifyInEq(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking divisibility failed!")
            have(sol)
        }
    }
    }

    def simplifyInEq(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {

        TacticSubproof{
      
        goal match {
          // ty < tx
          case RingStructure.<=(ty, tx) => {            
            val diff = evalRing(tx + -ty)
            val tx_inR = have(tx ∈ R) by typeCheck.apply
            val ty_inR = have(ty ∈ R) by typeCheck.apply
            val (tres, tprf) = evalRing(tx + -ty)
            if !(tprf.isValid) then return proof.InvalidProofTactic("evalRing failed!!")
            if (treeHasVariables(tres.tval)) return proof.InvalidProofTactic("I am a lazy tactic! I only work on numbers (mostly)!")
            val vprf = have(tprf) // tx - ty === tres

          }
          case RingStructure.<(ty, tx) => {            
            
          }
          case !(RingStructure.<=(ty, tx)) => {            
            
          }
          case !(RingStructure.<(ty, tx)) => {            
            
          }
          case _ => return proof.InvalidProofTactic("Can only solve inequalities")
            

        
      }
      }
    }

    def evalLe(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
    TacticSubproof{
      if !is_le(goal) then return proof.InvalidProofTactic("internal tactic, don't use me!")
        goal match {
          case RingStructure.<=(`0`, `1`) => {
            have(`0` <= `1`) by Tautology.from(zero_le_1)
          }
          case RingStructure.<=(`0`, tx) => {            
            if !(BigInt(0) < ci(tx)) then return proof.InvalidProofTactic("Not LE!")
            // val nres = evalRing(7tx + -1)
            ???
          }
          case _ => return proof.InvalidProofTactic("Unreachable!")
        } 
      }
    }

}
