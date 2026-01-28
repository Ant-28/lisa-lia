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
import Utils.{*, given Ordering[?]}
import EqReasoning.evalRingEq.evalRing
import InEqReasoning.inEquality

object DisEqReasoning extends lisa.Main {
  import RingElemConversions.*
  import EqReasoning.*
  import TypeChecker.*
  import RingDivOrdering.*
  object disEquality extends ProofTactic {
    def apply(using proof: library.Proof)(goal: Sequent)(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          goal.left.map(xs => assume(xs))
          if (!is_neq(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than inequalities!")
          else
            val sol = simplifyDisEq(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking divisibility failed!")
            have(sol)
        }
    }
    

    def simplifyDisEq(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {

      TacticSubproof{ IProof  ?=> 
      
        goal match {
          // ty < tx
          case !(ty `equality` tx) => {            
            
            val tx_inR = have(tx ∈ R) by typeCheck.apply
            val ty_inR = have(ty ∈ R) by typeCheck.apply
            val (tres, tprf) = evalRing(tx + -ty)
            if !(tprf.isValid) then return proof.InvalidProofTactic("evalRing failed!!")
            val hprf = have(tprf)
            val typing = typeChecking(getTypingVarsInAnte(hprf.bot.left))
            var temp  = (getTypings(hprf.bot.left), TacticSubproof {have(0 === 0) by Restate} )
            val seqs = typing + hprf
            have(hprf.bot) by Restate.from(hprf)
            typing.toList.sortBy(proofStepDepth).map( x => {
                val sof = IProof.sequentOfFact(x)
                val srh = sof.right.head
                val sl  = sof.left
                val consq = hprf.bot.right.head
                temp = evalRingCutHelper(x, consq, temp._1, lastStep)
                have(temp._2)     
              }
            )
            if (treeHasVariables(tres.tval)) return proof.InvalidProofTactic("I am a lazy tactic! I only work on numbers (mostly)!")
            // tx - ty === tres
            val vprf = have(temp._2)
            val leprf = evalNeq(`0` !== tres.tval)
            val l = have(leprf) // 0 <= tres.tval
            val ls = have(`0` !== tx  + -ty) by Congruence.from(lastStep, vprf)
            have(ty !== tx) by Tautology.from(ls,  x_neq_y_zero_neq_xmy_iff of (x := tx, y := ty), tx_inR,ty_inR)
          }
          case _ => proof.InvalidProofTactic("How did you get here?")
        }
      }
    }
    def evalNeq(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      TacticSubproof{ IProof  ?=> 
        goal match {
          
          case !(`0` `equality` ty) => {
            val ty_int = ci(ty)
            ty_int match {
              case ty_int if (ty_int == 0) => return proof.InvalidProofTactic("erm ackchually this is equal")
              case ty_int if (ty_int < 0) => {
                val typ = have(ty ∈ R) by typeCheck.apply
                have(ty < `0`) by inEquality.apply
                have((`0` !== ty)) by Tautology.from(typ, lastStep, trichotomy1 of (x := ty, y := 0), add_id_closure)
              }
              case ty_int if (BigInt(0) < ty_int) => {
                val typ = have(ty ∈ R) by typeCheck.apply
                have(`0` < ty) by inEquality.apply
                have((`0` !== ty)) by Tautology.from(typ, lastStep, trichotomy1 of (x := 0, y := ty), add_id_closure)
              }
            }
            
            
          }

          case _ => return proof.InvalidProofTactic("unreachable")
          }
      
      }
    }
  }
}
