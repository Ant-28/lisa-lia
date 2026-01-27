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
          goal.left.map(xs => assume(xs))
          if (!is_ineq(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than inequalities!")
          else
            val sol = simplifyInEq(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking divisibility failed!")
            have(sol)
        }
    }
    

    def simplifyInEq(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {

        TacticSubproof{ IProof  ?=> 
      
        goal match {
          // ty < tx
          case RingStructure.<=(ty, tx) => {            

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
            val leprf = evalLe(0 <= tres.tval)
            val l = have(leprf) // 0 <= tres.tval
            val ls = have(0 <= tx  + -ty) by Congruence.from(lastStep, vprf)
            have(ty <= tx) by Tautology.from(ls,  le_0ymx_xy of (x := ty, y := tx), tx_inR,ty_inR)
          }
          case RingStructure.<(ty, tx) => {            

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
            val ltprf = evalLt(0 < tres.tval)
            val l = have(ltprf) // 0 <= tres.tval
            val ls = have(0 < tx  + -ty) by Congruence.from(lastStep, vprf)
            have(ty < tx) by Tautology.from(ls,  lt_0ymx_xy of (x := ty, y := tx), tx_inR,ty_inR)
          }
          case !(RingStructure.<=(ty, tx)) => {
            val tx_inR = have(tx ∈ R) by typeCheck.apply
            val ty_inR = have(ty ∈ R) by typeCheck.apply            
            val sol = this.apply(tx < ty)
            if !sol.isValid then return proof.InvalidProofTactic("ty <= tx, this negation does not hold")
            have(sol)
            have(!(ty <= tx)) by Tautology.from(lastStep, le_lt_neg_iff of (x := tx, y := ty),tx_inR,ty_inR)
          }
          case !(RingStructure.<(ty, tx)) => {
            val tx_inR = have(tx ∈ R) by typeCheck.apply
            val ty_inR = have(ty ∈ R) by typeCheck.apply            
            val sol = this.apply(tx <= ty)
            if !sol.isValid then return proof.InvalidProofTactic("ty < tx, this negation does not hold")
            have(sol)
            have(!(ty < tx)) by Tautology.from(lastStep, le_lt_neg_iff of (x := ty, y := tx), tx_inR,ty_inR)
          }
          case _ => return proof.InvalidProofTactic("Can only solve inequalities")
            

        
      }
      }
    }

    def evalLe(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
    TacticSubproof{
      if !is_le(goal) then return proof.InvalidProofTactic("internal tactic, don't use me!")
        goal match {
          case RingStructure.<=(`0`, `0`) => {
            have(`0` <= `0`) by Tautology.from(le_refl of (x := 0), add_id_closure)
          }
          case RingStructure.<=(`0`, `1`) => {
            have(`0` <= `1`) by Tautology.from(zero_le_1)
          }
          case RingStructure.<=(`0`, tx) => {            
            if !(BigInt(0) <= ci(tx)) then return proof.InvalidProofTactic("Not LE!")
            val nres = evalRing(tx + -1)
            val res = evalLe(0 <= nres._1.tval)
            val rprf = have(res)
            val vprf = have(nres._2)
            val tprf = have(tx ∈ R) by typeCheck.apply
            have(0 <= (tx + -1)) by Congruence.from(rprf, vprf)
            val cc = have(0 <= (tx + -1) + 1) by Tautology.from(lastStep, tprf, add_closure of (x := tx, y := -1), neg_closure of (x := 1), mul_id_closure, le_plus1 of (x := 0, y := (tx + -1)), add_id_closure)
            val eqr = have((tx + -1) + 1 === tx) by Tautology.from(tprf, x_mz_z_x of (x := tx, z := 1), mul_id_closure)
            have(0 <= tx) by Congruence.from(cc, eqr)
          }
          case _ => return proof.InvalidProofTactic("Unreachable!")
        } 
      }
    }

    def evalLt(using proof: library.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
    TacticSubproof{
      if !is_lt(goal) then return proof.InvalidProofTactic("internal tactic, don't use me!")
        goal match {
          case RingStructure.<(`0`, `1`) => {
            have(`0` < `1`) by Tautology.from(zero_lt_1)
          }
          case RingStructure.<(`0`, tx) => {            
            if !(BigInt(0) < ci(tx)) then return proof.InvalidProofTactic("Not LT!")
            val nres = evalRing(tx + -1)
            val res = evalLt(0 < nres._1.tval)
            val rprf = have(res)
            val vprf = have(nres._2)
            val tprf = have(tx ∈ R) by typeCheck.apply
            have(0 < (tx + -1)) by Congruence.from(rprf, vprf)
            val cc = have(0 < (tx + -1) + 1) by Tautology.from(lastStep, tprf, add_closure of (x := tx, y := -1), neg_closure of (x := 1), mul_id_closure, lt_plus1 of (x := 0, y := (tx + -1)), add_id_closure)
            val eqr = have((tx + -1) + 1 === tx) by Tautology.from(tprf, x_mz_z_x of (x := tx, z := 1), mul_id_closure)
            have(0 < tx) by Congruence.from(cc, eqr)
          }
          case _ => return proof.InvalidProofTactic("Unreachable!")
        } 
      }
    }
}
}
