// Eq Reasoning 
// equational reasoning, with Main.hs as a reference point
import lisa.utils.prooflib.ProofTacticLib.ProofTactic

object EqReasoning extends lisa.Main {
    import RingStructure.{*}
    import Utils.{*}
    // RB-trees: an ex
    sealed trait Biased
    case class RB(x: Expr[Ind]) extends Biased 
    case class NRB(x: Expr[Ind]) extends Biased 

    def unapply(x: Biased): Expr[Ind] = x match
        case RB(xs)  => xs
        case NRB(xs) => xs


    object inSet extends ProofTactic {
      def from(using lib: library.type, proof: lib.Proof)(premises: proof.Fact*)(bot: Sequent) = ???
    }

    object evalRingEq extends ProofTactic {
    
    def apply(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          assume(ring(R, <=, +, *, -, |, `0`, `1`))
          if (!is_eq(goalElem)) then
            proof.InvalidProofTactic(
              "I can't prove anything other than equality!"
            )
          else
            val sol = simplify(goalElem)

            // println(have(sol).bot)
            if !sol.isValid then
              proof.InvalidProofTactic("Checking sums failed!")
            else
              val typing =  typeChecking(getTypingVarsInAnte(have(sol).bot.left))
              val seqs = typing + have(sol)
              // TODO: Use cuts instead
              have(goal) by Tautology.from(seqs.toSeq*)
        }
    }


    def simplify(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = ???

    }



}