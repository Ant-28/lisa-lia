// Eq Reasoning 
// equational reasoning, with Main.hs as a reference point
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import SubProofWithRes.TacticSubproofWithResult
import scala.collection.immutable.{Set => SSet}
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.{*, given}
import scala.quoted.quotes
import scala.quoted.{Expr => EExpr, Quotes  }


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
          if (!is_eq(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than equality!")
          else
            val sol = simplify(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking sums failed!")
            else
              val typing = typeChecking(getTypingVarsInAnte(have(sol).bot.left))
              val seqs = typing + have(sol)
              // TODO: Use cuts instead
              have(goal) by Tautology.from(seqs.toSeq*)
        }
    }


    def simplify(using lib: library.type, proof: lib.Proof)(goal: Expr[Prop]): proof.ProofTacticJudgement = 
      {assume(ring(R, <=, +, *, -, |, `0`, `1`))
      TacticSubproof {
        goal match 
          case x `equality` y => have(() |- x === x) by Restate
          case _ => return proof.InvalidProofTactic("Can only solve inequalities")
      }}
    
      

    def evalRing(using lib: library.type, proof: lib.Proof)(int: Expr[Ind]): (Biased, proof.ProofTacticJudgement) = {
      x
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
        int match {
          case `0` => {
            have(`0` === `0`) by Restate
            res = RB(`0`)
          }
          case `1` => {
            have(`1` === `1`) by Restate
            res = RB(`1`)
          }
          case x + y => {
            val (vx, px) = evalRing(x)
            val (vy, py) = evalRing(y)
            if(!px.isValid || !py.isValid) 
            // early exit
            then return (NRB(x), proof.InvalidProofTactic("evalRing failed!"))
            val (vsum, psum) = evalPlus(vx, vy)
            if(!psum.isValid) then return (NRB(x), proof.InvalidProofTactic("evalPlus failed!"))
            val (uvx, uvy, uvsum) = (vx, vy, vsum).map[[t] =>> Expr[Ind]]([t] => x => unapply(x.asInstanceOf[Biased]))
            val (xeq, yeq, sumeq) = (have(px), have(py), have(psum))
            var equalities = SSet(xeq, yeq, sumeq).map(_.bot.firstElemR)
            have(equalities |- x + y === x + y) by Restate 
            thenHave(equalities |- x + y === uvx + uvy) by RightSubstEq.withParameters(
              Seq((x, uvx), (y, uvy)),
              (Seq(a, b), x + y === a + b)
            )
            thenHave(equalities |- x + y === uvsum) by RightSubstEq.withParameters(
              Seq((x + y, uvsum)),
              (Seq(a), x + y === a)
            )
            // WARNING: you may need val typs = SSet(x ∈ R, y ∈ R) ++ List(xeq, yeq, sumeq).map(l => getTypings(l.bot.left)).fold(Set())((x, y) => x ++ y)
            // TODO: Remove first set?

            // var toCut = xeq.sRightHead
            // equalities = equalities.excl(xeq.sRightHead)
            // var tempAnte = equalities
            // tempAnte = tempAnte.excl(xeq.sRightHead) ++ xeq.sLeft
            // have(tempAnte |- x + y === uvsum) by Cut.withParameters(toCut)(xeq, lastStep)
            // toCut = yeq.sRightHead 
            // tempAnte = tempAnte.excl(yeq.sRightHead) ++ yeq.sLeft
            // have(tempAnte |- x + y === uvsum) by Cut.withParameters(toCut)(yeq, lastStep)
            // toCut = sumeq.sRightHead 
            // tempAnte = tempAnte.excl(sumeq.sRightHead) ++ sumeq.sLeft
            // have(tempAnte |- x + y === uvsum) by Cut.withParameters(toCut)(sumeq, lastStep)

            // thenHave(x + y)
            res = RB(uvsum)
          }
          // variables for last
          case x : Variable[Ind] => ???

        }
      }(res)
    }
    
    
    def evalPlus(using lib: library.type, proof: lib.Proof)(x: Biased, y: Biased): (Biased, proof.ProofTacticJudgement) = ???
    def evalInsert(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = ???
    def evalIncr(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = ???
    def evalDecr(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = ???
    def evalNeg(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = ???
    def evalNegHelper(using lib: library.type, proof: lib.Proof)(int: Biased, sign: Sign): (Biased, proof.ProofTacticJudgement) = ???
    def evalMult(using lib: library.type, proof: lib.Proof)(x: Biased, y: Biased): (Biased, proof.ProofTacticJudgement) = ???
  }


  


}