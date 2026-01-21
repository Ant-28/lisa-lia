// Eq Reasoning 
// equational reasoning, with Main.hs as a reference point
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import SubProofWithRes.TacticSubproofWithResult
import scala.collection.immutable.{Set => SSet}
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.{*, given}
import scala.quoted.quotes
import scala.quoted.{Expr => EExpr, Quotes  }
import scala.math.Ordering
import lisa.utils.prooflib.Library
import scala.collection.SortedSet
import scala.collection.SeqView.Sorted


object EqReasoning extends lisa.Main {
    import RingStructure.{*}
    import Utils.{*, given Ordering[?]}
    // RB-trees: an ex
    sealed trait Biased(treeval: Expr[Ind]) {
      def tval = treeval
    }
    case class RB(treeval: Expr[Ind]) extends Biased(treeval) {
      // def treeval : Expr[Ind] = this.treeval
    }
    case class NRB(treeval: Expr[Ind]) extends Biased(treeval) {
      // def treeval : Expr[Ind] = this.treeval
    }

    def unapply(x: Biased): Expr[Ind] = x match
        case RB(xs)  => xs
        case NRB(xs) => xs


    object inSet extends ProofTactic {
      def from(using lib: library.type, proof: lib.Proof)(premises: proof.Fact*)(bot: Sequent) = ???
    }

    object evalRingEq extends ProofTactic {
    
    def apply(using lib: library.type, proof: lib.Proof)(goal: Sequent)(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      // given myOrdering : Ordering[proof.InstantiatedFact | proof.ProofStep]{
      //     def compare(x: proof.InstantiatedFact | proof.ProofStep, y: proof.InstantiatedFact | proof.ProofStep): Int = {
      //         val IOrder = summon[Ordering[Int]]
      //         (x: @unchecked) match {
      //             case tx : Library#Proof#InnerProof#InstantiatedFact => {
      //                 (y: @unchecked) match {
      //                     case ty : Library#Proof#InnerProof#InstantiatedFact => IOrder.compare(treeDepth(getTypingVarsInAnte(tx.result.right).head), 
      //                                         treeDepth(getTypingVarsInAnte(ty.result.right).head))
                          
      //                     case ty : Library#Proof#InnerProof#ProofStep => IOrder.compare(treeDepth(getTypingVarsInAnte(tx.result.right).head), 
      //                                         treeDepth(getTypingVarsInAnte(ty.bot.right).head))
      //                 }
      //             }
      //             case tx : Library#Proof#InnerProof#ProofStep => {
      //                 (y: @unchecked) match {
      //                     case ty : Library#Proof#InnerProof#InstantiatedFact => IOrder.compare(treeDepth(getTypingVarsInAnte(tx.bot.right).head), 
      //                                         treeDepth(getTypingVarsInAnte(ty.result.right).head))
                          
      //                     case ty : Library#Proof#InnerProof#ProofStep => IOrder.compare(treeDepth(getTypingVarsInAnte(tx.bot.right).head), 
      //                                         treeDepth(getTypingVarsInAnte(ty.bot.right).head))
      //                 }
      //             }
      //         }
      //     }
      // }

      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          assume(ring(R, <=, +, *, -, |, 0, 1))
          if (!is_eq(goalElem)) then return proof.InvalidProofTactic("I can't prove anything other than equality!")
          else
            val sol = simplify(goalElem)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking sums failed!")
            else
              val hprf = have(sol)
              println("thing to cut")
              println(hprf.bot)
              val typing = typeChecking(getTypingVarsInAnte(have(sol).bot.left))
              println("unsorted")
              typing.map(x => {
                x match {
                  case x : Library#Proof#InnerProof#ProofStep => {
                    println("proofstep")
                    println(x.bot)
                    println(x.bot.firstElemR)}
                  case x : Library#Proof#InnerProof#InstantiatedFact => {
                    println("instfact")
                    println(x.result)
                    println(x.result.firstElemR)}
                }
              })
              val typing2 = typing.map(_.asInstanceOf[proof.InstantiatedFact | proof.ProofStep])
              println("typing2")
              typing2.map(x => {
                x match {
                  case x : Library#Proof#InnerProof#ProofStep => {
                    println("proofstep")
                    println(x.bot)
                    println(x.bot.firstElemR)}
                  case x : Library#Proof#InnerProof#InstantiatedFact => {
                    println("instfact")
                    println(x.result)
                    println(x.result.firstElemR)}
                }
              })
              println("end typing2")
              
              // val foo = SortedSet(typing.map(_.asInstanceOf[proof.InstantiatedFact | proof.ProofStep]).toSeq*)(using summon[Ordering[proof.InstantiatedFact | proof.ProofStep]])
              // println(foo)
              // println("sorted")
              // foo.map(x => {
              //   x match {
              //     case x : Library#Proof#InnerProof#ProofStep => {
              //       println("proofstep")
              //       println(x.bot)
              //       println(x.bot.firstElemR)}
              //     case x : Library#Proof#InnerProof#InstantiatedFact => {
              //       println("instfact")
              //       println(x.result)
              //       println(x.result.firstElemR)}
              //   }
              // })

              
      
              println("lengths")
              // println(foo.size)
              println(typing.size)
              println(typing2.size)
              println(typing.toList.sortBy(proofStepDepth).size)
              // val foo2 = SortedSet[proof.InstantiatedFact | proof.ProofStep]() ++ typing
              // println(foo2.size)
              val seqs = typing + have(sol)
              // TODO: Use cuts instead
              have(goal) by Tautology.from(seqs.toSeq*)
        }
    }


    def simplify(using lib: library.type, proof: lib.Proof)(goal: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = 
      {assume(ring(R, <=, +, *, -, |, 0, 1))
      TacticSubproof {
        goal match 
          case x `equality` y => {
            val (xval, xprf) = evalRing(x)
            if !xprf.isValid then return proof.InvalidProofTactic("simplify failed!")
            val (yval, yprf) = evalRing(y)
            if !yprf.isValid then return proof.InvalidProofTactic("simplify failed!")
            val (uvx, uvy) = (xval, yval).map[[t] =>> Expr[Ind]]([t] => x => unapply(x.asInstanceOf[Biased]))
            val (xeq, yeq) = (have(xprf), have(yprf))
            var equalities = SSet(xeq, yeq).map(_.bot.firstElemR)
            have(equalities |- uvx === uvy) by Restate 
            thenHave(equalities |- x === y) by RightSubstEq.withParameters(
              Seq((uvx, x), (uvy, y)),
              (Seq(a, b), a === b)
            )
        
            // WARNING: you may need val typs = SSet(x ∈ R, y ∈ R) ++ List(xeq, yeq, sumeq).map(l => getTypings(l.bot.left)).fold(Set())((x, y) => x ++ y)
            // TODO: Remove first set?
            var temp = evalRingCutHelper(xeq, x === y, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(yeq, x === y, temp._1, lastStep)
            have(temp._2)
          }
          case _ => return proof.InvalidProofTactic("Can only solve inequalities")
      }}
    
      

    def evalRing(using lib: library.type, proof: lib.Proof)(int: Expr[Ind])(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      assume(ring(R, <=, +, *, -, |, 0, 1))
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
        int match {
          case `0` => {
            have(0 === 0) by Restate
            res = RB(0)
          }
          case `1` => {
            have(1 === 1) by Restate
            res = RB(1)
          }
          case x + y => {
            val (vx, px) = evalRing(x)
            val (vy, py) = evalRing(y)
            if(!px.isValid || !py.isValid) // early exit
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
              Seq((uvx + uvy, uvsum)),
              (Seq(a), x + y === a)

            )
            // WARNING: you may need val typs = SSet(x ∈ R, y ∈ R) ++ List(xeq, yeq, sumeq).map(l => getTypings(l.bot.left)).fold(Set())((x, y) => x ++ y)
            // TODO: Remove first set?
            var temp = evalRingCutHelper(xeq, x + y === uvsum, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(yeq, x + y === uvsum, temp._1, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(sumeq, x + y === uvsum, temp._1, lastStep)
            have(temp._2)
            // thenHave(x + y)
            res = RB(uvsum)
          }
          // TODO: Check -(x) and x * y, the code is copypasted from the + case
          case -(x) => {
            val (vx, px) = evalRing(x)
            if(!px.isValid) // early exit
            then return (NRB(x), proof.InvalidProofTactic("evalRing failed!"))
            val (vneg, pneg) = evalNeg(vx)
            if(!pneg.isValid) then return (NRB(x), proof.InvalidProofTactic("evalNeg failed!"))
            val (uvx, uvneg) = (vx, vneg).map[[t] =>> Expr[Ind]]([t] => x => unapply(x.asInstanceOf[Biased]))
            val (xeq, negeq) = (have(px), have(pneg))
            var equalities = SSet(xeq, negeq).map(_.bot.firstElemR)
            have(equalities |- -(x) === -(x)) by Restate 
            thenHave(equalities |- -(x) === uvx) by RightSubstEq.withParameters(
              Seq((-(x), uvx)),
              (Seq(a), -(x) === a)
            )
            thenHave(equalities |- -(x) === uvneg) by RightSubstEq.withParameters(
              Seq((uvx, uvneg)),
              (Seq(a), -(x) === a)
            )
            // WARNING: you may need val typs = SSet(x ∈ R, y ∈ R) ++ List(xeq, yeq, sumeq).map(l => getTypings(l.bot.left)).fold(Set())((x, y) => x ++ y)
            // TODO: Remove first set?
            var temp = evalRingCutHelper(xeq, -(x) === uvneg, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(negeq, -(x) === uvneg, temp._1, lastStep)
            have(temp._2)
            res = RB(uvneg)
          }
          // TODO: refactor into binary + case? 
          case x * y => {
            val (vx, px) = evalRing(x)
            val (vy, py) = evalRing(y)
            if(!px.isValid || !py.isValid) // early exit
            then return (NRB(x), proof.InvalidProofTactic("evalRing failed!"))
            val (vmul, pmul) = evalMult(vx, vy)
            if(!pmul.isValid) then return (NRB(x), proof.InvalidProofTactic("evalMult failed!"))
            val (uvx, uvy, uvmul) = (vx, vy, vmul).map[[t] =>> Expr[Ind]]([t] => x => unapply(x.asInstanceOf[Biased]))
            val (xeq, yeq, muleq) = (have(px), have(py), have(pmul))
            var equalities = SSet(xeq, yeq, muleq).map(_.bot.firstElemR)
            have(equalities |- x * y === x * y) by Restate 
            thenHave(equalities |- x * y === uvx * y) by RightSubstEq.withParameters(
              Seq((x, uvx)),
              (Seq(a), x * y === a * y)
            )
            thenHave(equalities |- x * y === uvx * uvy) by RightSubstEq.withParameters(
              Seq((y, uvy)),
              (Seq(a), x * y === uvx * a)
            )
            println(uvx * uvy === uvmul)
            thenHave(equalities |- x * y === uvmul) by RightSubstEq.withParameters(
              Seq((((uvx) * (uvy)), uvmul)),
              (Seq(a), x * y === a)
            )
            // WARNING: you may need val typs = SSet(x ∈ R, y ∈ R) ++ List(xeq, yeq, muleq).map(l => getTypings(l.bot.left)).fold(Set())((x, y) => x ++ y)
            // TODO: Remove first set?
            var temp = evalRingCutHelper(xeq, x * y === uvmul, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(yeq, x * y === uvmul, temp._1, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(muleq, x * y === uvmul, temp._1, lastStep)
            have(temp._2)
            // thenHave(x + y)
            res = RB(uvmul)
          }
          // variables for last
          case x : Variable[Ind] => have(x === x) by Restate
          case _ => return (NRB(int), proof.InvalidProofTactic("Not a Ring Element? evalRing Failed!"))
        }
      }(res)
    }
    
    
    def evalPlus(using lib: library.type, proof: lib.Proof)(xint: Biased, yint: Biased)(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      assume(ring(R, <=, +, *, -, |, 0, 1))
      var res : Biased = NRB(xint.tval)
      TacticSubproofWithResult[Biased]{
        (xint.tval, yint.tval) match {
          case (`0`, tx)  => {
            // note: can't name inputs the same as variables
            have(tx ∈ R |- 0 + tx === tx) by Tautology.from(zero_x_x of (x := tx))
            res = RB(tx)
          }
          case (tx, `0`)  => {
            // note: can't name inputs the same as variables
            have(tx ∈ R |- tx + 0 === tx) by Tautology.from(x_zero_x of (x := tx))
            res = RB(tx)
          }
          case (`1`, tx) => {
            val (tres, tprf) = evalIncr(RB(tx))
            if !tprf.isValid then return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
            have(tprf) // 1 + tx === tprf
            res = tres
          }
          case (tx, `1`) => {
            val (tres, tprf) = evalPlus(yint, xint)
            if !tprf.isValid then return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // 1 + x === tres
            val ures = tres.tval
            val typings = SSet(1 ∈ R, tx ∈ R)
            val pprf2 = have(typings |- 1 + tx === tx + 1) by Tautology.from(add_comm of (x := 1, y := tx))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            // have()
            res = tres
            // TODO: eventually don't use taut? 
            have(equalities |- 1 + tx === 1 + tx) by Restate
            thenHave(equalities |- tx + 1 === 1 + tx ) by RightSubstEq.withParameters(
              Seq((1 + tx, tx + 1)),
              (Seq(a), a === 1 + tx)
            )
            thenHave(equalities |- tx + 1 === ures) by RightSubstEq.withParameters(
              Seq((1 + tx, ures)),
              (Seq(a), tx + 1 === a)
            )
            var temp = evalRingCutHelper(pprf2, tx + 1 === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, tx + 1 === ures, temp._1, lastStep)
            have(temp._2)
          }
          case (-(`1`), tx) => {
            val (tres, tprf) = evalDecr(RB(tx))
            if !tprf.isValid then return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
            have(tprf) // 1 + tx === tprf
            res = tres
          }
          case (tx, -(`1`)) => {
            val (tres, tprf) = evalPlus(yint, xint)
            if !tprf.isValid then return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // -1 + x === tres
            val ures = tres.tval
            val typings = SSet(-(1) ∈ R, tx ∈ R)
            val pprf2 = have(typings |- -(1) + tx === tx + -(1)) by Tautology.from(add_comm of (x := -(1), y := tx))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |- -(1) + tx === -(1) + tx) by Restate
            thenHave(equalities |- tx + -(1) === -(1) + tx ) by RightSubstEq.withParameters(
              Seq((-(1) + tx, tx + -(1))),
              (Seq(a), a === -(1) + tx)
            )
            thenHave(equalities |- tx + -(1) === ures) by RightSubstEq.withParameters(
              Seq((-(1) + tx, ures)),
              (Seq(a), tx + -(1) === a)
            )
            var temp = evalRingCutHelper(pprf2, tx + -(1) === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, tx + -(1) === ures, temp._1, lastStep)
            have(temp._2)
          }
          case (tx, ty) if isVariableOrNeg(tx) => {
            // x + y === res
            val (ires, iprf) = evalInsert(tx, ty)
            if !iprf.isValid then return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(iprf) 
            val ures = ires.tval
            val equalities = SSet(pprf).map(_.bot.firstElemR)
            // have()
            res = ires
            // TODO: eventually don't use taut? 
            have(equalities |- tx + ty === tx + ty) by Restate
            thenHave(equalities |- tx + ty === ures) by RightSubstEq.withParameters(
              Seq((tx + ty, ures)),
              (Seq(a), tx + ty === a)
            )
            var temp = evalRingCutHelper(pprf, tx + ty === ures, equalities, lastStep)
            have(temp._2)
          }
          case (tx, ty) if isVariableOrNeg(ty) => {
            val (ires, iprf) = evalInsert(ty, tx)
            if !iprf.isValid then return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(iprf) // ty + tx = ures
            val ures = ires.tval
            val typings = SSet(ty ∈ R, tx ∈ R)
            val pprf2 = have(typings |- ty + tx === tx + ty) by Tautology.from(add_comm of (x := ty, y := tx))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = ires
            have(equalities |- ty + tx === ty + tx) by Restate
            thenHave(equalities |- tx + ty === ty + tx ) by RightSubstEq.withParameters(
              Seq((ty + tx, tx + ty)),
              (Seq(a), a === ty + tx)
            )
            thenHave(equalities |- tx + ty === ures) by RightSubstEq.withParameters(
              Seq((ty + tx, ures)),
              (Seq(a), tx + ty === a)
            )
            var temp = evalRingCutHelper(pprf2, tx + ty === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, tx + ty === ures, temp._1, lastStep)
            have(temp._2)
          } 
          case (tx + txs, ty + tys) => (tx, ty) match {
          case (`1`, -(`1`)) => {
            val (tres, tprf) = evalPlus(RB(txs), RB(tys))
            if !tprf.isValid then return (NRB(txs), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // tx + ty === tres
            val ures = tres.tval
            val typings = SSet(1 ∈ R, tys ∈ R, txs ∈ R)
            val pprf2 = have(typings |- (1 + txs) + (-1 + tys) === txs + tys) by Tautology.from(addPlusHelper1g of (x := tx, y := ty, z := 1))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |-  (1 + txs) + (-1 + tys) === (1 + txs) + (-1 + tys)) by Restate
            thenHave(equalities |- (1 + txs) + (-1 + tys) === tx + tys ) by RightSubstEq.withParameters(
              Seq(((1 + txs) + (-1 + tys), txs + tys)),
              (Seq(a), (1 + txs) + (-1 + tys) === a)
            )
            thenHave(equalities |- (1 + txs) + (-1 + tys) === ures) by RightSubstEq.withParameters(
              Seq(((1 + txs) + (-1 + tys), ures)),
              (Seq(a), (1 + txs) + (-1 + tys) === a)
            )
            var temp = evalRingCutHelper(pprf2, (1 + txs) + (-1 + tys) === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, (1 + txs) + (-1 + tys) === ures, temp._1, lastStep)
            have(temp._2)
          }
          case (-(`1`), `1`) => {
            val (tres, tprf) = evalPlus(RB(txs), RB(tys))
            if !tprf.isValid then return (NRB(xint.tval), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // tx + ty === tres
            val ures = tres.tval
            val typings = SSet(1 ∈ R, tys ∈ R, txs ∈ R)
            val pprf2 = have(typings |- (1 + txs) + (-1 + tys) === txs + tys) by Tautology.from(addPlusHelper2g of (x := txs, y := tys, z := 1))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |-  (-1 + txs) + (1 + tys) === (-1 + txs) + (1 + tys)) by Restate
            thenHave(equalities |- (1 + txs) + (-1 + tys) === txs + tys ) by RightSubstEq.withParameters(
              Seq(((1 + txs) + (-1 + tys), txs + tys)),
              (Seq(a), (1 + txs) + (-1 + tys) === a)
            )
            thenHave(equalities |- (1 + txs) + (-1 + tys) === ures) by RightSubstEq.withParameters(
              Seq(((1 + txs) + (-1 + tys), ures)),
              (Seq(a), (1 + txs) + (-1 + tys) === a)
            )
            var temp = evalRingCutHelper(pprf2, (1 + txs) + (-1 + tys) === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, (1 + txs) + (-1 + tys) === ures, temp._1, lastStep)
            have(temp._2)
          }
          case (tx, ty) if isOneOrNegOne(tx) => {
            // tx + txs + ty + tys = txs + tx + ty + tys. 
            val (tres, tprf) = evalPlus(RB(txs), RB(tx + (ty + tys)))
            if !tprf.isValid then return (NRB(txs), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // txs + tys === tres
            val ures = tres.tval
            val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R, txs ∈ R)
            val pprf2 = have(typings |- (tx + txs) + (ty + tys) === txs + (tx + (ty + tys))) by Tautology.from(addPlusHelper3p of (x := txs, y := tys, z := tx, w := ty))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |-  (tx + txs) + (ty + tys) === (tx + txs) + (ty + tys)) by Restate
            thenHave(equalities |- (tx + txs) + (ty + tys) === txs + (tx + (ty + tys)) ) by RightSubstEq.withParameters(
              Seq(((tx + txs) + (ty + tys), txs + (tx + (ty + tys)))),
              (Seq(a), (tx + txs) + (ty + tys) === a)
            )
            thenHave(equalities |- (tx + txs) + (ty + tys) === ures) by RightSubstEq.withParameters(
              Seq((txs + (tx + (ty + tys)), ures)),
              (Seq(a), (tx + txs) + (ty + tys) === a)
            )
            var temp = evalRingCutHelper(pprf2, (tx + txs) + (ty + tys) === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, (tx + txs) + (ty + tys) === ures, temp._1, lastStep)
            have(temp._2)
          }
          case (tx, ty) if isVariableOrNeg(tx) => {
            // tx + txs + ty + tys = txs + tx + ty + tys. 
            val (vres, vprf) = evalInsert(tx, ty + tys)
            // tx + (ty + tys) = vres
            if !vprf.isValid then return (NRB(txs), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf1 = have(vprf)
            val (tres, tprf) = evalPlus(RB(txs), vres)
            // tx + txs + ty + tys = txs + vres = tres
            if !tprf.isValid then return (NRB(txs), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf2 = have(tprf) // txs + tys === tres
            val ures = tres.tval
            val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R, txs ∈ R)
            val pprf3 = have(typings |- (tx + txs) + (ty + tys) === txs + (tx + (ty + tys))) by Tautology.from(addPlusHelper3p of (x := txs, y := tys, z := tx, w := ty))
            val equalities = SSet(pprf1, pprf2, pprf3).map(_.bot.firstElemR)
            res = tres
            have(equalities |-  (tx + txs) + (ty + tys) === (tx + txs) + (ty + tys)) by Restate
            thenHave(equalities |- (tx + txs) + (ty + tys) === txs + (tx + (ty + tys)) ) by RightSubstEq.withParameters(
              Seq(((tx + txs) + (ty + tys), txs + (tx + (ty + tys)))),
              (Seq(a), (tx + txs) + (ty + tys) === a)
            )
            thenHave(equalities |- (tx + txs) + (ty + tys) === txs + vres.tval) by RightSubstEq.withParameters(
              Seq((tx + (ty + tys), vres.tval)),
              (Seq(a), (tx + txs) + (ty + tys) === txs + a)
            )
            thenHave(equalities |- (tx + txs) + (ty + tys) === ures) by RightSubstEq.withParameters(
              Seq((txs + vres.tval, ures)),
              (Seq(a), (tx + txs) + (ty + tys) === a)
            )
            var temp = evalRingCutHelper(pprf1, (tx + txs) + (ty + tys) === ures, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf2, (tx + txs) + (ty + tys) === ures, temp._1, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf3, (tx + txs) + (ty + tys) === ures, temp._1, lastStep)
            have(temp._2)
          }
            case _ => return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
          }
          case _ => return (NRB(xint.tval), proof.InvalidProofTactic("evalPlus failed!"))
        }
      }(res)
    }


    def evalInsert(using lib: library.type, proof: lib.Proof)(xint: Expr[Ind], yint: Expr[Ind])(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
      (xint, yint) match {
        case (tx, `0`) if isVariableOrNeg(tx) => {
          res = RB(tx)
          val typings = SSet(tx ∈ R)
          have(typings |- tx + 0 === tx) by Tautology.from(x_zero_x of (x := tx))
        }
        case (tx,  ty) if isVariableOrNeg(tx) && isOneOrNegOne(ty) => {
          res = RB(ty + tx)
          val typings = SSet(tx ∈ R, ty ∈ R)
          have(typings |- tx + ty === ty + tx) by Tautology.from(add_comm of (x := tx, y := ty))
        }
        case (tx, ty)  if List(tx, ty).forall(isVariable) || List(x, y).forall(isNegVariable) => {
          myOrd.compare(tx, ty)  match {
            case tcomp  if tcomp <= 0 => {
              res = RB(tx + ty)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === tx + ty) by Restate
            }
            case tcomp if tcomp > 0 => {
              res = RB(ty + tx)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === ty + tx) by Tautology.from(add_comm of (x := tx, y := ty))
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case (tx, ty) if (isVariable(tx) && isNegVariable(ty)) || (isVariable(ty) && isNegVariable(tx)) => {
          // sort by quantifier order
          // given Ordering 
          
            myOrd.compare(tx, ty) match {
            case tcomp if tcomp == 0 => {
              if isVariable(tx) && isNegVariable(ty) then {
                res = RB(0)
                val typings = SSet(tx ∈ R, ty ∈ R)
                have(typings |- tx + ty === 0) by Tautology.from(add_inv of (x := tx, y := ty))
              }
              else if isVariable(ty) && isNegVariable(tx) then {
                res = RB(0)
                val typings = SSet(tx ∈ R, ty ∈ R)
                have(typings |- tx + ty === 0) by Tautology.from(add_comm_inv of (x := tx, y := ty))
              }
            }
            case tcomp if tcomp < 0 => {
              res = RB(tx + ty)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === tx + ty) by Restate
            }
            case tcomp if tcomp > 0  => {
              res = RB(ty + tx)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === ty + tx) by Tautology.from(add_comm of (x := tx, y := ty))
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case (tx, ty + tys) if (isVariableOrNeg(tx) && isOneOrNegOne(ty)) => {
          val (ires, iprf) = evalInsert(tx, tys) // tx + tys === ires
          val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
          val pprf1 = have(iprf)
          res = RB(ty + ires.tval)
          // it's at most 3-4 atoms so using Taut should be ok
          val pprf2 = have(typings |- tx + (ty + tys) === ty + (tx + tys)) by Tautology.from(addInsertHelper of (x := tx, y := ty, z := tys))
          val equalities = SSet(pprf1, pprf2).map(_.bot.firstElemR)
          have(equalities |-  tx + (ty + tys) === tx + (ty + tys)) by Restate
          thenHave(equalities |- tx + (ty + tys) ===  ty + (tx + tys)) by RightSubstEq.withParameters(
            Seq((tx + (ty + tys), ty + (tx + tys))),
            (Seq(a), tx + (ty + tys) === a)
          )
          thenHave(equalities |- tx + (ty + tys) === ty + ires.tval) by RightSubstEq.withParameters(
            Seq((tx + tys, ires.tval)),
            (Seq(a), (tx + (ty + tys) === ty + a))
          )
          var temp = evalRingCutHelper(pprf1, tx + (ty + tys)  === ty + ires.tval, equalities, lastStep)
          have(temp._2)
          temp = evalRingCutHelper(pprf2, tx + (ty + tys)  === ty + ires.tval, temp._1, lastStep)
          have(temp._2)
        }
        case (tx, ty + tys)  if List(tx, ty).forall(isVariable) || List(x, y).forall(isNegVariable) => {
          myOrd.compare(tx, ty) match {
            case tcomp if tcomp <= 0 => {
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              res = RB(tx + (ty + tys))
              have(typings |- tx + (ty + tys) === tx + (ty + tys)) by Restate
            }
            case tcomp if tcomp > 0 => {
              val (ires, iprf) = evalInsert(tx, tys) // tx + tys === ires
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              val pprf1 = have(iprf)
              res = RB(ty + ires.tval)
              // it's at most 3-4 atoms so using Taut should be ok
              val pprf2 = have(typings |- tx + (ty + tys) === ty + (tx + tys)) by Tautology.from(addInsertHelper of (x := tx, y := ty, z := tys))
              val equalities = SSet(pprf1, pprf2).map(_.bot.firstElemR)
              have(equalities |-  tx + (ty + tys) === tx + (ty + tys)) by Restate
              thenHave(equalities |- tx + (ty + tys) ===  ty + (tx + tys)) by RightSubstEq.withParameters(
                Seq((tx + (ty + tys), ty + (tx + tys))),
                (Seq(a), tx + (ty + tys) === a)
              )
              thenHave(equalities |- tx + (ty + tys) === ty + ires.tval) by RightSubstEq.withParameters(
                Seq((tx + tys, ires.tval)),
                (Seq(a), (tx + (ty + tys) === ty + a))
              )
              var temp = evalRingCutHelper(pprf1, tx + (ty + tys)  === ty + ires.tval, equalities, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf2, tx + (ty + tys)  === ty + ires.tval, temp._1, lastStep)
              have(temp._2)
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case (tx , ty + tys) if (isVariable(tx) && isNegVariable(ty)) || (isVariable(ty) && isNegVariable(tx)) => {
          myOrd.compare(tx, ty) match {
            case tcomp if tcomp == 0 => {
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              res = RB(tys)
              if isVariable(tx) && isNegVariable(ty) then {
                val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
                have(typings |- tx + (ty + tys) === tys) by Tautology.from(z_mz_x_x of (z := tx, x := tys))
              }
              else if isVariable(ty) && isNegVariable(tx) then {
                val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
                have(typings |- tx + (ty + tys) === tys) by Tautology.from(mz_z_x_x of (z := tx, x := tys))
              }
            }
            case tcomp if tcomp < 0 => {
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              res = RB(tx + (ty + tys))
              have(typings |- tx + (ty + tys) === tx + (ty + tys)) by Restate
            }
            case tcomp if tcomp > 0 => {
              val (ires, iprf) = evalInsert(tx, tys) // tx + tys === ires
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              val pprf1 = have(iprf)
              res = RB(ty + ires.tval)
              // it's at most 3-4 atoms so using Taut should be ok
              val pprf2 = have(typings |- tx + (ty + tys) === ty + (tx + tys)) by Tautology.from(addInsertHelper of (x := tx, y := ty, z := tys))
              val equalities = SSet(pprf1, pprf2).map(_.bot.firstElemR)
              have(equalities |-  tx + (ty + tys) === tx + (ty + tys)) by Restate
              thenHave(equalities |- tx + (ty + tys) ===  ty + (tx + tys)) by RightSubstEq.withParameters(
                Seq((tx + (ty + tys), ty + (tx + tys))),
                (Seq(a), tx + (ty + tys) === a)
              )
              thenHave(equalities |- tx + (ty + tys) === ty + ires.tval) by RightSubstEq.withParameters(
                Seq((tx + tys, ires.tval)),
                (Seq(a), (tx + (ty + tys) === ty + a))
              )
              var temp = evalRingCutHelper(pprf1, tx + (ty + tys)  === ty + ires.tval, equalities, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf2, tx + (ty + tys)  === ty + ires.tval, temp._1, lastStep)
              have(temp._2)
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
        }
      }(res)
    }
    def evalIncr(using lib: library.type, proof: lib.Proof)(int: Biased)(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
      int match
        case RB(tx) => tx match {
          case -(`1`) => {
            res = RB(0)
            val typings = SSet(1 ∈ R)
            have(typings |- 1 + -(1) === 0) by Tautology.from(add_inv of (x := 1))
          }
          case (-(`1`) + txs) => {
            res = RB(txs)
            val typings = SSet(txs ∈ R)
            have(typings |- 1 + (-(1) + txs) === txs) by Tautology.from(one_mone_xs_xs of (x := txs))
          }
          case (txs) => {
            res = RB(1 + txs)
            val typings = SSet(txs ∈ R)
            have(typings |- 1 + txs === 1 + txs) by Restate
          }
        }
        case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalIncr failed!"))
      }(res)
    }
    def evalDecr(using lib: library.type, proof: lib.Proof)(int: Biased)(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
      int match
        case RB(tx) => tx match {
          case `1` => {
            res = RB(0)
            val typings = SSet(1 ∈ R)
            have(typings |- -(1) + 1 === 0) by Tautology.from(add_comm_inv of (x := 1))
          }
          case (`1` + txs) =>  {
            res = RB(txs)
            val typings = SSet(txs ∈ R)
            have(typings |- -(1) + (1 + txs) === txs) by Tautology.from(mone_one_xs_xs of (x := txs))
          }
          case (txs) => {
            res = RB(-(1) + txs)
            val typings = SSet(txs ∈ R)
            have(typings |- -(1) + txs === -(1) + txs) by Restate
          }
        }
        case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalIncr failed!"))
      }(res)
    }
    
    def evalNeg(using lib: library.type, proof: lib.Proof)(int: Biased)(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
      int match
        case RB(xint) => xint match {
          case `0` => {
            res = RB(0)
            val typings = SSet(0 ∈ R)
            have(typings |- -(`0`) === 0) by Tautology.from(negation_zero)
          }
          case tx if isOne(tx) || isVariable(tx) => {
            res = RB(-tx)
            val typings = SSet(tx ∈ R)
            have(typings |- -tx === -tx) by Restate
          }
          case tx if isNegOne(tx) || isNegVariable(tx) => {
            tx match {
              case -(`1`) => {
                res = RB(1)
                val typings = SSet(1 ∈ R)
                have(typings |- -(-`1`) === 1) by Tautology.from(double_negation_elimination of (x := 1))
              }
              case -(txs) => {
                res = RB(txs)
                val typings = SSet(txs ∈ R)
                have(typings |- -(-txs) === txs) by Tautology.from(double_negation_elimination of (x := txs))
              }
              case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalNeg reached an unreachable case!"))
            }
          }
          case (tx + txs) => tx match {
            case `1` => {
              val (pres, pprf) = evalNegHelper(Pos, tx + txs) 
              if !pprf.isValid then return (NRB(int.tval), proof.InvalidProofTactic("evalNeg failed!"))  
              have(pprf)
            }
            case (-(`1`)) => {
              val (pres, pprf) = evalNegHelper(Neg, tx + txs) 
              if !pprf.isValid then return (NRB(int.tval), proof.InvalidProofTactic("evalNeg failed!"))  
              have(pprf)
            }
            case tx if isVariableOrNeg(tx) => {
              // Pos or Neg no longer matters for vars
              val (pres, pprf) = evalNegHelper(Pos, tx + txs) 
              if !pprf.isValid then return (NRB(int.tval), proof.InvalidProofTactic("evalNeg failed!"))  
              have(pprf)
            }
            case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalNeg Failed!"))
          }
          case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalNeg Failed!"))
        }
        case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalNeg Failed!"))
      }(res)
    }
    def evalNegHelper(using lib: library.type, proof: lib.Proof)(sign: Sign, int: Expr[Ind])(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
        (sign, int) match {
          case (_, tx) if isVariable(tx) => {
            res = RB(-tx)
            val typings = SSet(tx ∈ R)
            have(typings |- -tx === -tx) by Restate
          }
          case (_, tx) if isNegVariable(tx) => {
            tx match {
              case -(txs) => {
                res = RB(txs)
                val typings = SSet(txs ∈ R)
                have(typings |- -(-txs) === txs) by Tautology.from(double_negation_elimination of (x := txs))
              }
              case _ => return (NRB(int), proof.InvalidProofTactic("evalNegHelper reached an unreachable case!"))
            }
          }
          case (_, tx + txs) if isVariableOrNeg(tx) => {
            tx match {
              case tx if isVariable(tx) => {
                val (nres, nprf) = evalNegHelper(Pos, txs)
                if !nprf.isValid then return (NRB(int), proof.InvalidProofTactic("evalPlus failed!"))
                res = RB(-tx + nres.tval)
                val pprf = have(nprf) // -txs === nres.tval
                val typings = SSet(tx ∈ R, txs ∈ R)
                val pprf2 = have(typings |- -(tx + txs) === -tx + -txs) by Tautology.from(negation_dist_add of (x := tx, y := txs))
                val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
                have(equalities |- -(tx + txs)  === -(tx + txs)) by Restate
                thenHave(equalities |- -(tx + txs) === -tx + -txs) by RightSubstEq.withParameters(
                  Seq((-(tx + txs),  -tx + -txs)),
                  (Seq(a), -(tx + txs) === a)
                )
                thenHave(equalities |- -(tx + txs) === -tx + nres.tval) by RightSubstEq.withParameters(
                  Seq((-txs, nres.tval)),
                  (Seq(a), -(tx + txs) === -tx + a)
                )
                var temp = evalRingCutHelper(pprf2, -(tx + txs) === -tx + nres.tval, equalities, lastStep)
                have(temp._2)
                temp = evalRingCutHelper(pprf, -(tx + txs) === -tx + nres.tval, temp._1, lastStep)
                have(temp._2)
              }
              case -(txp) if isNegVariable(tx) => {
                val (nres, nprf) = evalNegHelper(Pos, txs)
                if !nprf.isValid then return (NRB(int), proof.InvalidProofTactic("evalPlus failed!"))
                res = RB(txp + nres.tval)
                val pprf = have(nprf) // -txs === nres.tval
                val typings = SSet(tx ∈ R, txs ∈ R, txp ∈ R)
                val pprf2 = have(typings |- -(tx + txs) === -tx + -txs) by Tautology.from(negation_dist_add of (x := tx, y := txs))
                val pprf3 = have(typings |- -(-txp) === txp) by Tautology.from(double_negation_elimination of (x := txp))
                val equalities = SSet(pprf, pprf2, pprf3).map(_.bot.firstElemR)
                have(equalities |- -(-txp + txs)  === -(-txp + txs)) by Restate
                thenHave(equalities |- -(-txp + txs) === -(-txp) + -txs) by RightSubstEq.withParameters(
                  Seq((-(-txp + txs),  -(-txp) + -txs)),
                  (Seq(a), -(-txp + txs) === a)
                )
                thenHave(equalities |- -((-txp) + txs) === -(-txp) + nres.tval) by RightSubstEq.withParameters(
                  Seq((-txs, nres.tval)),
                  (Seq(a), -((-txp)  + txs) === -(-txp) + a)
                )
                thenHave(equalities |- -((-txp) + txs) === txp + nres.tval) by RightSubstEq.withParameters(
                  Seq((-(-txp), txp)),
                  (Seq(a), -((-txp)  + txs) === a + nres.tval)
                )
                var temp = evalRingCutHelper(pprf2, -((-txp) + txs) === txp + nres.tval, equalities, lastStep)
                have(temp._2)
                temp = evalRingCutHelper(pprf, -((-txp) + txs) === txp + nres.tval, temp._1, lastStep)
                have(temp._2)
                temp = evalRingCutHelper(pprf3, -((-txp) + txs) === txp + nres.tval, temp._1, lastStep)
                have(temp._2)
              }
              case _ => return (NRB(int), proof.InvalidProofTactic("evalNegHelper reached an unreachable case!"))
            }
          }
          case (Pos, `1`) => {
            res = RB(-`1`)
            val typings = SSet(`1` ∈ R)
            have(typings |- -`1` === -`1`) by Restate
          }
          case (Pos, `1` + txs) => {
            val (nres, nprf) = evalNegHelper(Pos, txs)
                if !nprf.isValid then return (NRB(int), proof.InvalidProofTactic("evalPlus failed!"))
                res = RB(-1 + nres.tval)
                val pprf = have(nprf) // -txs === nres.tval
                val typings = SSet(1 ∈ R, txs ∈ R)
                val pprf2 = have(typings |- -(1 + txs) === -1 + -txs) by Tautology.from(negation_dist_add of (x := 1, y := txs))
                val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
                have(equalities |- -(1 + txs)  === -(1 + txs)) by Restate
                thenHave(equalities |- -(1 + txs) === -1 + -txs) by RightSubstEq.withParameters(
                  Seq((-(1 + txs),  -1 + -txs)),
                  (Seq(a), -(1 + txs) === a)
                )
                thenHave(equalities |- -(1 + txs) === -1 + nres.tval) by RightSubstEq.withParameters(
                  Seq((-txs, nres.tval)),
                  (Seq(a), -(1 + txs) === -1 + a)
                )
                var temp = evalRingCutHelper(pprf2, -(1 + txs) === -1 + nres.tval, equalities, lastStep)
                have(temp._2)
                temp = evalRingCutHelper(pprf, -(1 + txs) === -1 + nres.tval, temp._1, lastStep)
                have(temp._2)
          }
          case (Neg, -(`1`)) => {
            res = RB(1)
            val typings = SSet(1 ∈ R)
            have(typings |- -(-`1`) === 1) by Tautology.from(double_negation_elimination of (x := 1))
          }
          case (Neg, -(`1`) + txs) => {
            val (nres, nprf) = evalNegHelper(Neg, txs)
            if !nprf.isValid then return (NRB(int), proof.InvalidProofTactic("evalPlus failed!"))
            res = RB(1 + nres.tval)
            val pprf = have(nprf) // -txs === nres.tval
            val typings = SSet(-1 ∈ R, txs ∈ R, 1 ∈ R)
            val pprf2 = have(typings |- -(-`1` + txs) === -(-`1`) + -txs) by Tautology.from(negation_dist_add of (x := -1, y := txs))
            val pprf3 = have(typings |- -(-`1`) === 1) by Tautology.from(double_negation_elimination of (x := 1))
            val equalities = SSet(pprf, pprf2, pprf3).map(_.bot.firstElemR)
            have(equalities |- -(-1 + txs)  === -(-1 + txs)) by Restate
            thenHave(equalities |- -(-1 + txs) === -(-`1`) + -txs) by RightSubstEq.withParameters(
              Seq((-(-1 + txs),  -(-`1`) + -txs)),
              (Seq(a), -(-1 + txs) === a)
            )
            thenHave(equalities |- -((-1) + txs) === -(-`1`) + nres.tval) by RightSubstEq.withParameters(
              Seq((-txs, nres.tval)),
              (Seq(a), -((-1)  + txs) === -(-`1`) + a)
            )
            thenHave(equalities |- -((-1) + txs) === 1 + nres.tval) by RightSubstEq.withParameters(
              Seq((-(-`1`), 1)),
              (Seq(a), -((-1)  + txs) === a + nres.tval)
            )
            var temp = evalRingCutHelper(pprf2, -((-1) + txs) === 1 + nres.tval, equalities, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf, -((-1) + txs) === 1 + nres.tval, temp._1, lastStep)
            have(temp._2)
            temp = evalRingCutHelper(pprf3, -((-1) + txs) === 1 + nres.tval, temp._1, lastStep)
            have(temp._2)
          }
          case _ => return (NRB(int), proof.InvalidProofTactic("evalNegHelper failed!")) 
        }
      }(res)
    }
    
    def evalMult(using lib: library.type, proof: lib.Proof)(xint: Biased, yint: Biased)(using myOrd: Ordering[Expr[Ind]]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(0)
      TacticSubproofWithResult[Biased]{
        (xint, yint) match {
          case (RB(xi), RB(yi)) => (xi, yi) match {
            case (`0`, ty) => {
              val typings = SSet(ty ∈ R)
              res = RB(0)
              have(typings |- 0 * ty === 0) by Tautology.from(mult_zero_x_zero of (x := ty))
            }
            case (tx, `0`) => {
              val typings = SSet(tx ∈ R)
              res = RB(0)
              have(typings |- tx * 0 === 0) by Tautology.from(mult_zero_x_zero of (x := tx))
            }
            case (`1`, ty) => {
              val typings = SSet(ty ∈ R)
              res = RB(ty)
              have(typings |- 1 * ty === ty) by Tautology.from(mul_id_right of (x := ty))
            }
            case (tx, `1`) => {
              val typings = SSet(tx ∈ R)
              res = RB(tx)
              have(typings |- tx * 1 === tx) by Tautology.from(mul_id_left of (x := tx))
            }
            case (`-`(`1`), ty) => {
              val (nres, nprf) = evalNeg(RB(ty))
              if !nprf.isValid then return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!"))
              res = nres
              val pprf = have(nprf) // -txs === nres.tval
              val typings = SSet(-1 ∈ R, ty ∈ R)
              val pprf2 = have(typings |- -1 * ty === -ty) by Tautology.from(mult_neg1_x_negx of (x := ty))
  
              val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
              have(equalities |- -1 * ty  === -1 * ty) by Restate
              thenHave(equalities |- -1 * ty === -ty) by RightSubstEq.withParameters(
                Seq((-1 * ty,  -ty)),
                (Seq(a), -1 * ty === a)
              )
              thenHave(equalities |- -1 * ty === nres.tval) by RightSubstEq.withParameters(
                Seq((-ty, nres.tval)),
                (Seq(a), -1 * ty === a)
              )

              var temp = evalRingCutHelper(pprf2, -1 * ty === nres.tval, equalities, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf, -1 * ty === nres.tval, temp._1, lastStep)
              have(temp._2)
            }
            case (ty, `-`(`1`)) => {
              val (nres, nprf) = evalNeg(RB(ty))
              if !nprf.isValid then return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!"))
              res = nres
              val pprf = have(nprf) // -txs === nres.tval
              val typings = SSet(-1 ∈ R, ty ∈ R)
              val pprf2 = have(typings |- ty * -1 === -ty) by Tautology.from(mult_x_neg1_negx of (x := ty))
  
              val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
              have(equalities |- ty * -1  === ty * -1) by Restate
              thenHave(equalities |- ty * -1 === -ty) by RightSubstEq.withParameters(
                Seq((ty * -1,  -ty)),
                (Seq(a), ty * -1 === a)
              )
              thenHave(equalities |- ty * -1 === nres.tval) by RightSubstEq.withParameters(
                Seq((-ty, nres.tval)),
                (Seq(a), ty * -1 === a)
              )

              var temp = evalRingCutHelper(pprf2, ty * -1 === nres.tval, equalities, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf, ty * -1 === nres.tval, temp._1, lastStep)
              have(temp._2)
            }
            case (tx + txs, ty) => {
              val (mres1, mprf1) = evalMult(RB(tx), RB(ty))
              if !mprf1.isValid then return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!"))
              val (mres2, mprf2) = evalMult(RB(txs), RB(ty))
              if !mprf2.isValid then return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!"))
              val (mres3, mprf3) = evalPlus(mres1, mres2)
              if !mprf3.isValid then return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!"))
              val typings = SSet(tx ∈ R, txs ∈ R, ty ∈ R)
              val (pprf, pprf2, pprf3) = (have(mprf1), have(mprf2), have(mprf3))
              val pprf4 = have(typings |- (tx + txs) * ty === (tx * ty) + (txs * ty)) by Tautology.from(mul_dist_right of (y := tx, z := txs, x := ty))
              res = mres3
              val equalities = SSet(pprf, pprf2, pprf3, pprf4).map(_.bot.firstElemR)
              have(equalities |- (tx + txs) * ty  === (tx + txs) * ty) by Restate
              thenHave(equalities |- (tx + txs) * ty === (tx * ty) + (txs * ty))  by RightSubstEq.withParameters(
                Seq(((tx + txs) * ty,  (tx * ty) + (txs * ty))),
                (Seq(a), (tx + txs) * ty === a)
              )
              thenHave(equalities |- (tx + txs) * ty === mres1.tval + mres2.tval) by RightSubstEq.withParameters(
                Seq(((tx * ty), mres1.tval), ((txs * ty), mres2.tval)),
                (Seq(a, b), (tx + txs) * ty === a + b)
              )
              thenHave(equalities |- (tx + txs) * ty === mres3.tval) by RightSubstEq.withParameters(
                Seq(((mres1.tval + mres2.tval), mres3.tval)),
                (Seq(a), (tx + txs) * ty === a)
              )

              var temp = evalRingCutHelper(pprf, (tx + txs) * ty === mres3.tval, equalities, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf2, (tx + txs) * ty === mres3.tval, temp._1, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf3, (tx + txs) * ty === mres3.tval, temp._1, lastStep)
              have(temp._2)
              temp = evalRingCutHelper(pprf4, (tx + txs) * ty === mres3.tval, temp._1, lastStep)
              have(temp._2)

            } 
            case _ => return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!")) 
          }
          case _ => return (NRB(xint.tval * yint.tval), proof.InvalidProofTactic("evalMult failed!")) 
        }
      }(res)
    }
  }


  


}