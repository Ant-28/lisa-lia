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
      assume(ring(R, <=, +, *, -, |, `0`, `1`))
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
            var temp = evalRingCutHelper(xeq, x + y === uvsum, equalities)
            have(temp._2)
            temp = evalRingCutHelper(yeq, x + y === uvsum, temp._1)
            have(temp._2)
            temp = evalRingCutHelper(sumeq, x + y === uvsum, temp._1)
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
            var temp = evalRingCutHelper(xeq, -(x) === uvneg, equalities)
            have(temp._2)
            temp = evalRingCutHelper(negeq, -(x) === uvneg, temp._1)
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
            thenHave(equalities |- x * y === uvx * uvy) by RightSubstEq.withParameters(
              Seq((x, uvx), (y, uvy)),
              (Seq(a, b), x * y === a * b)
            )
            thenHave(equalities |- x * y === uvmul) by RightSubstEq.withParameters(
              Seq((uvx * uvy, uvmul)),
              (Seq(a), x * y === a)
            )
            // WARNING: you may need val typs = SSet(x ∈ R, y ∈ R) ++ List(xeq, yeq, muleq).map(l => getTypings(l.bot.left)).fold(Set())((x, y) => x ++ y)
            // TODO: Remove first set?
            var temp = evalRingCutHelper(xeq, x * y === uvmul, equalities)
            have(temp._2)
            temp = evalRingCutHelper(yeq, x * y === uvmul, temp._1)
            have(temp._2)
            temp = evalRingCutHelper(muleq, x * y === uvmul, temp._1)
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
    
    
    def evalPlus(using lib: library.type, proof: lib.Proof)(xint: Biased, yint: Biased): (Biased, proof.ProofTacticJudgement) = {
      assume(ring(R, <=, +, *, -, |, `0`, `1`))
      var res : Biased = NRB(xint.tval)
      TacticSubproofWithResult[Biased]{
        (xint.tval, yint.tval) match {
          case (`0`, tx)  => {
            // note: can't name inputs the same as variables
            have(tx ∈ R |- `0` + tx === tx) by Tautology.from(zero_x_x of (x := tx))
            res = RB(tx)
          }
          case (tx, `0`)  => {
            // note: can't name inputs the same as variables
            have(tx ∈ R |- tx + `0` === tx) by Tautology.from(zero_x_x of (x := tx))
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
            val pprf = have(tprf) // `1` + x === tres
            val ures = tres.tval
            val typings = SSet(`1` ∈ R, tx ∈ R)
            val pprf2 = have(typings |- `1` + tx === tx + `1`) by Tautology.from(add_comm of (x := `1`, y := tx))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            // have()
            res = tres
            // TODO: eventually don't use taut? 
            have(equalities |- `1` + tx === `1` + tx) by Restate
            thenHave(equalities |- tx + `1` === `1` + tx ) by RightSubstEq.withParameters(
              Seq((`1` + tx, tx + `1`)),
              (Seq(a), a === `1` + tx)
            )
            thenHave(equalities |- tx + `1` === ures) by RightSubstEq.withParameters(
              Seq((`1` + tx, ures)),
              (Seq(a), tx + `1` === a)
            )
            var temp = evalRingCutHelper(pprf2, tx + `1` === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf, tx + `1` === ures, equalities)
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
            val pprf = have(tprf) // -`1` + x === tres
            val ures = tres.tval
            val typings = SSet(-(`1`) ∈ R, tx ∈ R)
            val pprf2 = have(typings |- -(`1`) + tx === tx + -(`1`)) by Tautology.from(add_comm of (x := -(`1`), y := tx))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |- -(`1`) + tx === -(`1`) + tx) by Restate
            thenHave(equalities |- tx + -(`1`) === -(`1`) + tx ) by RightSubstEq.withParameters(
              Seq((-(`1`) + tx, tx + -(`1`))),
              (Seq(a), a === -(`1`) + tx)
            )
            thenHave(equalities |- tx + -(`1`) === ures) by RightSubstEq.withParameters(
              Seq((-(`1`) + tx, ures)),
              (Seq(a), tx + -(`1`) === a)
            )
            var temp = evalRingCutHelper(pprf2, tx + -(`1`) === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf, tx + -(`1`) === ures, equalities)
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
            var temp = evalRingCutHelper(pprf, tx + ty === ures, equalities)
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
            var temp = evalRingCutHelper(pprf2, tx + ty === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf, tx + ty === ures, equalities)
            have(temp._2)
          } 
          case (tx + txs, ty + tys) => (tx, ty) match {
          case (`1`, -(`1`)) => {
            val (tres, tprf) = evalPlus(RB(txs), RB(tys))
            if !tprf.isValid then return (NRB(txs), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // tx + ty === tres
            val ures = tres.tval
            val typings = SSet(`1` ∈ R, tys ∈ R, txs ∈ R)
            val pprf2 = have(typings |- (`1` + txs) + (-`1` + tys) === txs + tys) by Tautology.from(addPlusHelper1g of (x := tx, y := ty, z := `1`))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |-  (`1` + txs) + (-`1` + tys) === (`1` + txs) + (-`1` + tys)) by Restate
            thenHave(equalities |- (`1` + txs) + (-`1` + tys) === tx + tys ) by RightSubstEq.withParameters(
              Seq(((`1` + txs) + (-`1` + tys), txs + tys)),
              (Seq(a), (`1` + txs) + (-`1` + tys) === a)
            )
            thenHave(equalities |- (`1` + txs) + (-`1` + tys) === ures) by RightSubstEq.withParameters(
              Seq(((`1` + txs) + (-`1` + tys), ures)),
              (Seq(a), (`1` + txs) + (-`1` + tys) === a)
            )
            var temp = evalRingCutHelper(pprf2, (`1` + txs) + (-`1` + tys) === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf, (`1` + txs) + (-`1` + tys) === ures, equalities)
            have(temp._2)
          }
          case (-(`1`), `1`) => {
            val (tres, tprf) = evalPlus(RB(txs), RB(tys))
            if !tprf.isValid then return (NRB(xint.tval), proof.InvalidProofTactic("evalPlus failed!"))
            val pprf = have(tprf) // tx + ty === tres
            val ures = tres.tval
            val typings = SSet(`1` ∈ R, tys ∈ R, txs ∈ R)
            val pprf2 = have(typings |- (`1` + txs) + (-`1` + tys) === txs + tys) by Tautology.from(addPlusHelper2g of (x := txs, y := tys, z := `1`))
            val equalities = SSet(pprf, pprf2).map(_.bot.firstElemR)
            res = tres
            have(equalities |-  (-`1` + txs) + (`1` + tys) === (-`1` + txs) + (`1` + tys)) by Restate
            thenHave(equalities |- (`1` + txs) + (-`1` + tys) === txs + tys ) by RightSubstEq.withParameters(
              Seq(((`1` + txs) + (-`1` + tys), txs + tys)),
              (Seq(a), (`1` + txs) + (-`1` + tys) === a)
            )
            thenHave(equalities |- (`1` + txs) + (-`1` + tys) === ures) by RightSubstEq.withParameters(
              Seq(((`1` + txs) + (-`1` + tys), ures)),
              (Seq(a), (`1` + txs) + (-`1` + tys) === a)
            )
            var temp = evalRingCutHelper(pprf2, (`1` + txs) + (-`1` + tys) === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf, (`1` + txs) + (-`1` + tys) === ures, equalities)
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
            var temp = evalRingCutHelper(pprf2, (tx + txs) + (ty + tys) === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf, (tx + txs) + (ty + tys) === ures, equalities)
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
            var temp = evalRingCutHelper(pprf1, (tx + txs) + (ty + tys) === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf2, (tx + txs) + (ty + tys) === ures, equalities)
            have(temp._2)
            temp = evalRingCutHelper(pprf3, (tx + txs) + (ty + tys) === ures, equalities)
            have(temp._2)
          }
            case _ => return (NRB(tx), proof.InvalidProofTactic("evalPlus failed!"))
          }
          case _ => return (NRB(xint.tval), proof.InvalidProofTactic("evalPlus failed!"))
        }
      }(res)
    }


    def evalInsert(using lib: library.type, proof: lib.Proof)(xint: Expr[Ind], yint: Expr[Ind]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
      (xint, yint) match {
        case (tx, `0`) if isVariableOrNeg(tx) => {
          res = RB(tx)
          val typings = SSet(tx ∈ R)
          have(typings |- tx + `0` === tx) by Tautology.from(x_zero_x of (x := tx))
        }
        case (tx,  ty) if isVariableOrNeg(tx) && isOneOrNegOne(ty) => {
          res = RB(ty + tx)
          val typings = SSet(tx ∈ R, ty ∈ R)
          have(typings |- tx + ty === ty + tx) by Tautology.from(add_comm of (x := tx, y := ty))
        }
        case (tx, ty)  if List(tx, ty).forall(isVariable) || List(x, y).forall(isNegVariable) => {
          (getVarName(tx), getVarName(ty)) match {
            case (zind, aind) if zind <= aind => {
              res = RB(tx + ty)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === tx + ty) by Restate
            }
            case (zind, aind) if zind > aind => {
              res = RB(ty + tx)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === ty + tx) by Tautology.from(add_comm of (x := tx, y := ty))
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case (tx, ty) if (isVariable(tx) && isNegVariable(ty)) || (isVariable(ty) && isNegVariable(tx)) => {
          (getVarName(tx), getVarName(ty)) match {
            case (zind, aind) if zind == aind => {
              if isVariable(tx) && isNegVariable(ty) then {
                res = RB(`0`)
                val typings = SSet(tx ∈ R, ty ∈ R)
                have(typings |- tx + ty === `0`) by Tautology.from(add_inv of (x := tx, y := ty))
              }
              else if isVariable(ty) && isNegVariable(tx) then {
                res = RB(`0`)
                val typings = SSet(tx ∈ R, ty ∈ R)
                have(typings |- tx + ty === `0`) by Tautology.from(add_comm_inv of (x := tx, y := ty))
              }
            }
            case (zind, aind) if zind < aind => {
              res = RB(tx + ty)
              val typings = SSet(tx ∈ R, ty ∈ R)
              have(typings |- tx + ty === tx + ty) by Restate
            }
            case (zind, aind) if zind > aind => {
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
          var temp = evalRingCutHelper(pprf1, tx + (ty + tys)  === ty + ires.tval, equalities)
          have(temp._2)
          temp = evalRingCutHelper(pprf2, tx + (ty + tys)  === ty + ires.tval, equalities)
          have(temp._2)
        }
        case (tx, ty + tys)  if List(tx, ty).forall(isVariable) || List(x, y).forall(isNegVariable) => {
          (getVarName(tx), getVarName(ty)) match {
            case (zind, aind) if zind <= aind => {
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              res = RB(tx + (ty + tys))
              have(typings |- tx + (ty + tys) === tx + (ty + tys)) by Restate
            }
            case (zind, aind) if zind > aind => {
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
              var temp = evalRingCutHelper(pprf1, tx + (ty + tys)  === ty + ires.tval, equalities)
              have(temp._2)
              temp = evalRingCutHelper(pprf2, tx + (ty + tys)  === ty + ires.tval, equalities)
              have(temp._2)
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case (tx , ty + tys) if (isVariable(tx) && isNegVariable(ty)) || (isVariable(ty) && isNegVariable(tx)) => {
          (getVarName(tx), getVarName(ty)) match {
            case (zind, aind) if zind == aind => {
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
            case (zind, aind) if zind < aind => {
              val typings = SSet(tx ∈ R, ty ∈ R, tys ∈ R)
              res = RB(tx + (ty + tys))
              have(typings |- tx + (ty + tys) === tx + (ty + tys)) by Restate
            }
            case (zind, aind) if zind > aind => {
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
              var temp = evalRingCutHelper(pprf1, tx + (ty + tys)  === ty + ires.tval, equalities)
              have(temp._2)
              temp = evalRingCutHelper(pprf2, tx + (ty + tys)  === ty + ires.tval, equalities)
              have(temp._2)
            }
            case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
          }
        }
        case _ => return (NRB(xint), proof.InvalidProofTactic("evalPlus failed!"))
        }
      }(res)
    }
    def evalIncr(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
      int match
        case RB(tx) => tx match {
          case -(`1`) => {
            res = RB(`0`)
            val typings = SSet(`1` ∈ R)
            have(typings |- `1` + -(`1`) === `0`) by Tautology.from(add_inv of (x := `1`))
          }
          case (-(`1`) + txs) => {
            res = RB(txs)
            val typings = SSet(txs ∈ R)
            have(typings |- `1` + (-(`1`) + txs) === txs) by Tautology.from(one_mone_xs_xs of (x := txs))
          }
          case (txs) => {
            res = RB(`1` + txs)
            val typings = SSet(txs ∈ R)
            have(typings |- `1` + txs === `1` + txs) by Restate
          }
        }
        case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalIncr failed!"))
      }(res)
    }
    def evalDecr(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
      int match
        case RB(tx) => tx match {
          case `1` => {
            res = RB(`0`)
            val typings = SSet(`1` ∈ R)
            have(typings |- -(`1`) + `1` === `0`) by Tautology.from(add_comm_inv of (x := `1`))
          }
          case (`1` + txs) =>  {
            res = RB(txs)
            val typings = SSet(txs ∈ R)
            have(typings |- -(`1`) + (`1` + txs) === txs) by Tautology.from(mone_one_xs_xs of (x := txs))
          }
          case (txs) => {
            res = RB(-(`1`) + txs)
            val typings = SSet(txs ∈ R)
            have(typings |- -(`1`) + txs === -(`1`) + txs) by Restate
          }
        }
        case _ => return (NRB(int.tval), proof.InvalidProofTactic("evalIncr failed!"))
      }(res)
    }
    
    def evalNeg(using lib: library.type, proof: lib.Proof)(int: Biased): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
      int match
        case RB(xint) => xint match {
          case `0` => ???
          case tx if isOne(tx) || isVariable(tx) => ???
          case tx if isNegOne(tx) || isNegVariable(tx) => ???
          case (tx + txs) => tx match {
            case `1` => ???
            case (-(`1`)) => ???
            case tx if isVariableOrNeg(tx) => ???
            case _ => ???
          }
          case _ => ???
        }
        case _ => ???
      }(res)
    }
    def evalNegHelper(using lib: library.type, proof: lib.Proof)(sign: Sign, int: Expr[Ind]): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
        (sign, int) match {
          case (_, tx) if isVariableOrNeg(tx) => ???
          case (_, tx + txs) if isVariableOrNeg(tx) => ???
          case (Pos, `1`) => ???
          case (Pos, `1` + txs) => ???
          case (Neg, -(`1`)) => ???
          case (Neg, -(`1`) + txs) => ???
          case _ => ??? 
        }
      }(res)
    }
    def evalMult(using lib: library.type, proof: lib.Proof)(xint: Biased, yint: Biased): (Biased, proof.ProofTacticJudgement) = {
      var res : Biased = NRB(`0`)
      TacticSubproofWithResult[Biased]{
        (xint, yint) match {
          case (RB(xi), RB(yi)) => (xi, yi) match {
            case (`0`, ty) => ???
            case (tx, `0`) => ???
            case (`1`, ty) => ???
            case (tx, `1`) => ???
            case (`-`(`1`), ty) => ???
            case (tx, `-`(`1`)) => ???
            case (tx + txs, ty) => ???
            case _ => ???
          }
          case _ => ???
        }
      }(res)
    }
  }


  


}