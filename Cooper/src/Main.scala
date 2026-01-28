import scala.collection.immutable.{Set => SSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, P => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, *, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}
import RingStructure.{_}
import Utils.treeDepth
import RingStructure.c
import EqReasoning.evalRingEq
import scala.collection.immutable.SortedSet
import TypeChecker.typeCheck
import DivReasoning.divInts
import InEqReasoning.inEquality
import DisEqReasoning.disEquality
import InDivReasoning.inDivInts
import liaByWitness.liaByWitnessProof
// object Rings extends lisa.Main: 
//     import RingStructure.{*}
//     import RingEqReasoning.{*} 

object Rings extends lisa.Main 
{
    import Utils.{*, given Ordering[?]}
    import EqReasoning.evalRingEq.evalRing
    
    val t = variable[Ind]
    val _ = RingStructure

  

    val w : THM = RingStructure.add_closure
    // println(w.statement)
    val dummy = Theorem(ring(R, <=, <, +, *, -, |, `0`, `1`) |- `1` ∈ R) {
        have(thesis) by Restate.from(mul_id_closure)
    }

    val PropVar1 = Theorem(() |- True) {
        have(thesis) by Restate
    }
    val PropVar2 = Theorem(() |- !False) {
        have(thesis) by Restate
    }

     
    // import scala.collection.immutable.{Set => SSet}
    // val xx = variable[Ind]
    // val yy = variable[Ind]
    // val zz = variable[Ind]

    // // a predicate with one argument
    // val P = variable[Ind >>: Prop]
    // val Q = variable[Ind >>: Prop]

    // // a first-order function with one argument
    // val f = variable[Ind >>: Ind]
    // val g = variable[Ind >>: Ind]

    // val simpleTheorem = Theorem(P(xx) |- P(xx)):
    //   have(thesis) by Restate

    // val dummyTheorem = Theorem(P(xx) |- Q(xx)): proof ?=>
    //   val assumptions: Seq[proof.InstantiatedFact | proof.ProofStep] = Seq(xx, ∅, f(xx)).map: 
    //     case v: Variable[?] => have(P(v) |- Q(f(v))) by Sorry
    //     case c: Constant[?] => have(P(c) |- Q(g(c))) by Sorry
    //     case other =>  simpleTheorem of (xx := other)

    //   assumptions.foreach: a =>
    //     println(s"""
    //     | Assumption: $a
    //     | Class: ${a.getClass}
    //     | Extracted: ${proof.getSequent(a)}
    //     |""".stripMargin)

    //   sorry
    // def getTypingVarsInAnte(xx: SSet[Expr[Prop]]): SSet[Expr[Ind]] = xx
    //   .flatMap((yy) =>
    //     yy match {
    //       case ys ∈ R => SSet(ys)
    //       case _      => SSet()
    //     }
    //   )
    // def getTypings(xx: SSet[Expr[Prop]]): SSet[Expr[Prop]] = xx.filter( xs => 
    //     xs match {
    //       case p ∈ R => true
    //       case _ => false
    //     }
    //   )

    

    

    // class myProofOrdering extends Ordering[proof.InstantiatedFact | proof.ProofStep] {
    //     def compare(x: proof.InstantiatedFact | proof.ProofStep, y: proof.InstantiatedFact | proof.ProofStep): Int = {
    //         ???
    //     }
    // }
    
    val test = Theorem( (ring(R, <=, <, +, *, -, |, `0`, `1`)) |- `1` + (`1` + `1`) === (`1` + `1`) + `1`){
        assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
        val t = add_assoc of (x := `1`, y := `1`, z := `1`)
        val q = typeChecking(getTypingVarsInAnte(t.result.left))
        val r = getTypings(t.result.left)
        have(t.result)
        have(thesis) by Cut.withParameters(r.head)(q.head, t)
    }
    val tes2 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), (`1` ∈ R)) |- `1` + (`1` + `1`) === (`1` + `1`) + `1`){
        have(thesis) by Restate.from(add_assoc of (x := `1`, y := `1`, z := `1`))
    }

    // val test = -(y)
    // println(treeDepth(test))
    override def main(args: Array[String]): Unit = {
        List(RingStructure, EqReasoning, RingDivOrdering).map(_.main(args))
        super.main(args)
        // println(om.stringWriter.toString)
    }
    println("Ždravo, ja sam mićo!")

    import RingElemConversions.i
    val ringEq1 = Theorem(ring(R, <=, <, +, *, -, |, `0`, `1`) |- i(2) === i(2)){
        have(thesis) by evalRingEq.apply
    }
    val ringEq2 = Theorem(ring(R, <=, <, +, *, -, |, `0`, `1`) |- i(2) + i(2) === i(4)){
        have(thesis) by evalRingEq.apply
    }
    val ringEq3 = Theorem(ring(R, <=, <, +, *, -, |, `0`, `1`) |- i(2) * i(2) === i(4)){
        have(thesis) by evalRingEq.apply
    }
    val ringEq4 = Theorem(ring(R, <=, <, +, *, -, |, `0`, `1`) |-  i(-2) * i(2) === i(-4)){
        have(thesis) by evalRingEq.apply
    }
    val ringEq5 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |-  3*x === x + x + x){
        have(thesis) by evalRingEq.apply
    }

    val ringEq6 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |-  -3*x === -x + -x + -x){
        have(thesis) by evalRingEq.apply
    }

    val ringEq7 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |-  -(-x) === x){
        have(thesis) by evalRingEq.apply
    }
    val ringEq8 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |-  (2*x + -3*y) + z === -y + -y + -y + x + z + x){
        have(thesis) by evalRingEq.apply
    }

    val ringEq9 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |-  i(5) + i(10) === i(15)){
        have(thesis) by evalRingEq.apply
    }
    // use 100 to stress test the kernel
    val ringEq10 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- i(10) + i(10) === i(20)){
        have(thesis) by evalRingEq.apply
        // proof checking takes time (possibly)!

    }

    val ringEq11 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- x - 3 === -3 + x){
        have(thesis) by evalRingEq.apply
        // proof checking takes time (possibly)
    }
    val ringEq12 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- (x + 3)*5 === i(20) `+` -5 + 3*x + 2*x){
        have(thesis) by evalRingEq.apply
        // proof checking takes time (possibly)
    }
    val ringTyp1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |-  (-i(10) * i(10) + x) ∈ R){
        have(thesis) by typeCheck.apply
    }

    val ringDiv1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- (10 | i(20))){
        have(thesis) by divInts.apply
    }

    val ringInEq1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- 0 <= `1`){
        have(thesis) by inEquality.apply
    }

    val ringInEq2 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- `0` <= 2){
        have(thesis) by inEquality.apply
    }

    val ringInEq3 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- `0` <= 0){
        have(thesis) by inEquality.apply
    }

    val ringInEq4 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- x <= x){
        have(thesis) by inEquality.apply
    }
    val ringInEq5 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- -2 <= `0`){
        have(thesis) by inEquality.apply
    }

    val ringInEq6 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- 0 < `1`){
        have(thesis) by inEquality.apply
    }

    val ringInEq7 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- `0` < 2){
        have(thesis) by inEquality.apply
    }

    val ringInEq8 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- !(`0` < 0)){
        have(thesis) by inEquality.apply
    }

    val ringInEq9 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- !(x < x)){
        have(thesis) by inEquality.apply
    }
    val ringInEq10 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- -2 < `0`){
        have(thesis) by inEquality.apply
    }

    val ringInEq11 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- (`1` !== `0`)){
        have(thesis) by disEquality.apply
    }

    val ringInEq12 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- ((x + 2) !== (x + 3))){
        have(thesis) by disEquality.apply
    }

    val ringInDiv1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- !(i(2) | i(3))){
        have(thesis) by inDivInts.apply
    }

    val ringConjunct1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- !(i(2) | i(3)) /\ (0 < `1`)){
        have(liaByWitnessProof.apply(thesis)(List()))
    }

    val ringDisJunct1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- (i(2) | i(3)) \/ (0 < `1`)){
        have(liaByWitnessProof.apply(thesis)(List()))
    }
    val ringDisJunct2 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- !(i(2) | i(3)) \/ (1 < `1`)){
        have(liaByWitnessProof.apply(thesis)(List()))
    }

    val ringConjunct2 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- ∃(x, !(i(2) | i(3)) /\ (x < `1`))){
        have(liaByWitnessProof.apply(thesis)(List(0)))
    }
    val R2 = variable[Ind >>: Prop]
    // val test2 = Theorem(∀(x, P(x)) <=> ∀(y, P(y))){
    //     have(thesis) by Tableau
    // }
    // println(isVariable(x))
    // println(`1`.id.name)   
    // println("seregost")
    // println(isVariableOrNeg(x))
    // println(isVariableOrNeg(-c))
    // println(isNegVariable(-c))
    // println(isNegVariable(-(x)))
    // println(List(-x, -y).forall(isNegVariable))
    // println(isVariableOrNeg(`0`))
    // println(isVariableOrNeg(x + x))
    
}
// end Rings