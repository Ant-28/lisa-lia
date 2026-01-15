import scala.collection.immutable.{Set => SSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{| => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, *, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}
import RingStructure.{_}
// object Rings extends lisa.Main: 
//     import RingStructure.{*}
//     import RingEqReasoning.{*} 

object Rings extends lisa.Main 
{
    val t = variable[Ind]
    val _ = RingStructure

  

    val w : THM = RingStructure.add_closure
    println(w.statement)
    val dummy = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- `1` ∈ R) {
        have(thesis) by Restate.from(mul_id_closure)
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
    // val test = Theorem( (ring(R, <=, +, *, -, |, `0`, `1`)) |- `1` + (`1` + `1`) === (`1` + `1`) + `1`){
    //     assume(ring(R, <=, +, *, -, |, `0`, `1`))
    //     val t = add_assoc of (xx := `1`, yy := `1`, z := `1`)
    //     val q = typeChecking(getTypingVarsInAnte(t.result.left))
    //     val r = getTypings(t.result.left)
    //     have(t.result)
    //     println(thesis)
    //     println(t.result)
    //     r.map(qr => println(qr))
    //     q.map(qp => println(qp))
    //     have(thesis) by Cut.withParameters(r.toList(0))(q.toList(0), t)
    //     // sorry
    // }
    override def main(args: Array[String]): Unit = {
        List(RingStructure, EqReasoning).map(_.main(Array()))
        super.main(Array())
        println(om.stringWriter.toString)
    }
    println("Hello!")
}
// end Rings