// object Rings extends lisa.Main: 
//     import RingStructure.{*}
//     import RingEqReasoning.{*} 

object Rings extends lisa.Main 
    with RingStructure
    with RingEqReasoning 
{
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
    // def getTypingsInAntecedent(xx: SSet[Expr[Prop]]): SSet[Expr[Ind]] = xx
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
    // val test = Theorem( (ring(R, <=, `+`, *, `-`, `0`, `1`)) |- `1` + (`1` + `1`) === (`1` + `1`) + `1`){
    //     assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //     val t = add_assoc of (xx := `1`, yy := `1`, z := `1`)
    //     val q = typeChecking(getTypingsInAntecedent(t.result.left))
    //     val r = getTypings(t.result.left)
    //     have(t.result)
    //     println(thesis)
    //     println(t.result)
    //     r.map(qr => println(qr))
    //     q.map(qp => println(qp))
    //     have(thesis) by Cut.withParameters(r.toList(0))(q.toList(0), t)
    //     // sorry
    // }
    println("Hello!")
}
// end Rings