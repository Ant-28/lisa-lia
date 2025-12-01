import scala.collection.immutable.{Set => SSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.{*, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution

import Base.{IBinFun, IUnFun, IRel, infixBinaryFunction, infixUnaryFunction}
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
// import lisa.utils.prooflib.WithTheorems.Proof.InvalidProofTactic
// import lisa.utils.prooflib.WithTheorems.Proof.ValidProofTactic


// def decomposeConjunction()

object Rings extends lisa.Main:

  private val x   = variable[Ind]
  private val y   = variable[Ind]
  private val z   = variable[Ind]
  private val `0` = variable[Ind]
  private val `1` = variable[Ind]

  private val R = variable[Ind] // ring base set

  
  // We introduce the signature of rings first. maybe PIDs?

  // leq order
  // <= ⊆ L × L
  object <= extends Variable[Ind]("<="):
    val leq = this // just an alias, as `this` cannot be used in patterns

    /**
      * Constructs an expression representing a <= b
      */
    def construct(a: Expr[Ind], b: Expr[Ind]): Expr[Prop] = IRel(leq, a, b)
    
    /**
      * allow pattern matching on expressions of the form a <= b
      * as `case a <= b => ...`
      */
    def unapply(e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = 
      e match
        case IRel(`leq`, a, b) => Some((a, b))
        case _ => None

  // divisibility

  object | extends Variable[Ind]("|"):
    val divvy = this // just an alias, as `this` cannot be used in patterns

    /**
      * Constructs an expression representing a <= b
      */
    def construct(a: Expr[Ind], b: Expr[Ind]): Expr[Prop] = IRel(divvy, a, b)
    
    /**
      * allow pattern matching on expressions of the form a <= b
      * as `case a <= b => ...`
      */
    def unapply(e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = 
      e match
        case IRel(`divvy`, a, b) => Some((a, b))
        case _ => None


  // addition symbol on rings
  object + extends Variable[Ind]("+"):
    val plus = this

    def construct(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] = IBinFun(plus, a, b)

    def unapply(e: Expr[Ind]): Option[(Expr[Ind], Expr[Ind])] = 
      e match
        case IBinFun(`plus`, a, b) => Some((a, b))
        case _ => None
  
  
  object `-` extends Variable[Ind]("-"):
    val unaryneg = this
    def construct(a: Expr[Ind]): Expr[Ind] = IUnFun(unaryneg, a)
    def unapply(e: Expr[Ind]): Option[(Expr[Ind])] = 
      e match
        case IUnFun(`unaryneg`, a) => Some((a))
        case _ => None

  // meet symbol: Intersection for Sets, Conjunction for boolean algebras
  // * ∈ L × L → L
  object * extends Variable[Ind]("*"):
    val mult = this

    def construct(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] = IBinFun(mult, a, b)

    def unapply(e: Expr[Ind]): Option[(Expr[Ind], Expr[Ind])] = 
      e match
        case IBinFun(`mult`, a, b) => Some((a, b))
        case _ => None
  
  // Enables infix notation
  extension (left: Expr[Ind]) {
    infix def <=(right : Expr[Ind]): Expr[Prop]  = Rings.<=.construct(left, right)
    infix def |(right: Expr[Ind]):Expr[Prop] = Rings.|.construct(left, right)
    // this is probably not right?
    def  `-` :Expr[Ind]                    = Rings.-.construct(left)
    infix def  +(right : Expr[Ind]): Expr[Ind]   = Rings.+.construct(left, right)
    infix def  *(right : Expr[Ind]): Expr[Ind]   = Rings.*.construct(left, right)
  }

  // the definition of a ring of integers with the signature as above
  // the properties are listed here in full for reference
  object ring:
    // wrap the curried definition for convenience
    protected val ring = DEF( λ(R, λ(<=, λ(+, λ(*, λ(-, λ(`0`, λ(`1`,
      <= ⊆ (R × R) /\
      (`+` :: (R × R -> R)) /\
      (* :: (R × R -> R)) /\
      (`-` :: (R -> R)) /\
      // identities over addition and multiplication
      (`0` ∈ R) /\ 
      (`1` ∈ R) /\
      // total order over Integers
        ∀(x, (x ∈ R) ==> x <= x) /\ // reflexivity
        ∀(x, ∀(y, ((x ∈ R) /\ (y ∈ R) /\ (x <= y) /\ (y <= x)) ==> (x === y))) /\ // antisymmetry
        ∀(x, ∀(y, ∀(z, ((x ∈ R) /\ (y ∈ R) /\ (z ∈ R) /\ (x <= y) /\ (y <= z)) ==> (x <= z)))) /\ // transitivity
        ∀(x, ∀(y, (x ∈ R) /\ (y ∈ R) ==> (x <= y) \/ (y <= x))) // totality 

      // closure

      //    ∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x + y) ∈ R))
      // /\ ∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x * y) ∈ R))
      // abelian group under addition axioms
      // commutativity 
      /\  ∀(x,∀(y, (x ∈ R) /\ (y ∈ R) ==> ((x + y) === (y + x)))) /\
      // associativity
        ∀(x,∀(y, ∀(z, (x ∈ R) /\ (y ∈ R) /\ (z ∈ R) ==> (((x + y) + z) === (x + (y + z))) ))) /\
      // identity on addition
        ∀(x, x ∈ R ==> (x === (`0` + x))) /\
      // additive inverse
        ∀(x,  x ∈ R ==> ((x + (`-`(x))) === `0`)) 
      // cancellation law?
      // monoid
      // associativity
      /\ ∀(x, ∀(y, ∀(z, (x ∈ R) /\ (y ∈ R) /\ (z ∈ R) ==> ((x * (y * z)) === ((x * y) * z)))))
      // identity on multiplication
      /\ ∀(x, x ∈ R ==> (x === (`1` * x)))
      // commutative rings
      /\ ∀(x, ∀(y, (x ∈ R) /\ (y ∈ R) ==> ( (x * y) === (y * x) )))
      // this is a corollary so I should remove it
      // /\ ∀(x, x ∈ R ==> ((x *`1`) === x))
      // distributivity
      /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> ((x * (y + z)) === ((x * y) + (x * z))))))
      /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> (((y + z) * x) === ((x * y) + (x * z))))))

      // ordered rings
      /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> (x <= y)      ==> ((x + z) <= (y + z)))))
      /\ ∀(x, ∀(y, (x ∈ R /\ y ∈ R /\ (`0` <= x) ==> (`0` <= y))  ==> (`0` <= (x * y))))
      // don't add redundant axioms
      // 
      /\ ∀(x, ∀(y, (x ∈ R /\ y ∈ R ==> ((x <= `0`) /\ (y <= `0`))  ==> (`0` <= (x * y)))))
      /\ ∀(x, ∀(y, (x ∈ R /\ y ∈ R ==> ((x <= `0`) /\  (`0` <= y)) ==> ((x * y) <= `0`))))
      // how should we represent our integers? 
      // what does HOL light do?

      // create a very modest milestone
      // linear arithmetic normalization in rings


      // proofs such as x * 0 = x * (0 + 0)

      
    )))))))).printAs(args => s"ring(${args.mkString(", ")})")

    inline def apply(R: Expr[Ind], leq: Expr[Ind], pl: Expr[Ind], st: Expr[Ind], mi: Expr[Ind], zero: Expr[Ind], one: Expr[Ind]): Expr[Prop] = ring(R)(leq)(pl)(st)(mi)(zero)(one)

    def unapply(e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind])] = {
      e match
        case App(App(App(App(App(App(App(`ring`, r), leq), pl), st), mi), zero), one) => Some((r, leq, pl, st, mi, zero, one))
        case _ => None
      
    }


    inline def definition = ring.definition

  // we can instantiate and extract each of the properties for easier reuse


  // scaffolding for "by definition" theorems that are universally quantified
  def freeVars(s: SSet[Expr[Prop]]): SSet[Variable[Ind]] = {
    s.flatMap(ps => ps match {
      case ∈(a, b) => a.freeTermVars
      case _ => SSet()
    })
  }

  def isRingElem(s: Expr[Prop]) : Boolean = s match {
      case ring(_) => true
      case _ => false 
    }
  def hasRingElem(s: SSet[Expr[Prop]]): Boolean = s.exists(isRingElem)
   

  // def forallify(l: LList[Variable[Ind]])(lhs: Expr[Prop])(r: Expr[Prop]): Expr[Prop] = 
  //   l match {
  //     case Nil => (lhs ==> r) 
  //     case Cons(a, xs) => ∀(a, forallify(xs)(lhs)(r))
  //   }
  // def forallify(l: LList[Variable[Ind]])(r: Expr[Prop]): Expr[Prop] = 
  //   l match {
  //     case Nil => r
  //     case Cons(a, xs) => ∀(a, forallify(xs)(r))
  //   }

  def forallify(l: LList[Variable[Ind]])(lhs: Expr[Prop])(r: Expr[Prop]): Expr[Prop] = 
    l.foldRight(lhs ==> r)((x, xs) => ∀(x, xs)) 
  def forallify(l: LList[Variable[Ind]])(r: Expr[Prop]): Expr[Prop] = 
    l.foldRight(r)((x, xs) => ∀(x, xs)) 

  // "by definition of the algebraic structure"
  object byRingDefn extends ProofTactic:
    def apply(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      if (!hasRingElem(goal.left)) then proof.InvalidProofTactic("Not a ring") else
      if (goal.right.toList.length != 1) then proof.InvalidProofTactic("right element should only be a string") else
        // evil lexicographical hack that forces a certain order on universal quantifiers
        // val fvs = freeVars(goal.left).toList.sortBy(x => x.id.name) // we want to be able to unpack items
        val fvs = freeVars(goal.left).toList.sortBy(x => x.id.name)
        // println(fvs)
        val statement: Expr[Prop] = goal.right.head
        val res = TacticSubproof:
          assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
          val assumptions = goal.left.filterNot(isRingElem)
          // println(assumptions)
          assumptions.map(x => assume(x))
          if !assumptions.isEmpty then 
            val prop_lhs = assumptions.reduceLeft((a, b) => a /\ b)
            
            val forallified_stmt = forallify(fvs)(prop_lhs)(goal.right.toList(0)) 
            val taut1 = have(forallified_stmt) by Tautology.from(ring.definition)
            have(goal) by Restate.from(taut1.of(fvs*))
          else 
            
            val forallified_stmt = forallify(fvs)(goal.right.toList(0))
            val taut1 = have(forallified_stmt) by Tautology.from(ring.definition)
            have(goal) by Restate.from(taut1.of(fvs*))
       
        if !res.isValid then proof.InvalidProofTactic("byRingDefn failed! Perhaps your axioms aren't universally quantified in lexicographica; prder") else res

    }
  
  val add_closure = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R, y ∈ R) |- ((x + y) ∈ R)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R, y ∈ R)
    have(app(`+`)((x, y)) ∈ R) by Tautology.from(
      ring.definition, 
      appTyping of (f := `+`, x := (x, y), A := R × R, B := R), 
      CartesianProduct.membershipSufficientCondition of (A := R, B := R)
    )
    thenHave(thesis) by Substitution(infixBinaryFunction.definition of (f := `+`))
  }

  val mul_closure = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R, y ∈ R) |- ((x * y) ∈ R)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R, y ∈ R)
    have(app(*)((x, y)) ∈ R) by Tautology.from(
      ring.definition, 
      appTyping of (f := *, x := (x, y), A := R × R, B := R), 
      CartesianProduct.membershipSufficientCondition of (A := R, B := R)
    )
    thenHave(thesis) by Substitution(infixBinaryFunction.definition of (f := *))
  }

  val neg_closure = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R) |- (`-`(x) ∈ R)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R)
    have(app(`-`)(x) ∈ R) by Tautology.from(
      ring.definition, 
      appTyping of (f := `-`, x := x, A := R, B := R), 
      // CartesianProduct.membershipSufficientCondition of (A := R, B := R)
    )
    thenHave(thesis) by Substitution(infixUnaryFunction.definition of (f := `-`))
  }

  val additive_id = Theorem(ring(R, <=, `+`, *, `-`, `0`, `1`) |- `0` ∈ R){
    have(thesis) by byRingDefn.apply
  }

  val mult_id = Theorem(ring(R, <=, `+`, *, `-`, `0`, `1`) |- `1` ∈ R){
    have(thesis) by byRingDefn.apply
  }
  val order_refl = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R) |- x <= x) {
    have(thesis) by byRingDefn.apply
  }
  
  val order_antisym = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), x ∈ R, y ∈ R, x <= y, y <= x) |- x === y){
    have(thesis) by byRingDefn.apply
  }


  val order_trans = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R) , (y ∈ R) , (z ∈ R) , (x <= y) , (y <= z)) |- x <= z){
    have(thesis) by byRingDefn.apply
  }

  val order_tot = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R) , (y ∈ R)) |- (x <= y) \/ (y <= x)){
    have(thesis) by byRingDefn.apply
  }

// ∀(x, y, z)
  val add_comm = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R) , (y ∈ R)) |- (x `+` y) === (y `+` x)){
    have(thesis) by byRingDefn.apply
  }

  val add_assoc = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R) , (y ∈ R), (z ∈ R)) |- ((x + y) + z) === (x + (y + z))){
    have(thesis) by byRingDefn.apply
  }

  val add_id    = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (x === (`0` + x))){ 
    have(thesis) by byRingDefn.apply 
  }

  val zero_x_x  = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (x === (`0` + x))){ 
    have(thesis) by Tautology.from(add_id)
  }

  val x_zero_x  = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (x === (x + `0`))){ 
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    assume(x ∈ R)
    val a = have(`0` ∈ R) by Tautology.from(additive_id)
    val b = have((x + `0`) ∈ R) by Tautology.from(add_closure of (x := x, y := `0`), a)
    have(x === (x + `0`)) by Congruence.from(add_id, add_comm of (x := x, y := `0`), a, b)
    have(thesis) by Tautology.from(lastStep, a, b)
  }
  
  val add_inv   = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- ((x + (`-`(x))) === `0`)){
    have(thesis) by byRingDefn.apply 
  }


  val mul_assoc = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R)) |- ((x * (y * z)) === ((x * y) * z))){
    have(thesis) by byRingDefn.apply
  }
  
  val mul_id_right = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (x === (`1` * x))){
    have(thesis) by byRingDefn.apply 
  }
  
  val mul_comm = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R)) |- (x * y) === (y * x)){
    have(thesis) by byRingDefn.apply 
  }

  val mul_id_left =  Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (x === (x * `1`))){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    assume(x ∈ R)
    val v1 = have(x === (`1` * x)) by Tautology.from(mul_id_right)
    val v2 = have(`1` ∈ R) by Tautology.from(mult_id)
    val v3 = have((`1` * x === x * `1`)) by Tautology.from(v2, mul_comm of (x := x, y := `1`))
    have(thesis) by Congruence.from(v1, v3)
  }

  // /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> ((x * (y + z)) === ((x * y) + (x * z))))))
  //     /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> (((y + z) * x) === ((x * y) + (x * z))))))

  val mul_dist_left = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R)) |- ((x * (y + z)) === ((x * y) + (x * z)))){
    have(thesis) by byRingDefn.apply 
  }

  val mul_dist_right = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R)) |- (((y + z) * x) === ((y * x) + (z * x)))){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    val v0 = have((y + z) ∈ R) by Tautology.from(add_closure of (x := y, y := z))
    val v0x = have((x * y) === (y * x)) by Tautology.from(mul_comm)
    val v0y = have((z * x) === (x * z)) by Tautology.from(mul_comm of (y := z))
    val v1 = have(((x * (y + z)) === ((x * y) + (x * z)))) by Tautology.from(mul_dist_left)
    val v2 = have((x * (y + z)) === ((y + z) * x)) by Tautology.from(v0, mul_comm of (x := x, y := (y + z)))
    have(thesis) by Congruence.from(v1, v2, v0x, v0y)
  } 
 
  val cong_test = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R), (x === y)) |- (x + z) === (y + z)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R), (x === y))
    val v1 = have((x + z) ∈ R) by Tautology.from(add_closure of (x:= x, y:=z))
    val v2 = have((y + z) ∈ R) by Tautology.from(add_closure of (x:= y, y:=z))
    have(thesis) by Congruence.from(v1, v2)
  }

  val zero_times = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (`0` * x === `0`)) {
    assume(x ∈ R)
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    val zero_r = have(`0` ∈ R) by Tautology.from(additive_id)
    val p0xr = have((`0` * x) ∈ R) by Tautology.from(zero_r, mul_closure of (x := `0`, y := x))
    val m0xr = have(`-`(`0` * x) ∈ R) by Tautology.from(neg_closure of (x := (`0` * x)), lastStep)
    
    have(`0` === (`0` + `0`)) by Tautology.from(add_id of (x := `0`), zero_r)
    val s1 = have((`0` + `0`) * x === `0` * x) by Congruence.from(lastStep)
    val s2 = have((`0` + `0`) * x === (`0` * x) + (`0` * x)) by Tautology.from(mul_dist_right of (x := x, y := `0`, z := `0`), zero_r)
    // equational reasoning advocated by fp people & dijkstra
    // Rustan Leino (of dafny fame)
    // equational reasoning used in a course 
    // new milestone: computing 
    // assume repr of numbers is as small an area of the tactic
    // avoid assuming internals of numbers
    // tactic should e.g. 2 + 3 === 5 or 2 * 3 === 6? 2 + (-3) === -1
    // all *ground* linear equalities over Z for linearization into "canonical form"
    val s3 = have((`0` * x) === (`0` * x) + (`0` * x)) by Congruence.from(s1, s2)
    val s4 = have((`0` * x) + `-`(`0` * x) === ((`0` * x) + (`0` * x)) + `-`(`0` * x)) by Congruence.from(lastStep)
    val s5 = have((`0` * x) + `-`(`0` * x) === `0`) by Tautology.from(add_inv of (x := (`0` * x)), p0xr, m0xr)
    val s6 = have((( (`0` * x) + (`0` * x) ) + (`-`(`0` * x))) === ( (`0` * x) + ( (`0` * x) + (`-`(`0` * x)) ))) by Tautology.from(p0xr, m0xr, add_assoc of (x := (`0` * x), y := (`0` * x), z := (`-`(`0` * x))))
    val s7 = have(((`0` * x) + ((`0` * x) + `-`(`0` * x))) === ((`0` * x) + `0`)) by Congruence.from(s5)
    val s8 = have((`0` * x) === (`0` + (`0` * x))) by Tautology.from(p0xr, add_id of (x := (`0` * x)), zero_r)
    val s9 = have( (`0` + (`0` * x)) ===  ((`0` * x) + `0`)) by Tautology.from(add_comm of (x:= `0`, y := (`0` * x)), zero_r, p0xr)
    have(thesis) by Congruence.from(s9, s8, s7, s6, s5, s4)
  }

  val double_negation_elimination = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R)) |- (`-`(`-`(x)) === x)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R))
    val n1 = have(`-`(x) ∈ R) by Tautology.from(neg_closure of (x := x))
    val n2 = have(`-`(`-`(x)) ∈ R) by Tautology.from(neg_closure of (x := `-`(x)), n1)

    have(`-`(x) + `-`(`-`(x)) === `0`) by Tautology.from(add_inv of (x := `-`(x)), n1)
   
    have(((x + `-`(x)) + `-`(`-`(x))) === x) by Congruence.from(lastStep, x_zero_x of (x := x), n1, n2, 
                                                               add_assoc of (x := x, y := `-`(x), z := `-`(`-`(x))))
    have(`-`(`-`(x)) === x) by Congruence.from(lastStep, add_inv of (x := x), zero_x_x of (x := `-`(`-`(x))), n1, n2)
    have(thesis) by Tautology.from(n1, n2, lastStep)
  }

  
  val neg_x_y_neg_xy = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R)) |- (`-`(x) * y) === `-`(x * y)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R))
    val h1 = have((x * y) ∈ R) by Tautology.from(mul_closure)
    // Discharge(h1)
    val h2 = have(`-`(x * y) ∈ R) by Tautology.from(neg_closure of (x := (x * y)), h1)
    val h3 = have(`-`(x) ∈ R) by Tautology.from(neg_closure)
    val h4 = have((`-`(x) * y) ∈ R) by Tautology.from(h3, mul_closure of (x:= `-`(x)))
    val h5 = have(`0` ∈ R) by Tautology.from(additive_id)
    // Discharge(h2)
    

    have((x + `-`(x)) === `0`) by Tautology.from(add_inv)
    val v2 = have((x + `-`(x)) * y === `0` * y) by Congruence.from(lastStep)
    have(`0` * y  === `0`) by Tautology.from(zero_times of (x := y))
    have((x + `-`(x)) * y === `0`) by Congruence.from(lastStep, v2)
    have(((x * y) + (`-`(x) * y)) === `0`) by Congruence.from(lastStep, h3, mul_dist_right of (y := x, z := `-`(x), x := y))
    have(((`-`(x) * y) + (x * y)) === `0`) by Congruence.from(h1, h2, h3, h4, add_comm of (x := (x * y), y:= (`-`(x) * y)), lastStep)
    have(((`-`(x) * y) + (x * y)) + `-`(x * y) === `-`(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, h5, add_id of (x := (`-`(x * y))))
    have((`-`(x) * y) + ((x * y) + `-`(x * y)) === `-`(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, add_assoc of (x := (`-`(x) * y), y := (x * y), z :=`-`(x * y)))
    have((`-`(x) * y) + ((x * y) + `-`(x * y)) === `-`(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, add_assoc of (x := (`-`(x) * y), y := (x * y), z :=`-`(x * y)))
    have((`-`(x) * y) + (`0`) === `-`(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, add_inv of (x := (x * y)))
    have(`0` + (`-`(x) * y) === `-`(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, h5, add_comm of (x := (`-`(x) * y), y := `0`))
    have((`-`(x) * y) === `-`(x * y)) by Congruence.from(lastStep, add_id of (x := (`-`(x) * y)), h1, h2, h3, h4, h5)     
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5)
  }

  val neg_x_neg_y_xy = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R)) |- (`-`(x) * `-`(y)) === (x * y)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R))
    val h1 = have((x * y) ∈ R) by Tautology.from(mul_closure)
    val h2 = have(`-`(x * y) ∈ R) by Tautology.from(neg_closure of (x := (x * y)), h1)
    val h3 = have(`-`(x) ∈ R) by Tautology.from(neg_closure)
    val h4 = have(`-`(y) ∈ R) by Tautology.from(neg_closure of (x := y))
    val h5 = have((`-`(x) * `-`(y)) ∈ R) by Tautology.from(h3, mul_closure of (x:= `-`(x), y := `-`(y)), h3, h4)
    val h6 = have(`0` ∈ R) by Tautology.from(additive_id)

    have((`-`(x) * `-`(y)) === `-`(x * `-`(y))) by Tautology.from(neg_x_y_neg_xy of (y := `-`(y)), h4)
    have((`-`(x) * `-`(y)) === (x * y)) by Congruence.from(lastStep, mul_comm of (y := `-`(y)), h1, h2, h3, h4, 
                                                                  mul_comm, 
                                                                  neg_x_y_neg_xy of (x := y, y := x),
                                                                  double_negation_elimination of (x := (x * y)))
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5)

  
  }

  val negation_dist_add = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R)) |- `-`(x + y) === `-`(x) + `-`(y)){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R))
    val h1 = have((x + y) ∈ R) by Tautology.from(add_closure)
    val h2 = have(`-`(x + y) ∈ R) by Tautology.from(neg_closure of (x := (x + y)), h1)
    val h3 = have(`-`(x) ∈ R) by Tautology.from(neg_closure)
    val h4 = have(`-`(y) ∈ R) by Tautology.from(neg_closure of (x := y))
    val h5 = have((`-`(x) + `-`(y)) ∈ R) by Tautology.from(h3, add_closure of (x:= `-`(x), y := `-`(y)), h3, h4)
    val h6 = have(`0` ∈ R) by Tautology.from(additive_id)
    val h7 = have((x + `-`(x)) ∈ R) by Tautology.from(add_closure of (x := x, y := `-`(x)), h3)
    val h8 = have((y + `-`(y)) ∈ R) by Tautology.from(add_closure of (x := y, y := `-`(y)), h4)

    have((x + `-`(x)) === `0`) by Tautology.from(add_inv)
    have((x + `-`(x)) + (y + `-`(y)) === `0`) by Congruence.from(lastStep, 
                                                    add_inv of (x := y), 
                                                    zero_x_x of (x := (y + `-`(y))))
    have(((x + `-`(x)) + y) + `-`(y) === `0`) by Congruence.from(lastStep, 
                                                                 add_assoc of (x := (x + `-`(x)), y := y, z := `-`(y)),
                                                                h7, h4)
    // have((x + y) + (`-`(x) + `-`(y)) === `0`)  by Congruence.from(lastStep, 
    have((x + (y + `-`(x))) + `-`(y) === `0`)  by Congruence.from(lastStep, 
                                                          add_assoc of (x := (x), y := `-`(x), z := y),
                                                          add_comm of (x := `-`(x), y := y),
                                                          // add_assoc of (x := x, y := y, z := (`-`(x))),
                                                          // add_assoc of (x := (x + y), y := `-`(x), z := `-`(y)),
                                                          h1, h2, h3, h4, h5, h6, h7, h8)
    have((x + y) + (`-`(x) + `-`(y)) === `0`) by Congruence.from(lastStep, 
                                                          add_assoc of (x := x, y := y, z := (`-`(x))),
                                                          add_assoc of (x := (x + y), y := `-`(x), z := `-`(y)),
                                                          h1, h2, h3, h4, h5, h6, h7, h8)

    have((`-`(x) + `-`(y))  === `-`(x + y)) by Congruence.from(lastStep,
                                                                        x_zero_x of (x := `-`(x + y)),
                                                                        add_assoc of (x := `-`(x + y), y := (x + y), z := (`-`(x) + `-`(y))),
                                                                        add_comm of (x := `-`(x + y), y := (x + y)),
                                                                        add_inv of (x := (x + y)),
                                                                        zero_x_x of (x := (`-`(x) + `-`(y))),
                                                                        h1, h2, h3, h4, h5, h6, h7, h8)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5, h6, h7, h8)

  }
  val negation_zero = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`)) |- `-`(`0`) === `0`){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    val h6 = have(`0` ∈ R) by Tautology.from(additive_id) 
    val h7 = have(`-`(`0`) ∈ R) by Tautology.from(neg_closure of (x := `0`), h6)
    have(`-`(`0`) === `0`) by Congruence.from(lastStep, add_inv of (x := `0`), h6, h7, zero_x_x of (x := `-`(`0`)))
    have(thesis) by Tautology.from(lastStep, h6, h7)
  }
  object BigIntToRingElem:
    def i(x : BigInt) : Expr[Ind] = {
      if x < 0 then 
        `-`.construct(i(-x))
      else if x > 0 then
        `1` `+` i(x - 1)
      else 
        `0`
    }
  


  
  def canonical_sum(x: Expr[Ind]): Boolean = {
    x match {
      case `0` => true
      case `1` + xs => canonical_sum(xs)
      case _ => false
    }
  }
  val w = x === y
  // hint; use structuralToString
  println(w.getClass)
  def is_eq(x: Expr[Prop]): Boolean = {
    x match {
      case (_ `equality` _) => true
      case _ => false
    }
  }

  def collectSubExprs(exp: Expr[Ind]): SSet[Expr[Ind]] = exp match {
    case a + b  => collectSubExprs(a) ++ collectSubExprs(b) + exp
    case `-`(a) => collectSubExprs(a) + exp
    case a * b  => collectSubExprs(a) ++ collectSubExprs(b) + exp
    case _      => SSet(exp)
  }
  


  val succ_succ_lr   = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R), (x + y === z)) |- (`1` + x) + y === (`1` + z)){
    assume(goal.left.toSeq*)
    have(thesis) by Congruence.from(add_assoc of (x := `1`, y := x, z := y),
                                    (have(`1` ∈ R) by Tautology.from(mult_id)))
  }

  private def typeChecking(using lib: library.type, proof: lib.Proof)(s: SSet[Expr[Ind]]): SSet[proof.InstantiatedFact | proof.ProofStep] = s.map: 
      case a + b  => add_closure of (x := a, y := b)
      case `-`(a) => neg_closure of (a)
      case a * b  => mul_closure of (x := a, y := b)
      case `0`    => have(`0` ∈ R) by Tautology.from(additive_id)
      case `1`    => have(`1` ∈ R) by Tautology.from(mult_id)
      case  x     => have(x ∈ R |- x ∈ R) by Restate

  inline def TacticSubproofWithResult[A](using proof: Library#Proof)(inline computeProof: proof.InnerProof ?=> Unit): (proof.ProofTacticJudgement, A) =
    val iProof: proof.InnerProof = new proof.InnerProof(None)
    computeProof(using iProof)
    SUBPROOF(using proof)(None)(iProof).judgement.asInstanceOf[proof.ProofTacticJudgement]


  val succ_succ_defn = Theorem((ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R)) |- (`1` + x) + (`1` + y) === (`1` + (`1` + (x + y)))){
    assume(ring(R, <=, `+`, *, `-`, `0`, `1`), (x ∈ R), (y ∈ R))
    // have(`1` ∈ R) by Restate.from(additive_id)
    val g = (goal.right.toList(0): @unchecked) match 
      case a `equality` b => (a, b)

    val subex = collectSubExprs(g._1) ++ collectSubExprs(g._2)
    val typing = typeChecking(subex)
    
    val part = TacticSubproof {
      assume(`1` ∈ R)
      assume((`1` + x) ∈ R)
      assume((`1` + y) ∈ R)
      have((`1` + x) + (`1` + y) === (((`1` + x) + `1`) + y)) by Tautology.from(add_assoc of (x := (`1` + x), y := `1`, z := y))
      have((`1` + x) + (`1` + y) === ((`1` + (`1` + x)) + y)) by Congruence.from(lastStep, add_comm of (x := `1`, y := `1` + x))
      have((`1` + x) + (`1` + y) === (`1` + ((`1` + x) + y))) by Congruence.from(lastStep, add_assoc of (x := `1`, y := `1` + x, z := y))
      have((`1` + x) + (`1` + y) === (`1` + (`1` + (x + y))) ) by Congruence.from(lastStep, add_assoc of (x := `1`, y := x, z := y))
    } 
    val seqs = typing + have(part)
    have(thesis) by Tautology.from(seqs.toSeq*)
  }

  def canonicalInt(x : Expr[Ind]): Boolean = {
    x match {
      case `0` => true
      case `1` + xs => canonicalInt(xs)
      case _ => false
    }
  }




  object evalRingEq extends ProofTactic:  
    // FIXME: Try to use collect
    def getTypingsInAntecedent(x: SSet[Expr[Prop]]): SSet[Expr[Ind]] = x.flatMap(
      (y) => y match {
        case ys ∈ R => SSet(ys)
        case _      => SSet()
      }
    ).flatMap(x => collectSubExprs(x))

    def apply(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
        if(goal.right.size != 1) then proof.InvalidProofTactic("I can't prove more than one sequent!")
        else  
          val goalElem = goal.right.toList(0)
          TacticSubproof:
            assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
            if(!is_eq(goalElem)) then proof.InvalidProofTactic("I can't prove anything other than equality!")
            else 
              val sol = eval(goalElem)

              println(have(sol).bot)
              if !sol.isValid then proof.InvalidProofTactic("Checking sums failed!") else 
                val typing = typeChecking(getTypingsInAntecedent(have(sol).bot.left))
                val seqs = typing + have(sol)
                // have(goal) by Congruence.from(seqs.toSeq*)
                have(goal) by Tautology.from(seqs.toSeq*)

    }


   
    def removeZeros(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (Expr[Ind], proof.ProofTacticJudgement) = {
      // this @unchecked will probably be the bane of my existence
      (ex : @unchecked) match {
      // removeZeros Zero = Zero
        case `0` => {
            val proofRes = TacticSubproof { 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              have(`0` ∈ R |- `0` === `0`) by Restate }
            val res = `0`
            (res, proofRes)
        }
      // removeZeros One = One
        case `1` => {
          val proofRes = TacticSubproof { 
            assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
            have(`1` ∈ R |- `1` === `1`) by Restate }
          val res = `1`
          (res, proofRes)
        }
      // removeZeros (Plus x Zero) = removeZeros x
        case xs + `0` => {
            // simpl(xs)
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (result, prf) = removeZeros(xs)
              if !prf.isValid then proof.InvalidProofTactic("simplification failed!") 
              else 
                val newstmt = ((`0`∈ R, xs ∈ R, result ∈ R) |- xs + `0` === result) 
                val stmt = newstmt ++<< have(prf).bot
                have(newstmt) by Congruence.from(x_zero_x of (x := xs), have(prf))
            }
            (removeZeros(xs)._1, prf)
        }
      // removeZeros (Plus Zero x) = removeZeros x
        case `0` + xs => {
            // simpl(xs)
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (result, prf) = removeZeros(xs)
              if !prf.isValid then proof.InvalidProofTactic("simplification failed!") 
              else 
                val newstmt = ((`0`∈ R, xs ∈ R, result ∈ R) |- `0` + xs === result) 
                val stmt = newstmt ++<< have(prf).bot
                have(newstmt) by Congruence.from(zero_x_x of (x := xs), have(prf))
            }
            (removeZeros(xs)._1, prf)
          }
      // removeZeros (Plus x y) = Plus (removeZeros x) (removeZeros y) 
        case xs + ys   => {
          val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (resultx, prfx) = removeZeros(xs)
              val (resulty, prfy) = removeZeros(ys)
              if !(prfx.isValid && prfy.isValid) then proof.InvalidProofTactic("removeZeros failed!") 
              else 
                val newstmt = ((`0`∈ R, xs ∈ R, resultx ∈ R, resulty ∈ R, ys ∈ R) |- xs + ys === resultx + resulty) 
                val stmt = newstmt ++<< have(prfx).bot ++<< have(prfy).bot
                have(newstmt) by Congruence.from(zero_x_x of (x := xs), have(prfy), have(prfx))
            }
          (removeZeros(xs)._1 + removeZeros(ys)._1, prf)
        } 
      // removeZeros (Neg x) = Neg (removeZeros x)
        case `-`(xs)  => {
          val prf = TacticSubproof{ 
            assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
            val (resultx, prfx) = removeZeros(xs)
            
            if !(prfx.isValid) then proof.InvalidProofTactic("removeZeros failed!") 
            else 
              val newstmt = ((`0`∈ R, xs ∈ R, resultx ∈ R )|- `-`(xs)  === `-`(resultx)) 
              val stmt = newstmt ++<< have(prfx).bot
              have(newstmt) by Congruence.from(have(prfx))
            }
          (`-`(removeZeros(xs)._1), prf)
        }
      // removeZeros (Mult x y) = Mult (removeZeros x) (removeZeros y) 
        case xs * ys   => {
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (resultx, prfx) = removeZeros(xs)
              val (resulty, prfy) = removeZeros(ys)
              if !(prfx.isValid && prfy.isValid) then proof.InvalidProofTactic("removeZeros failed!") 
              else 
                val newstmt = ((`0`∈ R, xs ∈ R, resultx ∈ R, resulty ∈ R, ys ∈ R) |- xs * ys === resultx * resulty) 
                val stmt = newstmt ++<< have(prfx).bot ++<< have(prfy).bot
                have(newstmt) by Congruence.from(have(prfy), have(prfx))
            }
            (removeZeros(xs)._1 * removeZeros(ys)._1, prf)
          }
        } 
    }
      
    

    def rightBias(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (Expr[Ind], proof.ProofTacticJudgement) = {
      (ex: @unchecked) match {
        // rightBias (Plus (Plus x y) z) = rightBias (Plus  (rightBias x) (Plus(rightBias y) (rightBias z)))
        case (xs + ys) + zs => {
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (resultx, prfx) = rightBias(xs)
              val (resulty, prfy) = rightBias(ys)
              val (resultz, prfz) = rightBias(zs)
              if !(prfx.isValid && prfy.isValid && prfz.isValid) then proof.InvalidProofTactic("rightBiasDef failed!") 
              else 
                val newstmt = ((`0`∈ R, `1` ∈ R,  xs ∈ R, resultx ∈ R, resulty ∈ R, ys ∈ R, resultz ∈ R, zs ∈ R) |- (x + y) + z === resultx + (resulty + resultz)) 
                val stmt = newstmt ++<< have(prfx).bot ++<< have(prfy).bot ++<< have(prfz).bot
                have(newstmt) by Congruence.from(have(prfy), have(prfx), have(prfz), add_assoc of (x := xs, y := ys, z := zs))
            }
            (rightBias(xs)._1 + (rightBias(ys)._1 + rightBias(zs)._1), prf)
        }
        // rightBias (Plus x z) = Plus (rightBias x) (rightBias z) -- x should be One, Zero or Neg One here
        case (xs + zs) => 
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (resultx, prfx) = rightBias(xs)
              val (resultz, prfz) = rightBias(zs)
              if !(prfx.isValid && prfz.isValid) then proof.InvalidProofTactic("rightBiasDef failed!") 
              else 
                val newstmt = ((`0`∈ R, `1` ∈ R,  xs ∈ R, resultx ∈ R, resultz ∈ R, zs ∈ R) |- x + z === resultx + resultz)
                val stmt = newstmt ++<< have(prfx).bot ++<< have(prfz).bot
                have(newstmt) by Congruence.from(have(prfx), have(prfz))
            }
            (rightBias(xs)._1 + rightBias(zs)._1, prf)
        // rightBias x = x
        case xs => {
          val prf = TacticSubproof{
          assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
          val (resultx, prfx) = rightBias(xs)
          if !(prfx.isValid) then proof.InvalidProofTactic("rightBiasDef failed!") 
          else 
            val newstmt = ((`0`∈ R, `1` ∈ R,  xs ∈ R, resultx ∈ R) |- x === resultx)
            val stmt = newstmt ++<< have(prfx).bot 
            have(newstmt) by Congruence.from(have(prfx))
          }
          (rightBias(xs)._1, prf)
        }
      }
    }
    

    def negElim(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (Expr[Ind], proof.ProofTacticJudgement) = {
      (ex : @unchecked) match {
        // negElim (Neg Zero) = Zero
        case `-`(`0`) => {???}
        // negElim (Neg (Neg x)) = negElim x
        case `-`(`-`(x)) => {???}
        // negElim (Neg (Plus x y)) = Plus (negElim (Neg x)) (negElim (Neg y))
        case `-`(x + y) => {???}
        // negElim (Neg (Mult x y)) =  Mult (negElim (Neg x)) (negElim y)
        case `-`(x * y) => {???}
        // negElim (Mult (Neg x) (Neg y)) = negElim (Mult x y)
        case (`-`(x) * `-`(y)) => {???}
        // negElim (Plus x y) = Plus (negElim x) (negElim y)
        case (x + y) => {???}
        // negElim (Mult x y) = Mult (negElim x) (negElim y)
        case x * y => {???}
        // negElim x = x
        case x => {???}
      }
    }

    def cancellation(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (Expr[Ind], proof.ProofTacticJudgement) = {
      (ex : @unchecked) match {
        // cancellation (Plus (Neg One) One) = Zero
        case `-`(`1`) + `1` => {???}
        // cancellation (Plus One (Neg One)) = Zero
        case `1` + `-`(`1`) => {???}
        case x + (y + z) => 
        // cancellation (Plus x (Plus y z)) = case (x, y, z) of 
          (x, y, z) match {
        //     (One, Neg One, z) -> cancellation z
            case (`1`, `-`(`1`), z) => {???}
        //     (One, y, Neg One) -> cancellation y
            case (`1`, y, `-`(`1`)) => {???}
        //     (Neg One, One, z) -> cancellation z
            case (`-`(`1`), `1`, z) => {???}
        //     (Neg One, y, One) -> cancellation y
            case (`-`(`1`), y, `1`) => {???}
        //     (x, One, Neg One) -> cancellation x
            case (x, `1`, `-`(`1`)) => {???}
        //     (x, Neg One, One) -> cancellation x
            case (x, `-`(`1`), `1`) => {???}
        //     (x, y, z) -> Plus (cancellation x) (cancellation (Plus y z))
            case (x, y, z) => {???}
          }
        //   cancellation x = x
        case x => {???}
        
      }
    }


    def pushDownMult(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (Expr[Ind], proof.ProofTacticJudgement) = {
    (ex : @unchecked) match {
      // pushDownMult (Mult x Zero) = Zero 
      case x * `0` => {???}
      // pushDownMult (Mult Zero x) = Zero
      case `0` * x => {???}
      // pushDownMult (Mult x One) = pushDownMult x
      case  x * `1` => {???}
      // pushDownMult (Mult One x) = pushDownMult x 
      case  `1` * x => {???}
      // pushDownMult (Mult x (Plus y z)) = Plus (pushDownMult (Mult x y)) (pushDownMult (Mult x z))
      case  (x * (y + z)) => {???}
      // pushDownMult (Mult (Plus y z) x) = Plus (pushDownMult (Mult x y)) (pushDownMult (Mult x z))
      case (y + z) * x => {???}
      // pushDownMult (Plus x y) = Plus (pushDownMult x) (pushDownMult y)
      case x + y => {???}
      // pushDownMult (Mult x y) = Mult (pushDownMult x) (pushDownMult y)
      case x * y => {???}
      // pushDownMult (Neg x) = Neg (pushDownMult x)
      case `-`(y) => {???}
      // pushDownMult x = x
      case x => {???}
      }
    }

    // allFns = pushDownMult . cancellation. negElim . rightBias. removeZeros
    // fixpointify f x = if f x == x then x else fixpointify f (f x)
    // need to check for any invalidProoftactic when returning fixpointified
    // ultimateOpt = fixpointify allFns
    /**
     *  
     * returns canonical form of ex, as i(n) for some n ∈ ℕ
     * 
     * and a proof that ring(...), ex ∈ R, i(n) ∈ R |- ex === i(n)
     * 
     * @param ex     
     * @example
     */
    sealed trait Biased
    case class RB(x : Expr[Ind]) extends Biased
    case class NRB(x: Expr[Ind]) extends Biased
    def simplify(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (RB, proof.ProofTacticJudgement) = {

        (ex : @unchecked) match {
          case `0` => {
            val proofRes = TacticSubproof { 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              have(`0` ∈ R |- `0` === `0`) by Restate }
            val res = RB(`0`)
            (res, proofRes)
          }
          case `1` => {
            val proofRes = TacticSubproof { 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              have(`1` ∈ R |- `1` === `1`) by Restate }
            val res = `1`
            (res, proofRes)
          }
          case `0` + xs => {
            // simpl(xs)
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (result, prf) = simplify(xs)
              if !prf.isValid then proof.InvalidProofTactic("simplification failed!") // TODO: check if invalidprooftactic needs .validate or st 
              else 
                val newstmt = ((`0`∈ R, xs ∈ R, result ∈ R) |- `0` + xs === result) 
                val stmt = newstmt ++<< have(prf).bot
                // TODO: change to one substitute instead
                // use tactic RightSubstEq
                // provide a lambda like (\y -> y === result) and substitute with 0 + xs === xs 
                have(newstmt) by Congruence.from(zero_x_x of (x := xs), have(prf))
            }
            (simplify(xs)._1, prf)
          }
          // case _ => (x, proof.InvalidProofTactic("not implemented"))
          case xs + `0` => {
            // simpl(xs)
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (result, prf) = simplify(xs)
              if !prf.isValid then proof.InvalidProofTactic("simplification failed!") 
              else 
                val newstmt = ((`0`∈ R, xs ∈ R, result ∈ R) |- xs + `0` === result) 
                val stmt = newstmt ++<< have(prf).bot
                // println(stmt.toString)
                // println(have(prf).bot.toString)
                // println("x + 0")
                // println(stmt.toString)
                have(newstmt) by Congruence.from(x_zero_x of (x := xs), have(prf))
            }
            (simplify(xs)._1, prf)
          }
          case (xs + ys) + zs => 
            val prf = TacticSubproof{
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (rxs, prfxs) = simplify(xs)
              val (rys, prfys) = simplify(ys)
              val (rzs, prfzs) = simplify(zs)
              // FIXME: have should be after you ahve checked the proof step
              // it consumes the ProofTacticResult, and may throw
              val h1 = have(prfxs) // have(xs === rxs) 
              val h2 = have(prfys) // have(ys === rys)
              val h3 = have(prfzs) // have(zs === rzs)

              // val associ = have(((xs + ys) + zs) === (rxs + (rys + rzs)))
              val (rsimp, prfsimp) = simplify(rxs + (rys + rzs))
              val hsimp = have(prfsimp) // have(rxs + (rys + rzs) === rsimp)
              if !(prfxs.isValid && prfys.isValid && prfzs.isValid && prfsimp.isValid) 
              then proof.InvalidProofTactic("simplification failed!") 
              else
                // TODO:
                //  can be done in two subst steps
                //  |- (x + y) + z = (x + y) + z by Restate
                //  |- (x + y) + z = (rx + ry) + rz by RightSubstEq(\ sx sy sz -> (x + y) + z = (sx + sy) + sz, x -> rx, y -> ry, z -> rz)
                //  |- (x + y) + z = rx + (ry + rz) by RightSubstEq(\ ss -> (x + y) + z = ss, theWhole -> theWholeAssoc)
                //  |- (x + y) + z = rsimp by RightSubstEq(\ ss -> (x + y) + z = ss, theWholeAssoc -> rsimp)
                val newstmt = ((xs ∈ R, ys ∈ R, zs ∈ R, rxs ∈ R, rys ∈ R, rzs ∈ R) |- (xs + ys) + zs === rsimp)
                val stmt = newstmt ++<< h1.bot ++<< h2.bot ++<< h3.bot  ++<< hsimp.bot // ++<< associ.bot 
                // println("x + y + z")
                // println(stmt.toString)
                have(stmt) by Congruence.from(x_zero_x of (x := xs), h1, h2, h3, hsimp, add_assoc of (x := xs, y := ys, z := zs))
            }
            (simplify(simplify(xs)._1 + (simplify(ys)._1 + simplify(zs)._1))._1, prf)
          case `1` + xs     => {
            // simpl(xs)
            val prf = TacticSubproof{ 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              val (result, prf) = simplify(xs)
              // println("x, xs, prf")
              // println(ex)
              // println(xs)
              // println(result)
              // println(have(prf).toString)
              if !prf.isValid then proof.InvalidProofTactic("simplification failed!") 
              else 
                val newstmt = ((`1`∈ R, xs ∈ R, result ∈ R) |- `1` + xs === `1` + result) 
                val stmt = newstmt ++<< have(prf).bot
                // println(stmt.toString)
                // println("1 + x")
                // println(stmt.toString)
                // println(have(prf).bot.toString)
                have(newstmt) by Congruence.from(have(prf))
            }
            (`1` + simplify(xs)._1, prf)
        }
        case `-`(`0`) => {
            val proofRes = TacticSubproof { 
              assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
              have((`0` ∈ R, `-`(`0`) ∈ R) |- `-`(`0`) + `0` === `0` + `-`(`0`) ) by Tautology.from(add_comm of (x := `0`, y := `-`(`0`))) }
            val res = `0`
            (res, proofRes)
          
        }
      }
    }

    def eval(using lib: library.type, proof: lib.Proof)(goal: Expr[Prop]): proof.ProofTacticJudgement = {
      assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
      TacticSubproof{
      goal match
        case x `equality` y if canonicalInt(x) && canonicalInt(y) => {
          have(x === y) by Tautology
        }
        case x `equality` y => {
          val (lval, lprf) = evalRingEq.simplify(x)
          val (rval, rprf) = evalRingEq.simplify(y)

          val typingAssumptions = typeChecking(getTypingsInAntecedent(have(lprf).bot.left) ++ 
                                               getTypingsInAntecedent(have(rprf).bot.left))
          val seqs = typingAssumptions + have(lprf) + have(rprf)
          // println(goal)
          
          have(goal) by Congruence.from(seqs.toSeq*)
          // val leftCongruence = have(x === simplify(x)) by Tautology
          // val rightCongruence = have(y === simplify(y)) by Tautology
        }
      
      
        case _ => proof.InvalidProofTactic("incomplete")
      }
    }
      
    //   {???}
    // }

  import BigIntToRingElem.i

  val evalAdd_test1 = Theorem(ring(R, <=, `+`, *, `-`, `0`, `1`) |- i(2) === i(2)){
    have(thesis) by evalRingEq.apply
  }


  val evalTest2 = Theorem(ring(R, <=, `+`, *, `-`, `0`, `1`) |- i(10) + i(5) === i(15)){
    have(thesis) by evalRingEq.apply


  }
  val evalAdd_test2 = Theorem(ring(R, <=, `+`, *, `-`, `0`, `1`) |- i(2) + i(2) === i(4)){
    have(thesis) by evalRingEq.apply
  }
  // val two_two_four = Theorem(ring(R, <=, `+`, *, `-`, `0`, `1`) |- i(2) + i(2) === i(4)){
  //   sorry
  // }

  inline def bigIntShorthand(x: BigInt): Expr[Ind] = {
    Variable(s"$x")
  }
  // inline def shorthandToBigInt(x: Expr[Ind]): BigInt = {
  //   x.
  // } 

  inline def bigIntEmbed(x: BigInt) : Expr[Prop] = {
    i(x) ∈ R
  }

 
  // println(Rings.ring.definition.statement)
  // println(order_refl.statement.left.getClass)
  // println(order_refl.statement.right)
  val test : Expr[Prop] = ∀(x, x ∈ R ==> x <= x)
  // println(test.getClass)
 



end Rings

