import scala.collection.immutable.{Set => SSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.{*, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution
import Base.{IBinFun, IUnFun, IRel, infixBinaryFunction, infixUnaryFunction}
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}
import Utils.*
// import lisa.utils.prooflib.WithTheorems.Proof.InvalidProofTactic
// import lisa.utils.prooflib.WithTheorems.Proof.ValidProofTactic
object RingStructure extends lisa.Main {
  implicit def intToExpr(x: BigInt): Expr[Ind] = {
    BigIntToRingElem.ic(x)
  }
  implicit def intToExpr(x: Int): Expr[Ind] = {
    BigIntToRingElem.ic(x)
  }
  val x   = variable[Ind]
  val y   = variable[Ind]
  val z   = variable[Ind]
  val w   = variable[Ind]
  val c   = variable[Ind]
  val `0` = variable[Ind]
  val `1` = variable[Ind]

  val R = variable[Ind] // ring base set
  val P = variable[Ind >>: Prop]
  
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
  
  
  object - extends Variable[Ind]("-"):
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
    // infix def <=(right : Expr[Ind]): Expr[Prop]  = RingStructure.<=.construct(left, right)
    // infix def |(right: Expr[Ind]):Expr[Prop]     = RingStructure.|.construct(left, right)
    // // this is probably not right?
    // def  - :Expr[Ind]                          = RingStructure.-.construct(left)
    // infix def  +(right : Expr[Ind]): Expr[Ind]   = RingStructure.+.construct(left, right)
    // infix def  *(right : Expr[Ind]): Expr[Ind]   = RingStructure.*.construct(left, right)
    infix def <=(right : Expr[Ind]): Expr[Prop]  = this.<=.construct(left, right)
    infix def |(right: Expr[Ind]):Expr[Prop]     = this.|.construct(left, right)
    // this is probably not right?
    def  - :Expr[Ind]                          = this.-.construct(left)
    infix def  +(right : Expr[Ind]): Expr[Ind]   = this.+.construct(left, right)
    infix def  *(right : Expr[Ind]): Expr[Ind]   = this.*.construct(left, right)
    infix def !==(right: Expr[Ind]): Expr[Prop] = !(left === right)
    def unary_- = this.-.construct(left)
    
  }


  

  // the definition of a ring of integers with the signature as above
  // the properties are listed here in full for reference
  object ring:
    // wrap the curried definition for convenience
    protected val ring = DEF( λ(R, λ(<=, λ(+, λ(*, λ(-, λ(|, λ(`0`, λ(`1`,
      <= ⊆ (R × R) /\
      (`+` :: (R × R -> R)) /\
      (* :: (R × R -> R)) /\
      (`-` :: (R -> R)) /\
      // identities over addition and multiplication
      (`0` ∈ R) /\ 
      (`1` ∈ R) /\
      // total order over Integers
        // TODO: change to LT?
        ∀(x, (x ∈ R) ==> x <= x) /\ // reflexivity
        ∀(x, ∀(y, ((x ∈ R) /\ (y ∈ R) /\ (x <= y) /\ (y <= x)) ==> (x === y))) /\ // antisymmetry
        ∀(x, ∀(y, ∀(z, ((x ∈ R) /\ (y ∈ R) /\ (z ∈ R) /\ (x <= y) /\ (y <= z)) ==> (x <= z)))) /\ // transitivity
        ∀(x, ∀(y, (x ∈ R) /\ (y ∈ R) ==> (x <= y) \/ (y <= x))) // totality 
        /\ (`0` <= `1`)
        /\ !(`0` === `1`) // note: does this need to be an axiom or a consequence of some other axiom??
      // TODO: add denseness to work in the rationals?
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
        ∀(x,  x ∈ R ==> ((x + (-(x))) === `0`)) 
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
      // nontriviality
      /\ ∃(x, ∃(y, x ∈ R /\ y ∈ R /\ !(x === y)))
      // create a very modest milestone
      // linear arithmetic normalization in rings
      // proofs such as x * 0 = x * (0 + 0)
      // divisibility axioms
      /\ ∀(x, ∀(y, (y | x) <=> ∃(c, (c ∈ R) /\ (x === y * c))))
      /\ ∀(x, x | `0`) // TODO: elim??
      // review this one
      // TODO: Add axiom !∃(c, c ∈ R /\ 0 < c /\ c < 1) -- use this to prove nondivisibility (d /| x + y in notes)
      // /\ 

      
    ))))))))).printAs(args => s"ring(${args.mkString(", ")})")

    inline def apply(R: Expr[Ind], leq: Expr[Ind], pl: Expr[Ind], st: Expr[Ind], mi: Expr[Ind], div: Expr[Ind], zero: Expr[Ind], one: Expr[Ind]): Expr[Prop] = ring(R)(leq)(pl)(st)(mi)(div)(zero)(one)

    def unapply(e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind], Expr[Ind])] = {
      e match
        case App(App(App(App(App(App(App(App(`ring`, r), leq), pl), st), mi), div), zero), one) => Some((r, leq, pl, st, mi, div, zero, one))
        case _ => None
      
    }

  // omega : bill pugh maryland
    inline def definition = ring.definition

  // we can instantiate and extract each of the properties for easier reuse
  // ∀ c ∈ R, !∃x ∈ R s.t. c < x < c + 1 
  // ∀ c ∈ R, ∀x ∈ R s.t. !(c < x) \/  !(x < c + 1) 
  // c < x -> c + 1 <= x
  // rewrite using ∀ in !∃
  // this is equivalent to ∀x, y ∈ R, x < y => x + 1 <= y 

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
   
  def forallify(l: LList[Variable[Ind]])(lhs: Expr[Prop])(r: Expr[Prop]): Expr[Prop] = 
    l.foldRight(lhs ==> r)((x, xs) => ∀(x, xs)) 

  def forallify(l: LList[Variable[Ind]])(r: Expr[Prop]): Expr[Prop] = 
    l.foldRight(r)((x, xs) => ∀(x, xs)) 

  // "by definition of the algebraic structure"
  object byRingDefn extends ProofTactic:
    def apply(using proof: library.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      if (!hasRingElem(goal.left)) then proof.InvalidProofTactic("Not a ring") else
      if (goal.right.toList.length != 1) then proof.InvalidProofTactic("right element should only be a string") else
        // evil lexicographical hack that forces a certain order on universal quantifiers
        // val fvs = freeVars(goal.left).toList.sortBy(x => x.id.name) // we want to be able to unpack items
        val fvs = freeVars(goal.left).toList.sortBy(x => x.id.name)
        // println(fvs)
        val statement: Expr[Prop] = goal.right.head
        val res = TacticSubproof:
          assume(ring(R, <=, +, *, -, |, `0`, `1`))
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
  
  val add_closure = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- ((x + y) ∈ R)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R)
    have(app(+)((x, y)) ∈ R) by Tautology.from(
      ring.definition, 
      appTyping of (f := +, x := (x, y), A := R × R, B := R), 
      CartesianProduct.membershipSufficientCondition of (A := R, B := R)
    )
    thenHave(thesis) by Substitution(infixBinaryFunction.definition of (f := +))
  }

  val mul_closure = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- ((x * y) ∈ R)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R)
    have(app(*)((x, y)) ∈ R) by Tautology.from(
      ring.definition, 
      appTyping of (f := *, x := (x, y), A := R × R, B := R), 
      CartesianProduct.membershipSufficientCondition of (A := R, B := R)
    )
    thenHave(thesis) by Substitution(infixBinaryFunction.definition of (f := *))
  }

  val neg_closure = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R) |- (-(x) ∈ R)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R)
    have(app(-)(x) ∈ R) by Tautology.from(
      ring.definition, 
      appTyping of (f := -, x := x, A := R, B := R), 
      // CartesianProduct.membershipSufficientCondition of (A := R, B := R)
    )
    thenHave(thesis) by Substitution(infixUnaryFunction.definition of (f := -))
  }

  val add_id_closure = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- `0` ∈ R){
    have(thesis) by byRingDefn.apply
  }

  val mul_id_closure = Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- `1` ∈ R){
    have(thesis) by byRingDefn.apply
  }
  val nmul_id_closure =Theorem(ring(R, <=, +, *, -, |, `0`, `1`) |- -(`1`) ∈ R){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    have(`1` ∈ R) by Tautology.from(mul_id_closure)
    have(-(`1`) ∈ R) by Tautology.from(lastStep, neg_closure of (x := `1`))
  } 
  val order_refl = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R) |- x <= x) {
    have(thesis) by byRingDefn.apply
  }
  
  val order_antisym = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, x <= y, y <= x) |- x === y){
    have(thesis) by byRingDefn.apply
  }


  val order_trans = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R) , (y ∈ R) , (z ∈ R) , (x <= y) , (y <= z)) |- x <= z){
    have(thesis) by byRingDefn.apply
  }

  val order_tot = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R) , (y ∈ R)) |- (x <= y) \/ (y <= x)){
    have(thesis) by byRingDefn.apply
  }

// ∀(x, y, z)
  val add_comm = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R) , (y ∈ R)) |- (x + y) === (y + x)){
    have(thesis) by byRingDefn.apply
  }

  val add_assoc = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R) , (y ∈ R), (z ∈ R)) |- ((x + y) + z) === (x + (y + z))){
    have(thesis) by byRingDefn.apply
  }

  val add_id    = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (x === (`0` + x))){ 
    have(thesis) by byRingDefn.apply 
  }

  val add_inv   = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- ((x + (-(x))) === `0`)){
    have(thesis) by byRingDefn.apply 
  }
  val add_comm_inv =  Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- ((-x + x) === `0`)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val h1 = have(-x ∈ R) by Tautology.from(neg_closure of (x := x))
    val h2 = have(x + -x === -x + x) by Tautology.from(add_comm of (x := x, y := -x), lastStep)
    val h3 = have(x + -x === `0`) by Tautology.from(add_inv of (x := x))
    have(-x + x === `0`) by Congruence.from(h2, h3)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3)
  }

  val mul_assoc = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R)) |- ((x * (y * z)) === ((x * y) * z))){
    have(thesis) by byRingDefn.apply
  }
  
  val mul_id_right = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (x === (`1` * x))){
    have(thesis) by byRingDefn.apply 
  }
  
  val mul_comm = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- (x * y) === (y * x)){
    have(thesis) by byRingDefn.apply 
  }

  val mul_id_left =  Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (x === (x * `1`))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val v1 = have(x === (`1` * x)) by Tautology.from(mul_id_right)
    val v2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val v3 = have((`1` * x === x * `1`)) by Tautology.from(v2, mul_comm of (x := x, y := `1`))
    have(thesis) by Congruence.from(v1, v3)
  }

  // /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> ((x * (y + z)) === ((x * y) + (x * z))))))
  //     /\ ∀(x, ∀(y, ∀(z, x ∈ R /\ y ∈ R /\ z ∈ R ==> (((y + z) * x) === ((x * y) + (x * z))))))

  val mul_dist_left = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R)) |- ((x * (y + z)) === ((x * y) + (x * z)))){
    have(thesis) by byRingDefn.apply 
  }

  val mul_dist_right = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R)) |- (((y + z) * x) === ((y * x) + (z * x)))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
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

  val divisibility_defn = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- ((y | x) <=> ∃(c, (c ∈ R) /\ (x === y * c)))){
    have(thesis) by byRingDefn.apply
  }

  val div_prod  =  Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- (y | (y * x))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)

    val xyinR = have((y * x) ∈ R) by Tautology.from(mul_closure of (x := y, y := x))
    have(x ∈ R /\ (y*x === y*x)) by Tautology
    thenHave(∃(c, c ∈ R /\ (y*x === y*c))) by RightExists
    have(y | (y * x)) by Tautology.from(lastStep, xyinR, divisibility_defn of (x := (y * x), y := y, c := x))
  }
  // val all_div_zero = Theorem()
  val div_lcm_removal = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (y ∈ R), ∃(x, (x ∈ R) /\ P(y * x))) |- ∃(x, (x ∈ R) /\ (y | x) /\ P(x))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(y ∈ R)

    val xyinR = have((x ∈ R) |- (y * x) ∈ R) by Tautology.from(mul_closure of (x := y, y := x))
    val v = have((x ∈ R) |- (y | (y * x))) by Tautology.from(div_prod)
    have((x ∈ R) /\ P(y * x) |- P(y * x)) by Restate
    have((x ∈ R) /\ P(y * x) |- P(y * x) /\ (y | (y * x))) by Tautology.from(v, lastStep)
    have((x ∈ R) /\ P(y * x) |- (y * x) ∈ R /\ P(y * x) /\ (y | (y * x))) by Tautology.from(xyinR, lastStep)
    thenHave((x ∈ R) /\ P(y * x) |- ∃(x, x ∈ R /\ P(x) /\ (y | x))) by RightExists
    thenHave(thesis) by LeftExists
  }

  val zero_x_x  = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (x === (`0` + x))){ 
    have(thesis) by Tautology.from(add_id)
  }

  val x_zero_x  = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (x === (x + `0`))){ 
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val a = have(`0` ∈ R) by Tautology.from(add_id_closure)
    val b = have((x + `0`) ∈ R) by Tautology.from(add_closure of (x := x, y := `0`), a)
    have(x === (x + `0`)) by Congruence.from(add_id, add_comm of (x := x, y := `0`), a, b)
    have(thesis) by Tautology.from(lastStep, a, b)
  }
  
  val cong_test = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R), (x === y)) |- (x + z) === (y + z)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R), (x === y))
    val v1 = have((x + z) ∈ R) by Tautology.from(add_closure of (x:= x, y:=z))
    val v2 = have((y + z) ∈ R) by Tautology.from(add_closure of (x:= y, y:=z))
    have(thesis) by Congruence.from(v1, v2)
  }

  val nontriviality = Theorem((ring(R, <=, +, *, -, |, `0`, `1`) ) |- ∃(x, ∃(y, x ∈ R /\ y ∈ R /\ !(x === y)))){
    have(thesis) by byRingDefn.apply
  }

  
 

  val mult_zero_x_zero = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (`0` * x === `0`)) {
    assume(x ∈ R)
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    val zero_r = have(`0` ∈ R) by Tautology.from(add_id_closure)
    val p0xr = have((`0` * x) ∈ R) by Tautology.from(zero_r, mul_closure of (x := `0`, y := x))
    val m0xr = have(-(`0` * x) ∈ R) by Tautology.from(neg_closure of (x := (`0` * x)), lastStep)
    
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
    val s4 = have((`0` * x) + -(`0` * x) === ((`0` * x) + (`0` * x)) + -(`0` * x)) by Congruence.from(lastStep)
    val s5 = have((`0` * x) + -(`0` * x) === `0`) by Tautology.from(add_inv of (x := (`0` * x)), p0xr, m0xr)
    val s6 = have((( (`0` * x) + (`0` * x) ) + (-(`0` * x))) === ( (`0` * x) + ( (`0` * x) + (-(`0` * x)) ))) by Tautology.from(p0xr, m0xr, add_assoc of (x := (`0` * x), y := (`0` * x), z := (-(`0` * x))))
    val s7 = have(((`0` * x) + ((`0` * x) + -(`0` * x))) === ((`0` * x) + `0`)) by Congruence.from(s5)
    val s8 = have((`0` * x) === (`0` + (`0` * x))) by Tautology.from(p0xr, add_id of (x := (`0` * x)), zero_r)
    val s9 = have( (`0` + (`0` * x)) ===  ((`0` * x) + `0`)) by Tautology.from(add_comm of (x:= `0`, y := (`0` * x)), zero_r, p0xr)
    have(thesis) by Congruence.from(s9, s8, s7, s6, s5, s4)
  }

  val mult_x_zero_zero = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (x * 0 === 0)) {
    assume(x ∈ R)
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    val zero_r = have(`0` ∈ R) by Tautology.from(add_id_closure)

    val h1 = have(x * 0 === 0 * x) by Tautology.from(mul_comm of (x := x, y := 0), zero_r)
    val h2 = have(0 * x === 0) by Tautology.from(mult_zero_x_zero)
    have(x * 0 === 0) by Congruence.from(h1, h2)
    have(thesis) by Tautology.from(h1, h2, lastStep)
  } 

  val double_negation_elimination = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R)) |- (-(-(x)) === x)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R))
    val n1 = have(-(x) ∈ R) by Tautology.from(neg_closure of (x := x))
    val n2 = have(-(-(x)) ∈ R) by Tautology.from(neg_closure of (x := -(x)), n1)

    have(-(x) + -(-(x)) === `0`) by Tautology.from(add_inv of (x := -(x)), n1)
   
    have(((x + -(x)) + -(-(x))) === x) by Congruence.from(lastStep, x_zero_x of (x := x), n1, n2, 
                                                               add_assoc of (x := x, y := -(x), z := -(-(x))))
    have(-(-(x)) === x) by Congruence.from(lastStep, add_inv of (x := x), zero_x_x of (x := -(-(x))), n1, n2)
    have(thesis) by Tautology.from(n1, n2, lastStep)
  }

  
  val neg_x_y_neg_xy = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- (-(x) * y) === -(x * y)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R))
    val h1 = have((x * y) ∈ R) by Tautology.from(mul_closure)
    // Discharge(h1)
    val h2 = have(-(x * y) ∈ R) by Tautology.from(neg_closure of (x := (x * y)), h1)
    val h3 = have(-(x) ∈ R) by Tautology.from(neg_closure)
    val h4 = have((-(x) * y) ∈ R) by Tautology.from(h3, mul_closure of (x:= -(x)))
    val h5 = have(`0` ∈ R) by Tautology.from(add_id_closure)
    have((x + -(x)) === `0`) by Tautology.from(add_inv)
    val v2 = have((x + -(x)) * y === `0` * y) by Congruence.from(lastStep)
    have(`0` * y  === `0`) by Tautology.from(mult_zero_x_zero of (x := y))
    have((x + -(x)) * y === `0`) by Congruence.from(lastStep, v2)
    have(((x * y) + (-(x) * y)) === `0`) by Congruence.from(lastStep, h3, mul_dist_right of (y := x, z := -(x), x := y))
    have(((-(x) * y) + (x * y)) === `0`) by Congruence.from(h1, h2, h3, h4, add_comm of (x := (x * y), y:= (-(x) * y)), lastStep)
    have(((-(x) * y) + (x * y)) + -(x * y) === -(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, h5, add_id of (x := (-(x * y))))
    have((-(x) * y) + ((x * y) + -(x * y)) === -(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, add_assoc of (x := (-(x) * y), y := (x * y), z := -(x * y)))
    have((-(x) * y) + ((x * y) + -(x * y)) === -(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, add_assoc of (x := (-(x) * y), y := (x * y), z := -(x * y)))
    have((-(x) * y) + (`0`) === -(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, add_inv of (x := (x * y)))
    have(`0` + (-(x) * y) === -(x * y)) by Congruence.from(lastStep, h1, h2, h3, h4, h5, add_comm of (x := (-(x) * y), y := `0`))
    have((-(x) * y) === -(x * y)) by Congruence.from(lastStep, add_id of (x := (-(x) * y)), h1, h2, h3, h4, h5)     
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5)
  }

  val neg_x_neg_y_xy = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- (-(x) * -(y)) === (x * y)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R))
    val h1 = have((x * y) ∈ R) by Tautology.from(mul_closure)
    val h2 = have(-(x * y) ∈ R) by Tautology.from(neg_closure of (x := (x * y)), h1)
    val h3 = have(-(x) ∈ R) by Tautology.from(neg_closure)
    val h4 = have(-(y) ∈ R) by Tautology.from(neg_closure of (x := y))
    val h5 = have((-(x) * -(y)) ∈ R) by Tautology.from(h3, mul_closure of (x:= -(x), y := -(y)), h3, h4)
    val h6 = have(`0` ∈ R) by Tautology.from(add_id_closure)

    have((-(x) * -(y)) === -(x * -(y))) by Tautology.from(neg_x_y_neg_xy of (y := -(y)), h4)
    have((-(x) * -(y)) === (x * y)) by Congruence.from(lastStep, mul_comm of (y := -(y)), h1, h2, h3, h4, 
                                                                  mul_comm, 
                                                                  neg_x_y_neg_xy of (x := y, y := x),
                                                                  double_negation_elimination of (x := (x * y)))
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5)

  
  }

  val negation_dist_add = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- -(x + y) === -(x) + -(y)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R))
    val h1 = have((x + y) ∈ R) by Tautology.from(add_closure)
    val h2 = have(-(x + y) ∈ R) by Tautology.from(neg_closure of (x := (x + y)), h1)
    val h3 = have(-(x) ∈ R) by Tautology.from(neg_closure)
    val h4 = have(-(y) ∈ R) by Tautology.from(neg_closure of (x := y))
    val h5 = have((-(x) + -(y)) ∈ R) by Tautology.from(h3, add_closure of (x:= -(x), y := -(y)), h3, h4)
    val h6 = have(`0` ∈ R) by Tautology.from(add_id_closure)
    val h7 = have((x + -(x)) ∈ R) by Tautology.from(add_closure of (x := x, y := -(x)), h3)
    val h8 = have((y + -(y)) ∈ R) by Tautology.from(add_closure of (x := y, y := -(y)), h4)

    have((x + -(x)) === `0`) by Tautology.from(add_inv)
    have((x + -(x)) + (y + -(y)) === `0`) by Congruence.from(lastStep, 
                                                    add_inv of (x := y), 
                                                    zero_x_x of (x := (y + -(y))))
    have(((x + -(x)) + y) + -(y) === `0`) by Congruence.from(lastStep, 
                                                                 add_assoc of (x := (x + -(x)), y := y, z := -(y)),
                                                                h7, h4)
    // have((x + y) + (-(x) + -(y)) === `0`)  by Congruence.from(lastStep, 
    have((x + (y + -(x))) + -(y) === `0`)  by Congruence.from(lastStep, 
                                                          add_assoc of (x := (x), y := -(x), z := y),
                                                          add_comm of (x := -(x), y := y),
                                                          // add_assoc of (x := x, y := y, z := (-(x))),
                                                          // add_assoc of (x := (x + y), y := -(x), z := -(y)),
                                                          h1, h2, h3, h4, h5, h6, h7, h8)
    have((x + y) + (-(x) + -(y)) === `0`) by Congruence.from(lastStep, 
                                                          add_assoc of (x := x, y := y, z := (-(x))),
                                                          add_assoc of (x := (x + y), y := -(x), z := -(y)),
                                                          h1, h2, h3, h4, h5, h6, h7, h8)

    have((-(x) + -(y))  === -(x + y)) by Congruence.from(lastStep,
                                                                        x_zero_x of (x := -(x + y)),
                                                                        add_assoc of (x := -(x + y), y := (x + y), z := (-(x) + -(y))),
                                                                        add_comm of (x := -(x + y), y := (x + y)),
                                                                        add_inv of (x := (x + y)),
                                                                        zero_x_x of (x := (-(x) + -(y))),
                                                                        h1, h2, h3, h4, h5, h6, h7, h8)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5, h6, h7, h8)
  }
  val negation_zero = Theorem((ring(R, <=, +, *, -, |, `0`, `1`)) |- -(`0`) === `0`){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    val h6 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h7 = have(-(`0`) ∈ R) by Tautology.from(neg_closure of (x := `0`), h6)
    have(-(`0`) === `0`) by Congruence.from(lastStep, add_inv of (x := `0`), h6, h7, zero_x_x of (x := -(`0`)))
    have(thesis) by Tautology.from(lastStep, h6, h7)
  }

  val one_mone_xs_xs = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R) |- `1` + (-(`1`) + x) === x){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    val h4 = have(`1` + (-(`1`) + x) === (`1` + -(`1`)) + x) by Tautology.from(h2, h3, add_assoc of (x := `1`, y := -(`1`), z := x))
    val h5 = have((`1` + -(`1`)) === `0`) by Tautology.from(add_inv of (x := `1`), h2)
    val h6 = have(`0` + x === x) by Tautology.from(zero_x_x)
    val res1 = have((`1` + -(`1`)) + x === (`1` + -(`1`)) + x).bot
    // assume equalities
    val equalities = Seq(h4.bot, h5.bot, h6.bot).map(x => x.firstElemR).toSet
    have(equalities |- (`1` + -(`1`)) + x === (`1` + -(`1`)) + x) by Tautology
    thenHave(equalities |- ((`1` + -(`1`)) + x  === `0` + x)) by RightSubstEq.withParameters(
      Seq(((`1` + -(`1`)), `0`)),
      (Seq(a), (`1` + -(`1`)) + x === a + x)
    )
    thenHave(equalities |- `1` + (-(`1`) + x) === `0` + x) by RightSubstEq.withParameters(
      Seq((`1` + (-(`1`) + x), (`1` + -(`1`)) + x)),
      (Seq(a), a === `0` + x)
    )
    thenHave(equalities |- `1` + (-(`1`) + x) === x) by RightSubstEq.withParameters(
      Seq((`0` + x, x)),
      (Seq(a), `1` + (-(`1`) + x) === a)
    )
  
    have(thesis) by Tautology.from(lastStep, h4, h5, h6)
  }
  
  val mone_one_xs_xs =  Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R) |- -(`1`) + (`1` + x) === x){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    val h4 = have(-(`1`) + (`1` + x) === (-(`1`) + `1`) + x) by Tautology.from(h2, h3, add_assoc of (x := -(`1`), y := `1`, z := x))
    val h5 = have((-(`1`) + `1`) === (`1` + -(`1`))) by Tautology.from(h2, h3, add_comm of (x := `1`, y := -(`1`)))
    val h6 = have(`1` + (-(`1`) + x) === (`1` + -(`1`)) + x) by Tautology.from(h2, h3, add_assoc of (x := `1`, y := -(`1`), z := x))

    have(-(`1`) + (`1` + x) === `1` + (-(`1`) + x)) by Congruence.from(h1, h2, h3, h4, h5, h6)
    have(-(`1`) + (`1` + x) === x) by Congruence.from(lastStep, one_mone_xs_xs)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5, h6)
  }


  val mz_z_x_x = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, z ∈ R) |- -(z) + (z + x) === x) {
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(z ∈ R)
    // val = 3
    val h2 = have(-(z) ∈ R) by Tautology.from(neg_closure of (x := z))

    val h4 = have(-(z) + (z + x) === (-(z) + z) + x) by Tautology.from(h2, add_assoc of (x := -(z), y := z, z := x))
    val h5 = have((-(z) + z) === (z + -(z))) by Tautology.from(h2, add_comm of (x := z, y := -(z)))
    val h6 = have(z + (-(z) + x) === (z + -(z)) + x) by Tautology.from(h2, add_assoc of (x := z, y := -(z), z := x))
    
    val h7 = have((z + -(z)) === `0`) by Tautology.from(add_inv of (x := z))
    val h8 = have(`0` + x === x) by Tautology.from(zero_x_x)
    have(-(z) + (z + x) === x) by Congruence.from(h2, h4, h5, h6, h7, h8)
    have(thesis) by Tautology.from(lastStep, h2, h4, h5, h6, h7, h8)

  }

  val z_mz_x_x = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, z ∈ R) |- z + (-z + x) === x){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(z ∈ R)
    val h1 = have(-z ∈ R) by Tautology.from(neg_closure of (x := z))
    val h2 = have(-(-z) + (-z + x) === x) by Tautology.from(mz_z_x_x of (z := -z), h1)
    val h3 = have(-(-z) === z) by Tautology.from(double_negation_elimination of (x := z))
    have(z + (-z + x) === x) by Congruence.from(h1, h2, h3)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3) 
  }

  val addPlusHelper1g = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |- (z + x) + (-(z) + y) === x + y){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h3 = have(-z ∈ R) by Tautology.from(neg_closure of (x := z))
    val h4 = have(z + x === x + z) by Tautology.from(add_comm of (x := z, y := x))
    val h5 = have((x + z) ∈ R) by Tautology.from(add_closure of (x := x, y := z))
    val h6 = have((-(z) + y) ∈ R) by Tautology.from(add_closure of (x := -(z), y := y), h3)
    val h7 = have(((x + z) + (-(z) + y)) === (x + (z + (-(z) + y)))) by Tautology.from(h5, h6, add_assoc of (x := x, y := z, z := (-(z) + y)))
    val h8 = have(z + (-(z) + y) === y) by Tautology.from(z_mz_x_x of (x := y))
    have((z + x) + (-(z) + y) === x + y) by Congruence.from(h1, h3, h4, h5, h6, h7, h8)
    have(thesis) by Tautology.from(lastStep, h1, h3, h4, h5, h6, h7, h8)
  }

  val addPlusHelper2g = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |- (-(z) + x) + (z + y) === x + y){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h3 = have(-z ∈ R) by Tautology.from(neg_closure of (x := z))
    val h4 = have(-z + x === x + -z) by Tautology.from(add_comm of (x := -z, y := x), h3)
    val h5 = have((x + -z) ∈ R) by Tautology.from(add_closure of (x := x, y := -z), h3)
    val h6 = have((z + y) ∈ R) by Tautology.from(add_closure of (x := z, y := y))
    val h7 = have(((x + -z) + (z + y)) === (x + (-z + (z + y)))) by Tautology.from(h5, h6, add_assoc of (x := x, y := -z, z := (z + y)), h3)
    val h8 = have(-z + (z + y) === y) by Tautology.from(mz_z_x_x of (x := y))
    have((-z + x) + (z + y) === x + y) by Congruence.from(h1, h3, h4, h5, h6, h7, h8)
    have(thesis) by Tautology.from(lastStep, h1, h3, h4, h5, h6, h7, h8)
  }

  val addPlusHelper1 = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (`1` + x) + (-(`1`) + y) === x + y){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    val h4 = have(`1` + x === x + `1`) by Tautology.from(add_comm of (x := `1`, y := x), h2)
    val h5 = have((x + `1`) ∈ R) by Tautology.from(add_closure of (x := x, y := `1`), h2)
    val h6 = have((-(`1`) + y) ∈ R) by Tautology.from(add_closure of (x := -(`1`), y := y), h3)
    val h7 = have(((x + `1`) + (-(`1`) + y)) === (x + (`1` + (-(`1`) + y)))) by Tautology.from(h5, h6, h2, add_assoc of (x := x, y := `1`, z := (-(`1`) + y)))
    val h8 = have(`1` + (-(`1`) + y) === y) by Tautology.from(one_mone_xs_xs of (x := y))
    have((`1` + x) + (-(`1`) + y) === x + y) by Congruence.from(h1, h2, h3, h4, h5, h6, h7, h8)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5, h6, h7, h8)
  }

  val addPlusHelper2 = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (-(`1`) + x) + (`1` + y) === x + y){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    val h4 = have(((`1`) + y) ∈ R) by Tautology.from(add_closure of (x := `1`, y := y), h2)
    val h5 = have((-(`1`) + x) ∈ R) by Tautology.from(add_closure of (x := -(`1`), y := x), h3)
    val h6 = have((-(`1`) + x) + ((`1`) + y)  === ((`1`) + y)  + (-(`1`) + x)) by Tautology.from(h4, h5, add_comm of (x := ((`1`) + y) , y := (-(`1`) + x)))
    val h7 = have(((`1`) + y)  + (-(`1`) + x) === y + x) by Tautology.from(addPlusHelper1 of (x := y, y := x))
    have((-(`1`) + x) + (`1` + y) === x + y) by Congruence.from(h1, h2, h3, h4, h5, h6, h7, add_comm)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h4, h5, h6, h7, add_comm)
  }

  val addPlusHelper3p = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R, w ∈ R) |- (z + x) + (w + y) === x + (z + (w + y))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    assume(w ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h3 = have(-(z) ∈ R) by Tautology.from(neg_closure of (x := z))
    val h4 = have((z + x) ∈ R) by Tautology.from(add_closure of (x := z, y := x))
    val h5 = have((w + y) ∈ R) by Tautology.from(add_closure of (x := w, y := y))
    val h6 = have((z + x)  === (x + z)) by Tautology.from(add_comm of (x := z, y := x))
    val h6p = have((z + x) + (w + y) === (z + x) + (w + y)) by Restate
    val h7 = have((z + x) + (w + y) === (x + z) + (w + y)) by Congruence.from(h6, h6p)
    val h7p = have((x + z) + (w + y) === x + (z + (w + y))) by Tautology.from(add_assoc of (x := x, y := z, z := w + y), h5)

    have((z + x) + (w + y) === x + (z + (w + y))) by Congruence.from(h1, h3, h4, h5, h6, h6p, h7, h7p)
    have(thesis) by Tautology.from(h1, h3, h4, h5, h6, h7, h7p, lastStep)
  }

  val addPlusHelper3 = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (`1` + x) + (`1` + y) === x + (`1` + (`1` + y))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    have(thesis) by Tautology.from(addPlusHelper3p of (x := x, y := y, z := `1`, w := `1`), h2)
  }
  val addPlusHelper4 = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (-(`1`) + x) + (-(`1`) + y) === x + (-(`1`) + (-(`1`) + y))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    have(thesis) by Tautology.from(addPlusHelper3p of (x := x, y := y, z := -(`1`), w := -`1`), h3)
  }
  
  val addInsertHelper = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |- x + (y + z) === y + (x + z)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    val h1 = have(x + y === y + x) by Tautology.from(add_comm of (x := x, y := y))
    val h2 = have(x + (y + z) === (x + y) + z) by Tautology.from(add_assoc of (x := x, y := y, z := z)) 
    val h3 = have((y + x) + z === y + (x + z)) by Tautology.from(add_assoc of (x := y, y := x, z := z))
    have(x + (y + z) === y + (x + z)) by Congruence.from(h1, h2, h3)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3)
  }

  // thank you past me
  val mult_neg1_x_negx = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R) |- -(`1`)*x === -(x)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val h1 = have(`0` ∈ R) by Tautology.from(add_id_closure) 
    val h2 = have(`1` ∈ R) by Tautology.from(mul_id_closure)
    val h3 = have(-(`1`) ∈ R) by Tautology.from(neg_closure of (x := `1`), h2)
    val h5 = have((-(`1`))*x === -(`1` * x)) by Tautology.from(neg_x_y_neg_xy of (x := (`1`), y := x), h2)
    val h6 = have(`1` * x === x) by Tautology.from(mul_id_right)
    have(-(`1`)*x === -(x)) by Congruence.from(h1, h2, h3, h5, h6)
    have(thesis) by Tautology.from(lastStep, h1, h2, h3, h5, h6)
  }
  val mult_x_neg1_negx = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R) |- x*(-1) === -(x)){
    assume(x ∈ R)
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    val id_r = have(1 ∈ R) by Tautology.from(mul_id_closure)
    val nid_r = have(-1 ∈ R) by Tautology.from(neg_closure of (x := 1), id_r)
    val h1 = have(x * -1 === -1 * x) by Tautology.from(mul_comm of (x := x, y := -1), nid_r)
    val h2 = have(-1 * x === -x) by Tautology.from(mult_neg1_x_negx)
    have(x * -1 === -x) by Congruence.from(h1, h2)
    have(thesis) by Tautology.from(h1, h2, lastStep)
  }

  val zero_eq_1_implies_triviality = Theorem((ring(R, <=, +, *, -, |, `0`, `1`) , 0 === 1, c ∈ R) |- (c === 0)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    val v = assume(0 === 1)
    val s1 = have(c ∈ R |- c*1 === c) by Tautology.from(mul_id_left of (x := c))
    val s2 = have(c ∈ R |- c*`0` === `0`) by Tautology.from(mult_x_zero_zero of (x := c))
    val s3 = have(c ∈ R |- c*1 === c*0) by Congruence.from(v)
    val s4 = have(c ∈ R |- c === 0) by Congruence.from(s1, s2, s3, v)
    have(thesis) by Tautology.from(s1, s2, s3, s4, v)

  }

   val zero_neq_1 = Theorem((ring(R, <=, +, *, -, |, `0`, `1`) ) |- (0 !== 1)){
    assume(ring(R, <=, +, *, -, |, `0`, `1`))
    val h0 = have(0 ∈ R) by Tautology.from(add_id_closure)
    val h1 = have(1 ∈ R) by Tautology.from(mul_id_closure)
    val res1 = have(0 ∈ R /\ 1 ∈ R) by Tautology.from(h0, h1)
    // have(0 !== 1) by Tautology
    sorry
  }
  

  val x_y_1x_1y = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (x === y) <=> (1 + x === 1 + y))
  val x_lt_y_iff_p1 = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (x <= y) <=> (1 + x <= 1 + y))

  val does_not_divide = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |- (z | x) ==> ∀(y, y ∈ R /\ (1 <= y) /\ (y <= (z + -1)) /\ !(z | (x + y))))
  object BigIntToRingElem{
    def i(x : BigInt) : Expr[Ind] = {
      if x < 0 then 
        -.construct(i(-x))
      else if x > 0 then
        `1` + i(x - 1)
      else 
        `0`
    }
    def ic(x : BigInt) : Expr[Ind] = {
      x match {
        case x if x == BigInt(0) => `0`
        case x if x == BigInt(1) => `1`
        case x if x == BigInt(-1)  => -(`1`)
        case x if x > 0 => `1` + ic(x - 1)
        case x if x < 0 => -(`1`) + ic(x + 1)
      } 
    }
  }


  
  def canonical_sum(x: Expr[Ind]): Boolean = {
    x match {
      case `0` => true
      case `1` + xs => canonical_sum(xs)
      case _ => false
    }
  }
  // val w = x === y
  // hint; use structuralToString
  // println(w.getClass)
  

  



  val succ_succ_lr   = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R), (z ∈ R), (x + y === z)) |- (`1` + x) + y === (`1` + z)){
    assume(goal.left.toSeq*)
    have(thesis) by Congruence.from(add_assoc of (x := `1`, y := x, z := y),
                                    (have(`1` ∈ R) by Tautology.from(mul_id_closure)))
  }

  

  val succ_succ_defn = Theorem((ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R)) |- (`1` + x) + (`1` + y) === (`1` + (`1` + (x + y)))){
    assume(ring(R, <=, +, *, -, |, `0`, `1`), (x ∈ R), (y ∈ R))
    // have(`1` ∈ R) by Restate.from(add_id_closure)
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
}
// end RingStructure