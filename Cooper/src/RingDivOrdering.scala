import scala.collection.immutable.{Set => SSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, P => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution
import Base.{IBinFun, IUnFun, IRel, infixBinaryFunction, infixUnaryFunction}
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}
import Utils.*

object RingDivOrdering extends lisa.Main {
  import RingStructure.*
    
  val zero_eq_1_implies_triviality = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`) , 0 === 1, c ∈ R) |- (c === 0)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    val v = assume(0 === 1)
    val s1 = have(c ∈ R |- c*1 === c) by Tautology.from(mul_id_left of (x := c))
    val s2 = have(c ∈ R |- c*`0` === `0`) by Tautology.from(mult_x_zero_zero of (x := c))
    val s3 = have(c ∈ R |- c*1 === c*0) by Congruence.from(v)
    val s4 = have(c ∈ R |- c === 0) by Congruence.from(s1, s2, s3, v)
    have(thesis) by Tautology.from(s1, s2, s3, s4, v)
  }

  val triviality_lemma = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`) , 0 === 1) |- ∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x === y)))){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(0 === 1)
    val aic = have(0 ∈ R) by Tautology.from(add_id_closure)
    val v1 = have(c ∈ R |- (c === 0)) by Tautology.from(zero_eq_1_implies_triviality)
    have(c ∈ R ==> (c === 0)) by Tautology.from(lastStep)
    val v0 = thenHave(∀(c, (c ∈ R) ==> (c === 0))) by RightForall
    val vx = have((x ∈ R) ==> (x === 0)) by InstantiateForall(x)(v0)
    val vy = have((y ∈ R) ==> (y === 0)) by InstantiateForall(y)(v0)
    val v2 = have(x ∈ R |- x === 0) by Tautology.from(vx)
    val v3 = have(y ∈ R |- y === 0) by Tautology.from(vy)
    // have((0 ∈ R /\ c ∈ R) ==> (c === 0)) by  Tautology.from(lastStep)
    val v4 = have((x ∈ R, y ∈ R) |- x === y) by Congruence.from(v2, v3)
    val v5 = have((x ∈ R /\ y ∈ R) ==> (x === y)) by Tautology.from(lastStep)
    thenHave(∀(y, (x ∈ R /\ y ∈ R) ==> (x === y))) by RightForall
    thenHave(thesis) by RightForall
  }

  val lem_inst = Theorem(!(∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x === y)))) |- (∃(x, ∃(y, (x ∈ R /\ y ∈ R) /\ !(x === y))))){
    have(thesis) by Tableau
  }

  val lem_inst2 = Theorem((∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x === y)))) |- !(∃(x, ∃(y, (x ∈ R /\ y ∈ R) /\ !(x === y))))){
    have(thesis) by Tableau
  }

  val zero_neq_1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`) ) |- (0 !== 1)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    // val h0 = have(0 ∈ R) by Tautology.from(add_id_closure)
    // val h1 = have(1 ∈ R) by Tautology.from(mul_id_closure)
    // val res1 = have(0 ∈ R /\ 1 ∈ R) by Tautology.from(h0, h1)
    // have(0 !== 1) by Tautology
    val t1 = have((0 === 1) |- ∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x === y)))) by Tautology.from(triviality_lemma)
    val t2 = have(∀(x, ∀(y, (x ∈ R /\ y ∈ R) ==> (x === y))) |- !(∃(x, ∃(y, (x ∈ R /\ y ∈ R) /\ !(x === y))))) by Tautology.from(lem_inst2)
    val t3 = have(∃(x, ∃(y, (x ∈ R /\ y ∈ R) /\ !(x === y)))) by Tautology.from(nontriviality)
    have(thesis) by Tautology.from(t1, t2, t3)
  }
  
  /*
  ∀(x, (x ∈ R) ==> x <= x) /\ // reflexivity
  ∀(x, ∀(y, ((x ∈ R) /\ (y ∈ R) /\ (x <= y) /\ (y <= x)) ==> (x === y))) /\ // antisymmetry
  ∀(x, ∀(y, ∀(z, ((x ∈ R) /\ (y ∈ R) /\ (z ∈ R) /\ (x <= y) /\ (y <= z)) ==> (x <= z)))) /\ // transitivity
  ∀(x, ∀(y, (x ∈ R) /\ (y ∈ R) ==> (x <= y) \/ (y <= x))) /\ // totality 
  ∀(x, ∀(y, (x ∈ R) /\ (y ∈ R) ==> ((x < y) <=> ((x <= y) /\ !(y < x))))) // strict order
  */

  val le_refl = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- x <= x){
    have(thesis) by byRingDefn.apply
  }
  val le_antisym = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (x <= y) /\ (y <= x) ==> (x === y)){
    have(thesis) by byRingDefn.apply
  }
  val le_trans = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |- ((x <= y) /\ (y <= z)) ==> (x <= z)){
    have(thesis) by byRingDefn.apply
  }
  val le_totality = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (x <= y) \/ (y <= x)){
    have(thesis) by byRingDefn.apply
  }
  val lt_defn = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- ((x < y) <=> ((x <= y) /\ !(y <= x)))){
    have(thesis) by byRingDefn.apply
  }

  val le_antisym_conv = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, (x === y)) |-  ((x <= y) /\ (y <= x))) {
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume((x === y))
    val p = have(x <= x) by Tautology.from(le_refl)
    val p1 = thenHave(x <= y) by Congruence
    val p2 = have(y <= x) by Congruence.from(p)
    have(thesis) by RightAnd(p1, p2)
  }

  val le_antisym_iff = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (x === y) <=> ((x <= y) /\ (y <= x))){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    have(thesis) by Tautology.from(le_antisym_conv, le_antisym)
  }

  val zero_le_1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- (`0` <= 1)){
    have(thesis) by byRingDefn.apply
  }

  val zero_lt_1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`)) |- 0 < `1`){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    // have(0 <= `1`) by Tautology.from(zero_le_1)
    // have(0 !== 1) by Tautology.from(zero_neq_1)
    have((0 === 1) <=> ((0 <= `1`) /\ (`1` <= 0))) by Tautology.from(le_antisym_iff of (x := 0, y := 1), add_id_closure, mul_id_closure)
    have(!(0 === 1) <=> (!(0 <= `1`) \/ !(`1` <= 0))) by Tautology.from(lastStep)
    have((0 !== 1) <=> (!(0 <= `1`) \/ !(`1` <= 0))) by Tautology.from(lastStep)
    have(!(`1` <= 0)) by Tautology.from(lastStep, zero_le_1, zero_neq_1)
    have((`0` <= 1) /\ !(`1` <= 0)) by Tautology.from(lastStep, zero_le_1)
    have(thesis) by Tautology.from(lastStep, add_id_closure, mul_id_closure, lt_defn of (x := 0, y := 1))
  }

  val lt_nrefl = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- !(x < x)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    have(thesis) by Tautology.from(le_refl, lt_defn of (x := x, y := x))
  }

  val lt_implies_neq = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, x < y) |- !(x === y)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(x < y)
    have((x <= y) /\ !(y <= x)) by Tautology.from(lt_defn)
    have(thesis) by Tautology.from(le_antisym_iff, lastStep)
  }

  val lt_not_sym = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, x < y) |- !(y < x)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(x < y)
    val p = have((x <= y) /\ !(y <= x)) by Tautology.from(lt_defn)
    have(thesis) by Tautology.from(p, lt_defn of (x := y, y := x))
  }

  val trichotomy1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, x < y) |- !(y < x) /\ !(y === x)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(x < y)
    have(thesis) by Tautology.from(lt_implies_neq, lt_not_sym)
  }
  val trichotomy2 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, y < x) |- !(x < y) /\ !(y === x)){
    have(thesis) by Tautology.from(trichotomy1 of (x := y, y := x))
  }
  val trichotomy3 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, x === y) |- !(x < y) /\ !(y < x)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(x === y)
    have(thesis) by Tautology.from(lt_defn, lt_defn of (x := y, y := x), le_antisym_iff)
  }

  val le_neg = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, !(x <= y)) |- y < x){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(!(x <= y))
    have(thesis) by Tautology.from(le_totality, lt_defn of (x := y, y := x))
  }

  // FIXME: is actually a proof by contraposition
  val lt_neg = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, !(x < y)) |- y <= x){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(!(x < y))
    have(!((x <= y) /\ !(y <= x))) by Tautology.from(lt_defn)
    have(!(x <= y) \/ (y <= x)) by Tautology.from(lastStep)
    have((y < x) \/ (y <= x)) by Tautology.from(lastStep, le_neg)
    have((y <= x) \/ (y <= x)) by Tautology.from(lastStep, lt_defn of (x := y, y := x))
    have(thesis) by Tautology.from(lastStep)
  }

  val le_lt_neg_iff = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- !(x < y) <=> (y <= x)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    val l = have(!(x < y) ==> y <= x)  by Tautology.from(lt_neg)
    val r = have(y <= x ==> !(x < y)) by Tautology.from(lt_defn)
    have(thesis) by Tautology.from(l, r)
  }

  val lt_trans = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R, x < y, y < z) |- x < z){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    assume(x < y)
    assume(y < z)
    val xley = have(x <= y) by Tautology.from(lt_defn)
    val ylez = have(y <= z) by Tautology.from(lt_defn of (x := y, y := z))
    val ynlex = have(!(y <= x)) by Tautology.from(lt_defn)
    val znley = have(!(z <= y)) by Tautology.from(lt_defn of (x := y, y := z))
    val xlez = have(x <= z) by Tautology.from(le_trans, xley, ylez)
    val zlex_entails_xeqz  = have(z <= x |- x === z) by Tautology.from(lastStep, le_antisym of (x := x, y := z))
    have(z <= x |- z < y) by Congruence.from(lastStep)
    have(z <= x |- !(y < z)) by Tautology.from(lt_not_sym of (x := z, y := y), lastStep) 
    val contr = have(!(z <= x)) by Tautology.from(lastStep)
    have(thesis) by Tautology.from(contr, xlez, lt_defn of (x := x, y := z))
  }
  

  val le_add_imp = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R) |- (x <= y ==> (x + z) <= (y + z))){
    have(thesis) by byRingDefn.apply
  }
  val le_add = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R, x <= y) |- ((x + z) <= (y + z))){
    have(thesis) by Tautology.from(le_add_imp)
  }

  val lt_mul_left_imp = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x∈ R, y ∈ R, z ∈ R) |- ((0 < x) /\ (y < z)) ==> ((x * y) < (x * z))){
    have(thesis) by byRingDefn.apply
  }
  val lt_mul_left = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R, 0 < x, y < z) |- ((x * y) < (x * z))){
    
    have(thesis) by Tautology.from(lt_mul_left_imp)
  }
  val lt_mul_right = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x∈ R, y ∈ R, z ∈ R, 0 < z, x < y) |- ((x * z) < (y * z))){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    assume(0 < z)
    assume(x < y)
    val p1 = have(z * x < z * y) by Tautology.from(lt_mul_left of (x := z, y := x, z := y))
    val e1 = have(z * x === x * z) by Tautology.from(mul_comm of (x := x, y := z))
    val e2 = have(z * y === y * z) by Tautology.from(mul_comm of (x := y, y := z))
    have(x * z < y * z) by Congruence.from(e1, e2, p1)
    have(thesis) by Tautology.from(lastStep, p1, e1, e2)
  }

  val le_lt_eq = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x∈ R, y ∈ R, x <= y) |- (x < y) \/ (x === y)){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    have(x <= y |- x <= y) by Restate
    have(x <= y |- (x <= y) /\ ((y <= x) \/ !(y <= x))) by Tautology.from(lastStep)
    have(x <= y |- ((x <= y) /\ (y <= x)) \/ ((x <= y) /\ !(y <= x))) by Tautology.from(lastStep)
    have(x <= y |- (x < y) \/ (x === y)) by Tautology.from(lt_defn, le_antisym)
    have(thesis) by Tautology.from(lastStep)
  }
  
  val zxltzy_xlty = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x∈ R, y ∈ R, z ∈ R, 0 < z, z*x < z*y) |- x < y){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    assume(0 < z)
    assume(z * x < z * y)
    val contra = have(!(x < y) |- (y < x) \/ (y === x)) by Tautology.from(lt_neg, le_lt_eq of (x := y, y := x)) 
    val p1 = have(y === x |- z * y === z * x) by Congruence
    val p2 = have(y === x |- !(z * x < z * y)) by Tautology.from(lastStep, trichotomy3 of (x := z*x, y := z*y), mul_closure of (x := z, y := x), mul_closure of (x := z, y := y))
    val p3 = have(!(y === x)) by Tautology.from(lastStep)

    val p4 = have(y < x |- z*y < z*x) by Tautology.from(lt_mul_left of (x := z, y:=y, z := x))
    val p5 = have(y < x |- !(z*x < z*y)) by Tautology.from(lastStep, trichotomy2 of (x := z*x, y := z*y), mul_closure of (x := z, y := x), mul_closure of (x := z, y := y))
    val p6 = have(!(y < x)) by Tautology.from(lastStep)

    have(x < y) by Tautology.from(contra, p3, p6)

  }
  val lt_add = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, z ∈ R, x < y) |- ((x + z) < (y + z))){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    assume(y ∈ R)
    assume(z ∈ R)
    assume(x < y)
    val l = have(x <= y) by Tautology.from(lt_defn)
    val r = have(!(y <= x)) by Tautology.from(lt_defn)
    val con = have((x + z) <= (y + z)) by Tautology.from(le_add, l)
    val con1 = have((y + z) <= (x + z)|- (y + z) === (x + z)) by Tautology.from(con, le_antisym of (x := x + z, y := y + z), add_closure of (x := x, y := z), add_closure of (x := y, y := z))
    val ls = have((y + z) === (x + z) |- ((y + z) + (-z)) === ((x + z) + (-z))) by Congruence
    val asc1 = have(((x + (z + -z))) === ((x + z) + (-z))) by Tautology.from(add_assoc of (x := x, y := z, z := -z), neg_closure of (x := z))
    val asc2 = have(((y + (z + -z))) === ((y + z) + (-z))) by Tautology.from(add_assoc of (x := y, y := z, z := -z), neg_closure of (x := z))
    
    val ls2 = have((y + z) === (x + z) |- ((y + (z + -z)) === ((x + (z + -z))))) by Congruence.from(ls, asc1, asc2) 
    val asc3 = have(y + 0 === y) by Tautology.from(add_id_right of (x := y), add_id_closure)
    val asc4 = have(x + 0 === x) by Tautology.from(add_id_right, add_id_closure)
    val asc5 = have(z + -z === 0) by Tautology.from(neg_closure of (x := z), add_inv of (x := z))
    val con2 = have((y + z) === (x + z) |- (y === x)) by Congruence.from(ls2, asc3, asc4, asc5)
    val contr = have(y === x |- !(x < y)) by Tautology.from(trichotomy3 of (x := y, y := x))
    have((y + z) <= (x + z) |- !(x < y)) by Tautology.from(contr, con2, con1)
    val r2 = have(!((y + z) <= (x + z))) by Tautology.from(lastStep)
    have(thesis) by Tautology.from(r2, con, lt_defn of (x := x + z, y := y + z), add_closure of (x := x, y := z), add_closure of (x := y, y := z))
  }
  
  val x_lt_xp1 = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R) |- x < x + 1){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(x ∈ R)
    val p1 = have(0 < `1`) by Tautology.from(zero_lt_1)
    val p2 = have(0 + x === x) by Tautology.from(add_id)
    val p3 = have(1 + x === x + 1) by Tautology.from(mul_id_closure, add_comm of (x := x, y := 1))
    have(0 + x < 1 + x) by Tautology.from(p1, lt_add of (x := 0, y := 1, z := x), add_id_closure, mul_id_closure)
    have(x < x + 1) by Congruence.from(p2, p3, lastStep)
  }

  val sparse_order = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R) |- (x < y ==> x + 1 <= y)){
    have(thesis) by byRingDefn.apply
  }
  val sparse_order_ext = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), x ∈ R, y ∈ R, x < y) |- (x + 1 <= y)){
    have(thesis) by Tautology.from(sparse_order)
  }

  
  val lem = Theorem(∀(x, !Q) |- !(∃(x, Q))){
    have(thesis) by Tableau
  }

  val sparseness_alt = Theorem((ring(R, <=, <, +, *, -, |, `0`, `1`), c ∈ R) |- !(∃(x, x ∈ R /\ (c < x) /\ (x < (c + 1))))){
    assume(ring(R, <=, <, +, *, -, |, `0`, `1`))
    assume(c ∈ R)
    have(x ∈ R |- ((c < x ==> (c + 1 <= x)))) by Tautology.from(sparse_order of (x := c, y := x))
    have(x ∈ R |- !(!((c < x ==> (c + 1 <= x))))) by Tautology.from(lastStep)
    have(x ∈ R |- !(!((c < x ==> (c + 1 <= x))))) by Tautology.from(lastStep)
    val ls = have(x ∈ R |- !(((c < x) /\ !(c + 1 <= x)))) by Tautology.from(lastStep)
    have(x ∈ R |- !(((c < x) /\ (x < (c + 1))))) by Tautology.from(ls, le_lt_neg_iff of (x := x, y := (c + 1)), mul_id_closure, add_closure of (x := c, y := 1))
    have(!(x ∈ R) \/ !(((c < x) /\ (x < (c + 1))))) by Tautology.from(lastStep)
    have(!(x ∈ R /\ (((c < x) /\ (x < (c + 1)))))) by Tautology.from(lastStep)
    inline def Px : Expr[Prop] = (x ∈ R /\ (((c < x) /\ (x < (c + 1)))))
    have(∀(x, !Px)) by RightForall(lastStep)
    have(thesis) by Tautology.from(lastStep, lem of (x := x, Q := Px))
  }

  
}
