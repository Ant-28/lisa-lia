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
import Utils.*

object liaByWitness extends lisa.Main {
  import RingElemConversions.*
    object liaByWitnessProof extends ProofTactic {
    def apply(using proof: library.Proof)(goal: Sequent)(witnesses: List[Expr[Ind]])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {
      if (goal.right.size != 1) then
        proof.InvalidProofTactic("I can't prove more than one sequent!")
      else
        val goalElem = goal.right.head 
        TacticSubproof{
          goal.left.map(xs => assume(xs))
          println(freeVariables(goalElem))
          if (!freeVariables(goalElem).isEmpty) then return proof.InvalidProofTactic("I cannot have free variables!")
          else
            val sol = simplifyLia(goalElem)(witnesses)
            // println(have(sol).bot)
            if !sol.isValid then return proof.InvalidProofTactic("Checking divisibility failed!")
            have(sol)
        }
    }
    }

    def simplifyLia(using proof: library.Proof)(goal: Expr[Prop])(witnesses: List[Expr[Ind]])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement = {

        TacticSubproof{ 
            // TODO: prenex + renames
            val rengoal = nnf(goal)
            val finalGoal = have(goal <=> rengoal) by Tableau
            val bvars = boundVars(goal)
            if SSet(bvars.toSeq*).size != bvars.size then return proof.InvalidProofTactic("duplicated bvar!")

            def makeNewGoal(go : Expr[Prop], l: List[Expr[Ind]]): Expr[Prop] = {
              go match {
                case p if is_atom(p) => subst(p, l)
                case p1 `and` p2 => makeNewGoal(p1, l) /\ makeNewGoal(p2, l)
                case p1 `or` p2 => makeNewGoal(p1, l) \/  makeNewGoal(p2, l)
                case exists(_, p1) => makeNewGoal(p1, l)
              }
            }
            def subst(p : Expr[Prop], l: List[Expr[Ind]]): Expr[Prop] = {
              require(is_atom(p))
              def substHelper(t1: Expr[Ind], t2: Expr[Ind]): (Expr[Ind], Expr[Ind]) = {
                def sr(tp: Expr[Ind]): Expr[Ind] = tp  match {
                  case tpp if isVariable(tpp) => if l.contains(tpp) then witnesses(l.indexOf(tpp)) else tpp
                  case -(tpp) if isNegVariable(tp) => -(if l.contains(tpp) then witnesses(l.indexOf(tpp)) else tpp)
                  case t1p + t2p => sr(t1p) + sr(t2p) 
                  case -(t1p) => -(sr(t1p))
                  case t1p * t2p => sr(t1p)*sr(t2p)
                  case t => t
                }
                val left = sr(t1)
                val right = sr(t2)
                return (left, right)
              }
              p match {
                case !(RingStructure.<=(tx, ty)) => {
                  val t = substHelper(tx, ty)
                  !(t._1 <= t._2)
                }
                case !(RingStructure.<(tx, ty)) => {
                  val t = substHelper(tx, ty)
                  !(t._1 < t._2)
                } 
                case !(RingStructure.|(tx, ty)) => {
                  val t = substHelper(tx, ty)
                  !(t._1 | t._2)
                } 
                case !(tx `equality` ty) => {
                  val t = substHelper(tx, ty)
                  !(t._1 === t._2)
                }
                case (RingStructure.<=(tx, ty)) => {
                  val t = substHelper(tx, ty)
                  (t._1 <= t._2)
                }
                case (RingStructure.<(tx, ty)) => {
                  val t = substHelper(tx, ty)
                  (t._1 < t._2)
                } 
                case (RingStructure.|(tx, ty)) => {
                  val t = substHelper(tx, ty)
                  (t._1 | t._2)
                }
                case (tx `equality` ty) => {
                  val t = substHelper(tx, ty)
                  (t._1 === t._2)
                }
              }
            }
            // println(makeNewGoal(rengoal, bvars))
            val simprf = simplRecurse(makeNewGoal(rengoal, bvars))
            if !simprf.isValid then return proof.InvalidProofTactic(s"simplRecurse Failed! ${simprf.toString()}")
            val p = have(simprf)
            
            val leftList = bvars.zipWithIndex.map((i, j) => (bvars.dropRight(j + 1)))
            val rightList = bvars.zipWithIndex.map((i, j) => (bvars.drop(j))).reverse
            leftList.zip(rightList).map((l, r) => {

              val res = r.foldRight(makeNewGoal(rengoal, l))((l1: Expr[Ind], r1 : Expr[Prop]) => ∃(l1.asInstanceOf[lisa.utils.fol.FOL.Variable[lisa.utils.fol.FOL.Ind]], r1))
              thenHave(res) by RightExists

            })
            // bvars.zipWithIndex.foldRight(p)((i, j) => 
            //   println(j.bot)
            //   println(i)
            //   // println(j)
            //   println("bvars, bvars dropright")
            //   println(bvars)
            //   println(bvars.dropRight((bvars.length) - (i._2)))
            //   println(makeNewGoal(rengoal, bvars.dropRight((bvars.length) - (i._2 + 1))))

            //   val res = bvars.dropRight((bvars.length) - (i._2)).foldRight(makeNewGoal(rengoal, bvars.dropRight((bvars.length) - (i._2 + 1))))((l: Expr[Ind], r : Expr[Prop]) => ∃(l.asInstanceOf[lisa.utils.fol.FOL.Variable[lisa.utils.fol.FOL.Ind]], r))
            //   println("lastStep")
            //   println(lastStep.bot)
            //   println(res)
            //   // println(∃(bvars.reverse(j).asInstanceOf[lisa.utils.fol.FOL.Variable[lisa.utils.fol.FOL.Ind]], ))
              
            //   val p2 = thenHave(res) by RightExists
            //   println(p2.bot)
            //   p2
            // )
            have(goal) by Tautology.from(lastStep, finalGoal)
                
        }
  }

  def simplRecurse(using proof: library.Proof)(g: Expr[Prop])(using myOrd: Ordering[Expr[Ind]]): proof.ProofTacticJudgement  = {
        TacticSubproof{
            g match {
                case g if is_ineq(g) => {
                  val res = inEquality.apply(g)
                  if !res.isValid then return proof.InvalidProofTactic("ineq failed!") else have(res)
                }
                case g if is_eq(g) => {
                  val res = evalRingEq.apply(g)
                  if !res.isValid then return proof.InvalidProofTactic("evalRingEq failed!") else have(res)
                }
                case g if is_neq(g) => {
                  val res = disEquality.apply(g)
                  if !res.isValid then return proof.InvalidProofTactic("disEquality failed!") else have(res)
                }                 
                case g if is_div(g) => {
                  val res = divInts.apply(g)
                  if !res.isValid then return proof.InvalidProofTactic("divInts failed!") else have(res)

                }
                case g if is_indiv(g) => {
                  val res = inDivInts.apply(g)
                  if !res.isValid then return proof.InvalidProofTactic("divInts failed!") else have(res)
                }
                case p1 /\ p2 => {
                  val prf1 = simplRecurse(p1)
                  if !prf1.isValid then return proof.InvalidProofTactic("LHS of conjunct not valid!")
                  val prf2 = simplRecurse(p2)
                  if !prf2.isValid then return proof.InvalidProofTactic("RHS of conjunct not valid!")
                  have(p1 /\ p2) by Tautology.from(have(prf1), have(prf2))
                }
                case p1 \/ p2 => {
                  println(p1)
                  val prf1 = simplRecurse(p1)
                  println(p2)
                  val prf2 = simplRecurse(p2)
                  if !prf1.isValid && !prf2.isValid then return proof.InvalidProofTactic("disjunct not valid!")
                  if prf1.isValid then 
                    have(prf1)
                    have(p1 \/ p2) by Tautology.from(lastStep)
                  else if !prf1.isValid then 
                    have(prf2)
                    have(p1 \/ p2) by Tautology.from(lastStep)
                  
                }

        }
      }
  }
}
