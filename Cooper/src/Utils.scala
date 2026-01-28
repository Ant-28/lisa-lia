
// a file storing utilites on Expr[Ind]s
import scala.collection.immutable.{Set => SSet, SortedSet}
import scala.collection.immutable.{List => LList, :: => Cons}
import lisa.maths.SetTheory.Base.Predef.{x => _, y => _, z => _, P => _, ∈ => _, have => _, | => _, given, _}
import lisa.maths.SetTheory.Functions.Predef.{R => _, _, given}
import lisa.maths.SetTheory.Base.Pair.{pair, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping}
import lisa.automation.Substitution.Apply as Substitution
import Base.{IBinFun, IUnFun, IRel, infixBinaryFunction, infixUnaryFunction}
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import SubProofWithRes.{TacticSubproofWithResult, DebugRightSubstEq}
import scala.quoted.Varargs
import RingStructure.{variable => _, _}


object Utils {

    inline def max(x : BigInt, y: BigInt): BigInt = if x > y then x else y
    extension (s: Sequent)
      def firstElemL: Expr[Prop] = s.left.head
      def firstElemR: Expr[Prop] = s.right.head

    extension (using proof: library.Proof)(p : proof.ProofStep | proof.InstantiatedFact)
      def sLeft = proof.sequentOfFact(p).left
      def sRight = proof.sequentOfFact(p).right
      def sRightHead = proof.sequentOfFact(p).firstElemR

    
  

    def isVariableOrNeg(x: Expr[Ind]): Boolean = {
      x match {
        case `1` => false
        case `0` => false
        case x : Variable[Ind] => true
        case -(x) => isVariableOrNeg(x)
        case _ => false
      }
    }
    /**
      * 
      *
      * @param x an expression tree in a Ring
      * @return
      */
    inline def isVariable(x: Expr[Ind]): Boolean = {
      x match {
        case x : Variable[Ind] => x.id.name.head.isLetter
        case _ => false
      }
    }
    /**
      * 
      *
      * @param x An Expression true. 
      * @return True if of the form -(x), x: Variable[Ind]
      */
    inline def isNegVariable(x: Expr[Ind]): Boolean = {
      x match {
        case -(x) => isVariable(x)
        case _ => false
      }
    }

    inline def isOne(x: Expr[Ind]): Boolean =  x == `1` 
    inline def isNegOne(x: Expr[Ind]): Boolean = x == -(`1`)
    inline def isZero(x: Expr[Ind]): Boolean = x == `0`
    inline def isOneOrNegOne(x: Expr[Ind]): Boolean = isOne(x) || isNegOne(x)

    /**
      * Collects subexpressions to apply typing rules to 
      *
      * @param exp
      * @return
      */
    def collectSubExprs(exp: Expr[Ind]): SSet[Expr[Ind]] = exp match {
        case a + b  => collectSubExprs(a) ++ collectSubExprs(b) + exp
        case -(a) => collectSubExprs(a) + exp
        case a * b  => collectSubExprs(a) ++ collectSubExprs(b) + exp
        case _      => SSet(exp)
    }
    /**
      * Gets all typing variables in the antecedent of a sequent
      *
      * @param x The set of all antecedent expressions
      *  
      */
    def getTypingVarsInAnte(x: SSet[Expr[Prop]]): SSet[Expr[Ind]] = x
      .flatMap((y) =>
        y match {
          case ys ∈ R => SSet(ys)
          case _      => SSet()
        }
      )
      .flatMap(x => collectSubExprs(x))

    def getTypingFromProp(x : Expr[Prop]): Expr[Ind] = x match {
          case ys ∈ R => ys
          case _      => throw Exception("invalid typing!")
        }

    /**
      * Gets all typing propositions in the antecedent of a sequent
      * i.e. any expr of the form x ∈ R
      * @param x
      * @return
      */
    def getTypings(x: SSet[Expr[Prop]]): SSet[Expr[Prop]] = x.filter( xs => 
        xs match {
          case p ∈ R => true
          case _ => false
        }
      )


    def proofStepDepth(using proof: library.Proof)(x : proof.InstantiatedFact | proof.ProofStep) : Int = {
                (x: @unchecked) match {
                  case tx : Library#Proof#InnerProof#ProofStep => {
                    // println("proofstep")
                    // println(x.bot)
                    // println(x.bot.firstElemR)
                    -treeDepth(getTypingFromProp(tx.bot.firstElemR))
                    }
                  case tx : Library#Proof#InnerProof#InstantiatedFact => {
                    // println("instfact")
                    // println(tx.result)
                    // println(tx.result.firstElemR)
                    -treeDepth(getTypingFromProp(tx.result.firstElemR))
                }
      }
    }

    def proofStepSequent(using proof: library.Proof)(x : proof.InstantiatedFact | proof.ProofStep) : Sequent = {
                (x: @unchecked) match {
                  case tx : Library#Proof#InnerProof#ProofStep => tx.bot
                  case tx : Library#Proof#InnerProof#InstantiatedFact => tx.result
                }
    }
    

    // TODO: proof.sequentOfFact
    def proofStepDebugPrint(using proof: library.Proof)(x : proof.InstantiatedFact | proof.ProofStep) : Unit = {
        println(proof.sequentOfFact(x))
        println(x.sRightHead)
        println(treeDepth(getTypingFromProp(x.sRightHead)))
        println(x.getClass())
        println(" ")
        x match {
          case tx : proof.ProofStep => println("proofstep")
          case tx : proof.InstantiatedFact => println("instfact")
      }
    }

    def proofStepDebugCut(using proof: library.Proof)(x : proof.InstantiatedFact | proof.ProofStep) : Unit = {
        println(proof.sequentOfFact(x))
        println(x.sRightHead)
        println(treeDepth(getTypingFromProp(x.sRightHead)))
        println(x.getClass())
        println(" ")
        x match {
          case tx : proof.ProofStep => println("proofstep")
          case tx : proof.InstantiatedFact => println("instfact")
      }
    }
    /**
      * 
      *
      * @param lib Proof Library
      * @param proof Proof
      * @param s: Set of all typings obtained from an antecedent
      * @return Either an instantiated fact or a proof of inclusion
      */
    def typeChecking(using proof: library.Proof)(s: SSet[Expr[Ind]]): SSet[proof.InstantiatedFact | proof.ProofStep] = 

      s.map { 
      sval => 
      
      sval match  
        case `0`    => have(`0` ∈ R) by Tautology.from(add_id_closure)
        case `1`    => have(`1` ∈ R) by Tautology.from(mul_id_closure)
        case -(a)   => neg_closure of (x := a)
        case a + b  => add_closure of (x := a, y := b)
        case a * b  => mul_closure of (x := a, y := b)
        case  x     => have(x ∈ R |- x ∈ R) by Restate
      }

    /**
      * Find the depth of an expression tree. Needed to sort sequents prior to cutting
      *
      * @param exp
      * @return
      */
    def treeDepth(exp: Expr[Ind]): Int = {
      exp match {
        case a + b => scala.math.max(treeDepth(a), treeDepth(b)) + 1
        case a * b => scala.math.max(treeDepth(a), treeDepth(b)) + 1
        case `0` => 1
        case `1` => 1
        case -(a) => treeDepth(a) + 1
        case x : Variable[Ind] => 1
        case _ => throw Exception("I don't know this expression!")
      }
    }

    /**
      * Get name of Variable[Ind]
      *
      * @param exp
      * @return
      */
    def getVarName(exp: Expr[Ind]): String = {
      require(isVariable(exp) || isNegVariable(exp))
      exp match {
        case tx : Variable[Ind] => tx.id.name
        case -(tx) => getVarName(tx)
        case _ => throw Exception("I don't know this expression!")
      }
    }

    given myExprOrdering : Ordering[Expr[Ind]] {
        def compare(x: Expr[Ind], y: Expr[Ind]): Int = {
            // summon[Ordering[String]].compare(x.asInstanceOf[Variable[Ind]].id.name, y.asInstanceOf[Variable[Ind]].id.name)
            summon[Ordering[String]].compare(getVarName(x), getVarName(y))
        }
    }
    def containsQuantifier(exp: Expr[Prop]): Boolean = {
      exp match {
        case exists(tx, p) => true
        case forall(tx, p) => true 
        case _ => false
      }
    }

    
    // class myProofOrdering(using val lib: library.type, val proof: lib.Proof){
    //   object meepo extends 
    //   // given MPO:  with {
    
    //   // }
    // }


    sealed trait Sign
    case object Pos extends Sign
    case object Neg extends Sign

    def is_eq(x: Expr[Prop]): Boolean = {
      x match {
        case (tx `equality` ty) => true
        case _ => false
      }
    }

    def is_neq(x: Expr[Prop]): Boolean = {
      x match {
        case !(tx `equality` ty) => true
        case _ => false
      }
    }

    def is_div(x: Expr[Prop]): Boolean = {
      x match {
        case RingStructure.`|`(x, y) => true
        case _ => false
      }
    }
    def is_indiv(x: Expr[Prop]): Boolean = {
      x match {
        case !(RingStructure.`|`(x, y)) => true
        case _ => false
      }
    }

    def is_le(x: Expr[Prop]): Boolean = {
      x match {
        case RingStructure.<=(x, y) => true
        case _ => false
      }
    }

    def is_lt(x: Expr[Prop]): Boolean = {
      x match {
        case RingStructure.<(x, y) => true
        case _ => false
      }
    }

    def is_nle(x: Expr[Prop]): Boolean = {
      x match {
        case !(RingStructure.<=(x, y)) => true
        case _ => false
      }
    }

    def is_nlt(x: Expr[Prop]): Boolean = {
      x match {
        case !(RingStructure.<(x, y)) => true
        case _ => false
      }
    }

    inline def is_ineq(x : Expr[Prop]) = is_lt(x) || is_le(x) || is_nlt(x) || is_nle(x)
    inline def is_atom(x : Expr[Prop]) = is_ineq(x) || is_eq(x) || is_neq(x) || is_div(x) || is_indiv(x)
    

    def is_incl(x: Expr[Prop]): Boolean = {
      x match {
        case (_ ∈ R) => true
        case _ => false
      }
    }

    def treeHasVariables(xt: Expr[Ind]): Boolean = {
      xt match {
        case `0` => false
        case `1` => false
        case  tx if isVariableOrNeg(tx) => true 
        case tx + ty => treeHasVariables(tx) || treeHasVariables(ty)
        case tx * ty => treeHasVariables(tx) || treeHasVariables(ty)
        case -(tx) => treeHasVariables(tx) 
        case _ => throw Exception("I don't know this expression!")
      }
    }

    def treeVariables(xt: Expr[Ind]): SSet[Expr[Ind]] = {
      xt match {
        case `0` => SSet()
        case `1` => SSet()
        case  tx if isVariable(tx) => SSet(tx)
        case tx + ty => treeVariables(tx) ++ treeVariables(ty)
        case tx * ty => treeVariables(tx) ++ treeVariables(ty)
        case -(tx) => treeVariables(tx) 
        case _ => throw Exception("I don't know this expression!")
      }
    }

    def exprHasVariables(xt : Expr[Prop]): Boolean = {
      xt match {
        case (tx `equality` ty) => treeHasVariables(tx) || treeHasVariables(ty)
        case RingStructure.`|`(tx, ty) => treeHasVariables(tx) || treeHasVariables(ty)
        case RingStructure.<=(tx, ty) => treeHasVariables(tx) || treeHasVariables(ty)
        case RingStructure.<(tx, ty) => treeHasVariables(tx) || treeHasVariables(ty)
        case !(tx `equality` ty) => treeHasVariables(tx) || treeHasVariables(ty)
        case !(RingStructure.`|`(tx, ty)) => treeHasVariables(tx) || treeHasVariables(ty)
        case !(RingStructure.<=(tx, ty)) => treeHasVariables(tx) || treeHasVariables(ty)
        case !(RingStructure.<(tx, ty)) => treeHasVariables(tx) || treeHasVariables(ty)
        case _ => throw Exception("I don't know this expression!")
      }
    }


    def freeVariables(ex : Expr[Prop]): SSet[Expr[Ind]] = {
      ex match {
        case !(RingStructure.<=(tx, ty)) => treeVariables(tx) ++  treeVariables(ty)
        case !(RingStructure.<(tx, ty)) => treeVariables(tx) ++  treeVariables(ty) 
        case !(RingStructure.|(tx, ty)) => treeVariables(tx) ++  treeVariables(ty) 
        case !(tx `equality` ty) => treeVariables(tx) ++  treeVariables(ty)
        case (RingStructure.<=(tx, ty)) => treeVariables(tx) ++  treeVariables(ty)
        case (RingStructure.<(tx, ty)) => treeVariables(tx) ++  treeVariables(ty) 
        case (RingStructure.|(tx, ty)) => treeVariables(tx) ++  treeVariables(ty)
        case (tx `equality` ty) => treeVariables(tx) ++  treeVariables(ty)
        case p1 `and` p2 => freeVariables(p1) ++ freeVariables(p2)
        case p1 `or` p2 => freeVariables(p1) ++ freeVariables(p2)
        case p1 `iff` p2 => freeVariables(p1) ++ freeVariables(p2)
        case p1 `implies` p2 => freeVariables(p1) ++ freeVariables(p2)
        case `neg`(p1) => freeVariables(p1)
        case forall(tx, p1) => freeVariables(p1) - tx
        case exists(tx, p1) => freeVariables(p1) - tx
        case _ => throw Exception("custom logic!")
      }
    }
    // assumes nnf 
    def boundVars(ex : Expr[Prop]): List[Expr[Ind]] = {
      ex match {
        case forall(tx, p1) => List(tx) ++ boundVars(p1)
        case exists(tx, p1) => List(tx) ++ boundVars(p1)
        case _ => List()
      }

    }

    // def collectLBs(exp: Expr[Prop]): SSet = {
    //   case !(RingStructure.<=(tx, ty)) => SSet(tx, ty)
    //   case !(RingStructure.<(tx, ty)) => SSet(tx, ty) 
    //   case !(RingStructure.|(tx, ty)) => SSet(tx, ty) 
    //   case !(tx `equality` ty) => SSet(tx, ty)
    //   case (RingStructure.<=(tx, ty)) => SSet(tx, ty)
    //   case (RingStructure.<(tx, ty)) => SSet(tx, ty) 
    //   case (RingStructure.|(tx, ty)) => SSet(tx, ty)
    //   case (tx `equality` ty) => SSet(tx, ty)
    // }
    

    def nnf(ex: Expr[Prop]): Expr[Prop] = {
      ex match {
        case p if is_atom(p) => p
        case p1 `and` p2 => nnf(p1) /\ nnf(p2)
        case p1 `or` p2 => nnf(p1) \/ nnf(p2)
        case p1 `implies` p2 => nnf(!p1) \/ nnf(p2)
        case p1 `iff` p2 => nnf(p1 ==> p2) /\ nnf(p2 ==> p1)
        case `neg`(p1) => p1 match {
          case p if (is_eq(p) || is_lt(p) || is_le(p) || is_div(p)) => p
          case !(RingStructure.<=(tx, ty)) => tx <= ty
          case !(RingStructure.<(tx, ty)) => tx < ty 
          case !(RingStructure.|(tx, ty)) => tx | ty 
          case !(tx `equality` ty) => tx === ty
          case p1 `and` p2 => nnf(!p1) \/ nnf(!p2)
          case p1 `or` p2 => nnf(!p1) /\ nnf(!p2)
          case p1 `implies` p2 => nnf(p1) /\ nnf(!p2)
          case p1 `iff` p2 => nnf(p1 /\ !p2) \/ nnf(p2 /\ !p1) 
          case forall(tx, p1) => exists(tx, nnf(!p1))
          case exists(tx, p1) => forall(tx, nnf(!p1))
        }
        case forall(tx, p1) => forall(tx, nnf(p1))
        case exists(tx, p1) => exists(tx, nnf(p1))
        case _ => throw Exception("custom logic!")
      }
    }


    def renameAllVars(ex: Expr[Prop]): Expr[Prop] = {
      var counter = 0
      val substList : Map[Expr[Ind], Expr[Ind]] = Map.empty
      def renameHelper(ex: Expr[Prop], sl : Map[Expr[Ind], Expr[Ind]]): Expr[Prop] = {
      inline def ctns(tx : Expr[Ind], ty : Expr[Ind]) = (sl.contains(tx) || sl.contains(ty))
      ex match {
        case !(RingStructure.<=(tx, ty)) if ctns(tx, ty)  =>  !(sl.getOrElse(tx, tx) <= sl.getOrElse(ty, ty) )
        case !(RingStructure.<(tx, ty)) if ctns(tx, ty)  => !(sl.getOrElse(tx, tx) < sl.getOrElse(ty, ty) )
        case !(RingStructure.|(tx, ty)) if ctns(tx, ty)  => !(sl.getOrElse(tx, tx) | sl.getOrElse(ty, ty) )
        case !(tx `equality` ty) if ctns(tx, ty)  => !(sl.getOrElse(tx, tx) === sl.getOrElse(ty, ty))
        case (RingStructure.<=(tx, ty)) if ctns(tx, ty)  => sl.getOrElse(tx, tx) <= sl.getOrElse(ty, ty)
        case (RingStructure.<(tx, ty)) if ctns(tx, ty)  => sl.getOrElse(tx, tx) < sl.getOrElse(ty, ty) 
        case (RingStructure.|(tx, ty)) if ctns(tx, ty)  => sl.getOrElse(tx, tx) | sl.getOrElse(ty, ty) 
        case (tx `equality` ty) if ctns(tx, ty)=> sl.getOrElse(tx, tx) === sl.getOrElse(ty, ty)
        case p1 `and` p2 => renameHelper(p1, sl) /\ renameHelper(p1, sl)
        case p1 `or` p2 => renameHelper(p1, sl) \/ renameHelper(p1, sl)
        case `neg`(p1) => renameHelper(p1, sl)
        case forall(tx, p1) => {
          val newsl = sl + (tx -> variable[Ind](s"x$counter"))
          counter = counter + 1
          forall(tx, renameHelper(p1, newsl))}
        case exists(tx, p1) => {
          val newsl = sl + (tx -> variable[Ind](s"x$counter"))
          counter = counter + 1
          exists(tx, renameHelper(p1, newsl))}
        case _ => throw Exception("custom logic!")
        }
      }
      renameHelper(ex, substList)
    }
    def prenex(ex: Expr[Prop]): Expr[Prop] = {
      variable[Ind]("x")
      ex match {
        // renamed vars
        case p if is_atom(p) => p
        case forall(tx, p1) `and` forall(ty, p2) => forall(tx, forall(ty, prenex(p1 /\ p2)))
        case forall(tx, p1) `or` forall(ty, p2) => forall(tx, forall(ty, prenex(p1 \/ p2)))
        case forall(tx, p1) `and` exists(ty, p2) => forall(tx, exists(ty, prenex(p1 /\ p2)))
        case forall(tx, p1) `or` exists(ty, p2) => forall(tx, exists(ty, prenex(p1 \/ p2)))
        case exists(tx, p1) `and` forall(ty, p2) => exists(tx, forall(ty, prenex(p1 /\ p2)))
        case exists(tx, p1) `or` forall(ty, p2) => exists(tx, forall(ty, prenex(p1 \/ p2)))
        case exists(tx, p1) `and` exists(ty, p2) => exists(tx, exists(ty, prenex(p1 /\ p2)))
        case exists(tx, p1) `or` exists(ty, p2) => exists(tx, exists(ty, prenex(p1 \/ p2)))
        case forall(tx, p1) `or` p2 => forall(tx, prenex(p1 \/ p2))
        case forall(tx, p1) `and` p2 => forall(tx, prenex(p1 /\ p2))
        case exists(tx, p1) `and` p2 => exists(tx, prenex(p1 /\ p2))
        case exists(tx, p1) `or` p2 => exists(tx, prenex(p1 \/ p2))
        case p2 `or` forall(tx, p1) => forall(tx, prenex(p1 \/ p2))
        case p2 `and` forall(tx, p1) => forall(tx, prenex(p1 /\ p2))
        case p2 `and` exists(tx, p1) => exists(tx, prenex(p1 /\ p2))
        case p2 `or` exists(tx, p1) => exists(tx, prenex(p1 \/ p2))
        case forall(tx, p1) => forall(tx, prenex(p1))
        case exists(tx, p1) => exists(tx, prenex(p1))
        case !(p1) => !p1
        case p1 `and` p2 => prenex(p1) /\ prenex(p2) 
        case p1 `or` p2 => prenex(p1) \/ prenex(p2) 
        case _ => throw Exception("idk missed a case")

      }
    }
    // def evalRingCutHelperB(using proof: library.Proof)
    // (equalityToCut: proof.InstantiatedFact, consq: Expr[Prop], equalities: SSet[Expr[Prop]], ls: proof.ProofStep): (SSet[Expr[Prop]], proof.ProofTacticJudgement) = {
    //   if(equalities.contains(equalityToCut.sRightHeadB)) then {
    //     val res = equalities.excl(equalityToCut.sRightHeadB) ++ equalityToCut.sLeftB
    //     val toCut = equalityToCut.sRightHeadB
    //     TacticSubproofWithResult[SSet[Expr[Prop]]]{
    //       have(res |- consq) by Cut.withParameters(toCut)(equalityToCut, ls)
    //     }(res)
    //   } else {
    //     TacticSubproofWithResult[SSet[Expr[Prop]]]{
    //       have(equalities |- consq) by Restate.from(ls)
    //     }(equalities)
    //   }
    // }
    def evalRingCutHelper(using proof: library.Proof)
    (equalityToCut: proof.ProofStep | proof.InstantiatedFact, consq: Expr[Prop], equalities: SSet[Expr[Prop]], ls: proof.ProofStep): (SSet[Expr[Prop]], proof.ProofTacticJudgement) = {
      if(equalities.contains(equalityToCut.sRightHead)) then {
        val res = equalities.excl(equalityToCut.sRightHead) ++ equalityToCut.sLeft
        val toCut = equalityToCut.sRightHead
        TacticSubproofWithResult[SSet[Expr[Prop]]]{
          have(res |- consq) by Cut.withParameters(toCut)(equalityToCut, ls)
        }(res)
      } else {
        TacticSubproofWithResult[SSet[Expr[Prop]]]{
          have(equalities |- consq) by Restate.from(ls)
        }(equalities)
      }
    }


}