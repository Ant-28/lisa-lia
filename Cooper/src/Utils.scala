
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
import RingStructure.*


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
      s.map: 
        case a + b  => add_closure of (x := a, y := b)
        case -(a)   => neg_closure of (a)
        case a * b  => mul_closure of (x := a, y := b)
        case `0`    => have(`0` ∈ R) by Tautology.from(add_id_closure)
        case `1`    => have(`1` ∈ R) by Tautology.from(mul_id_closure)
        case  x     => have(x ∈ R |- x ∈ R) by Restate

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
      }
    }

    given myExprOrdering : Ordering[Expr[Ind]] {
        def compare(x: Expr[Ind], y: Expr[Ind]): Int = {
            // summon[Ordering[String]].compare(x.asInstanceOf[Variable[Ind]].id.name, y.asInstanceOf[Variable[Ind]].id.name)
            summon[Ordering[String]].compare(getVarName(x), getVarName(y))
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
      case (_ `equality` _) => true
      case _ => false
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