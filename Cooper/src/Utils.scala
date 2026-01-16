
// a file storing utilites on Expr[Ind]s
import scala.collection.immutable.{Set => SSet, SortedSet}
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


object Utils {

    inline def max(x : BigInt, y: BigInt): BigInt = if x > y then x else y
    import RingStructure.{+, -, `*`, add_closure, neg_closure, mul_closure, `0`, `1`, add_id_closure, mul_id_closure}

    extension (s: Sequent)
      def firstElemL: Expr[Prop] = s.left.head
      def firstElemR: Expr[Prop] = s.right.head

    extension (using lib: library.type, proof: lib.Proof)(p : proof.ProofStep)
      def sLeft = p.bot.left
      def sRight = p.bot.right
      def sRightHead = p.bot.firstElemR


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

    /**
      * 
      *
      * @param lib Proof Library
      * @param proof Proof
      * @param s: Set of all typings obtained from an antecedent
      * @return Either an instantiated fact or a proof of inclusion
      */
    def typeChecking(using lib: library.type, proof: lib.Proof)(s: SSet[Expr[Ind]]): SSet[proof.InstantiatedFact | proof.ProofStep] = 
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
    def treeDepth(exp: Expr[Ind]): BigInt = {
      exp match {
        case a + b => max(treeDepth(a) + 1, treeDepth(b) + 1)
        case `0` => 1
        case `1` => 1
        case -(a) => treeDepth(a) + 1
        case x => 1
      }
    }

    


    sealed trait Sign
    case object P extends Sign
    case object M extends Sign

    def is_eq(x: Expr[Prop]): Boolean = {
    x match {
      case (_ `equality` _) => true
      case _ => false
    }
    }

    def evalRingCutHelper(using lib: library.type, proof: lib.Proof)
    (equalityToCut: proof.ProofStep, consq: Expr[Prop], equalities: SSet[Expr[Prop]]): (SSet[Expr[Prop]], proof.ProofTacticJudgement) = {
      val res = equalities.excl(equalityToCut.sRightHead) ++ equalityToCut.sLeft
      val toCut = equalityToCut.sRightHead
      TacticSubproofWithResult[SSet[Expr[Prop]]]{
        have(res |- consq) by Cut.withParameters(toCut)(equalityToCut, lastStep)
      }(res)
    }


}