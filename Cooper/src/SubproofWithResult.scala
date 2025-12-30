import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import lisa.utils.fol.{FOL => F}
import lisa.utils.K
import lisa.utils.KernelHelpers.{|- => `K|-`, _}


object SubProofWithRes {

class SUBPROOF(using val proof: Library#Proof)(statement: Option[F.Sequent])(val iProof: proof.InnerProof) extends ProofTactic {
    val bot: Option[F.Sequent] = statement
    val botK: Option[K.Sequent] = statement map (_.underlying)
    val scproof: Option[K.SCProof] = if (iProof.length == 0) then None else Some(iProof.toSCProof)

    val premises: Seq[proof.Fact] = iProof.getImports.map(of => of._1)
    def judgement: proof.ProofTacticJudgement = {
      if (iProof.length == 0)
        proof.InvalidProofTactic(s"Subproof is empty.")
      else if (botK.isEmpty)
        proof.ValidProofTactic(iProof.mostRecentStep.bot, scproof.get.steps, premises)
      else if (!K.isSameSequent(botK.get, scproof.get.conclusion))
        proof.InvalidProofTactic(s"The subproof does not prove the desired conclusion.\n\tExpected: ${botK.get.repr}\n\tObtained: ${scproof.get.conclusion.repr}")
      else
        proof.ValidProofTactic(bot.get, scproof.get.steps :+ K.Restate(botK.get, scproof.get.length - 1), premises)
    }
  }

 inline def TacticSubproofWithResult[A](using proof: Library#Proof)(inline computeProof: proof.InnerProof ?=> Unit)(inline result: A): (A, proof.ProofTacticJudgement) =
    val iProof: proof.InnerProof = new proof.InnerProof(None)
    computeProof(using iProof)
    (result, SUBPROOF(using proof)(None)(iProof).judgement.asInstanceOf[proof.ProofTacticJudgement])

  object DebugRightSubstEq extends ProofTactic {
      @deprecated("Use withParameters instead", "0.9")
      def withParametersSimple(using
          lib: Library,
          proof: lib.Proof
      )(
          equals: Seq[(F.Expr[F.Ind], F.Expr[F.Ind])],
          lambdaPhi: (Seq[F.Variable[?]], F.Expr[F.Prop])
      )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
        withParameters(equals, lambdaPhi)(premise)(bot)
      }

      def withParameters(using
          lib: Library,
          proof: lib.Proof
      )(
          equals: Seq[(F.Expr[?], F.Expr[?])],
          lambdaPhi: (Seq[F.Variable[?]], F.Expr[F.Prop])
      )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
        // println(bot.left.map(x => x))
        lazy val premiseSequent = proof.getSequent(premise).underlying
        lazy val botK = bot.underlying
        lazy val equalsK = equals.map(p => (p._1.underlying, p._2.underlying))
        lazy val lambdaPhiK = (lambdaPhi._1.map(_.underlying), lambdaPhi._2.underlying)

        val (s_es, t_es) = equalsK.unzip
        val (phi_args, phi_body) = lambdaPhiK
        if (phi_args.size != s_es.size) // Not strictly necessary, but it's a good sanity check. To reactivate when tactics have been modified.
          proof.InvalidProofTactic("The number of arguments of φ must be the same as the number of equalities.")
        else if (equals.zip(phi_args).exists { case ((s, t), arg) => s.sort != arg.sort || t.sort != arg.sort })
          proof.InvalidProofTactic("The arities of symbols in φ must be the same as the arities of equalities.")
        else {
          val phi_s_for_f = K.substituteVariables(phi_body, (phi_args zip s_es).toMap)
          val phi_t_for_f = K.substituteVariables(phi_body, (phi_args zip t_es).toMap)
          val sEqT_es = equalsK map { case (s, t) =>
            val no = (s.freeVariables ++ t.freeVariables).view.map(_.id.no).maxOption.getOrElse(-1) + 1
            val vars = (no until no + s.sort.depth).map(i => K.Variable(K.Identifier("x", i), K.Ind))
            val inner1 = vars.foldLeft(s)(_(_))
            val inner2 = vars.foldLeft(t)(_(_))
            val base = if (inner1.sort == K.Prop) K.iff(inner1)(inner2) else K.equality(inner1)(inner2)
            vars.foldLeft(base: K.Expression) { case (acc, s_arg) => K.forall(s_arg, acc) }
          }
          println(botK.left.map(x => x.repr))
          println((premiseSequent.left ++ sEqT_es).map(x => x.repr))
          if (K.isSameSet(botK.left, premiseSequent.left ++ sEqT_es))
            
            if (
              K.isSameSet(botK.right + phi_t_for_f, premiseSequent.right + phi_s_for_f) ||
              K.isSameSet(botK.right + phi_s_for_f, premiseSequent.right + phi_t_for_f)
            )
              proof.ValidProofTactic(bot, Seq(K.RightSubstEq(botK, -1, equalsK, lambdaPhiK)), Seq(premise))
            else
              proof.InvalidProofTactic("Right-hand side of the premise and the conclusion should be the same with each containing one of φ(s_) φ(t_), but it isn't the case.")
          else proof.InvalidProofTactic("Left-hand sides of the premise + (s=t)_ must be the same as left-hand side of the premise.")
        }
      }
    }
}

