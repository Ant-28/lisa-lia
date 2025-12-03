 // def simplify(using lib: library.type, proof: lib.Proof)(ex: Expr[Ind]): (RB, proof.ProofTacticJudgement) = {

    //     (ex : @unchecked) match {
    //       case `0` => {
    //         val proofRes = TacticSubproof { 
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           have(`0` ∈ R |- `0` === `0`) by Restate }
    //         val res = RB(`0`)
    //         (res, proofRes)
    //       }
    //       case `1` => {
    //         val proofRes = TacticSubproof { 
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           have(`1` ∈ R |- `1` === `1`) by Restate }
    //         val res = `1`
    //         (res, proofRes)
    //       }
    //       case `0` + xs => {
    //         // simpl(xs)
    //         val prf = TacticSubproof{ 
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           val (result, prf) = simplify(xs)
    //           if !prf.isValid then proof.InvalidProofTactic("simplification failed!") // TODO: check if invalidprooftactic needs .validate or st 
    //           else 
    //             val newstmt = ((`0`∈ R, xs ∈ R, result ∈ R) |- `0` + xs === result) 
    //             val stmt = newstmt ++<< have(prf).bot
    //             // TODO: change to one substitute instead
    //             // use tactic RightSubstEq
    //             // provide a lambda like (\y -> y === result) and substitute with 0 + xs === xs 
    //             have(newstmt) by Congruence.from(zero_x_x of (x := xs), have(prf))
    //         }
    //         (simplify(xs)._1, prf)
    //       }
    //       // case _ => (x, proof.InvalidProofTactic("not implemented"))
    //       case xs + `0` => {
    //         // simpl(xs)
    //         val prf = TacticSubproof{ 
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           val (result, prf) = simplify(xs)
    //           if !prf.isValid then proof.InvalidProofTactic("simplification failed!") 
    //           else 
    //             val newstmt = ((`0`∈ R, xs ∈ R, result ∈ R) |- xs + `0` === result) 
    //             val stmt = newstmt ++<< have(prf).bot
    //             // println(stmt.toString)
    //             // println(have(prf).bot.toString)
    //             // println("x + 0")
    //             // println(stmt.toString)
    //             have(newstmt) by Congruence.from(x_zero_x of (x := xs), have(prf))
    //         }
    //         (simplify(xs)._1, prf)
    //       }
    //       case (xs + ys) + zs => 
    //         val prf = TacticSubproof{
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           val (rxs, prfxs) = simplify(xs)
    //           val (rys, prfys) = simplify(ys)
    //           val (rzs, prfzs) = simplify(zs)
    //           // FIXME: have should be after you ahve checked the proof step
    //           // it consumes the ProofTacticResult, and may throw
    //           val h1 = have(prfxs) // have(xs === rxs) 
    //           val h2 = have(prfys) // have(ys === rys)
    //           val h3 = have(prfzs) // have(zs === rzs)

    //           // val associ = have(((xs + ys) + zs) === (rxs + (rys + rzs)))
    //           val (rsimp, prfsimp) = simplify(rxs + (rys + rzs))
    //           val hsimp = have(prfsimp) // have(rxs + (rys + rzs) === rsimp)
    //           if !(prfxs.isValid && prfys.isValid && prfzs.isValid && prfsimp.isValid) 
    //           then proof.InvalidProofTactic("simplification failed!") 
    //           else
    //             // TODO:
    //             //  can be done in two subst steps
    //             //  |- (x + y) + z = (x + y) + z by Restate
    //             //  |- (x + y) + z = (rx + ry) + rz by RightSubstEq(\ sx sy sz -> (x + y) + z = (sx + sy) + sz, x -> rx, y -> ry, z -> rz)
    //             //  |- (x + y) + z = rx + (ry + rz) by RightSubstEq(\ ss -> (x + y) + z = ss, theWhole -> theWholeAssoc)
    //             //  |- (x + y) + z = rsimp by RightSubstEq(\ ss -> (x + y) + z = ss, theWholeAssoc -> rsimp)
    //             val newstmt = ((xs ∈ R, ys ∈ R, zs ∈ R, rxs ∈ R, rys ∈ R, rzs ∈ R) |- (xs + ys) + zs === rsimp)
    //             val stmt = newstmt ++<< h1.bot ++<< h2.bot ++<< h3.bot  ++<< hsimp.bot // ++<< associ.bot 
    //             // println("x + y + z")
    //             // println(stmt.toString)
    //             have(stmt) by Congruence.from(x_zero_x of (x := xs), h1, h2, h3, hsimp, add_assoc of (x := xs, y := ys, z := zs))
    //         }
    //         (simplify(simplify(xs)._1 + (simplify(ys)._1 + simplify(zs)._1))._1, prf)
    //       case `1` + xs     => {
    //         // simpl(xs)
    //         val prf = TacticSubproof{ 
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           val (result, prf) = simplify(xs)
    //           // println("x, xs, prf")
    //           // println(ex)
    //           // println(xs)
    //           // println(result)
    //           // println(have(prf).toString)
    //           if !prf.isValid then proof.InvalidProofTactic("simplification failed!") 
    //           else 
    //             val newstmt = ((`1`∈ R, xs ∈ R, result ∈ R) |- `1` + xs === `1` + result) 
    //             val stmt = newstmt ++<< have(prf).bot
    //             // println(stmt.toString)
    //             // println("1 + x")
    //             // println(stmt.toString)
    //             // println(have(prf).bot.toString)
    //             have(newstmt) by Congruence.from(have(prf))
    //         }
    //         (`1` + simplify(xs)._1, prf)
    //     }
    //     case `-`(`0`) => {
    //         val proofRes = TacticSubproof { 
    //           assume(ring(R, <=, `+`, *, `-`, `0`, `1`))
    //           have((`0` ∈ R, `-`(`0`) ∈ R) |- `-`(`0`) + `0` === `0` + `-`(`0`) ) by Tautology.from(add_comm of (x := `0`, y := `-`(`0`))) }
    //         val res = `0`
    //         (res, proofRes)
          
    //     }
    //   }
    // }
