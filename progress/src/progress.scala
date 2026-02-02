// import PartialFunction._
import stainless.lang.*
import stainless.collection.List
import stainless.collection.Cons

import RightBiasing.*

// def is



def evalRing(x : Tree): RB = {
    decreases(treeDepth(x))
    require(isLinear(x))
    x match
        case x if isBaseTerm(x) => {
            assert(isRightBiased(x))
            RB(x)

        }
        case Plus(l, r) => {
            assert(treeDepth(l) < treeDepth(x))
            assert(treeDepth(r) < treeDepth(x))
            val el = evalRing(l)
            val er = evalRing(r)
            rb_implies_linearity(el)
            rb_implies_linearity(er)
            assert(isLinear(Plus(el.x, er.x)))
            (el.x, er.x) match {
                case (l, r) if (hasVariables(l) && hasVariables(r)) => {
                    assert(!isLinear(x))
                }
                case (l, r) if (!hasVariables(l) && hasVariables(r)) => {
                    assert(!hasVariables(el.x))
                    assert(hasVariables(er.x))
                    assert(hasVariables(Plus(el.x, er.x)))
                }
                case (l, r) if (hasVariables(l) && !hasVariables(r)) => {
                    assert(hasVariables(el.x))
                    assert(!hasVariables(er.x))
                    assert(hasVariables(Plus(el.x, er.x)))
                }
                case (l, r) if (!hasVariables(l) && !hasVariables(r)) => {
                    assert(!hasVariables(el.x))
                    assert(!hasVariables(er.x))
                    assert(!hasVariables(Plus(el.x, er.x)))
                }
            } 


            val res = evalPlus(el, er)
            assert(hasVariables(x) ==> hasVariables(res.x) 
                && !hasVariables(x) ==> !hasVariables(res.x))
            res
        }
        case Neg(l) => {
            assert(treeDepth(l) < treeDepth(x))
            val el = evalRing(l)
            rb_implies_linearity(el)
            assert(isLinear(Neg(el.x)))
            el match
                case l if hasVariables(l.x) => assert(hasVariables(Neg(el.x)))
                case l if !hasVariables(l.x) => assert(!hasVariables(Neg(el.x)))
            
            val res = evalNeg(el)
            assert(hasVariables(x) ==> hasVariables(res.x) 
                && !hasVariables(x) ==> !hasVariables(res.x))
            res
        }
        case Mult(l, r) => {
            assert(treeDepth(l) < treeDepth(x))
            assert(treeDepth(r) < treeDepth(x))
            val el = evalRing(l)
            val er = evalRing(r)
            rb_implies_linearity(el)
            rb_implies_linearity(er)

            (l, r) match {
                case (l, r) if (hasVariables(l) && hasVariables(r)) => {
                    assert(!isLinear(x))
                }
                case (l, r) if (!hasVariables(l) && hasVariables(r)) => {
                    assert(!hasVariables(el.x))
                    assert(hasVariables(er.x))
                    assert(isLinear(Mult(el.x, er.x)))
                    assert(hasVariables(Mult(el.x, er.x)))
                }
                case (l, r) if (hasVariables(l) && !hasVariables(r)) => {
                    assert(hasVariables(el.x))
                    assert(!hasVariables(er.x))
                    assert(isLinear(Mult(el.x, er.x)))
                    assert(hasVariables(Mult(el.x, er.x)))
                }
                case (l, r) if (!hasVariables(l) && !hasVariables(r)) => {
                    assert(!hasVariables(el.x))
                    assert(!hasVariables(er.x))
                    assert(isLinear(Mult(el.x, er.x)))
                    assert(!hasVariables(Mult(el.x, er.x)))
                } 
            }
            val res = evalMult(el, er)
            assert(hasVariables(x) ==> hasVariables(res.x) 
                && !hasVariables(x) ==> !hasVariables(res.x))
            res
        }
}.ensuring(res => hasVariables(x) ==> hasVariables(res.x) 
                && !hasVariables(x) ==> !hasVariables(res.x)  )

def evalPlus(t1 : RB, t2: RB): RB = {
    decreases(treeDepth(t1.x) + treeDepth(t2.x))
    require(isLinear(Plus(t1.x, t2.x)))
    (t1, t2) match
        case (RB(Zero), x) => x
        case (x, RB(Zero)) => x
        
        case (RB(One), x) => evalIncr(x)
        case (x, RB(One)) => evalIncr(x)

        case (RB(Neg(One)), x) => evalDecr(x)
        case (x, RB(Neg(One))) => evalDecr(x)

        case (x@RB(vx), y) if isVarOrNegation(vx) => evalInsert(x, y)    
        case (y, x@RB(vx)) if isVarOrNegation(vx) => evalInsert(x, y)

        case (RB(Plus(x, xs)), RB(Plus(y, ys))) => (x, y) match
            case (One, Neg(One)) => evalPlus(RB(xs), RB(ys))
            case (Neg(One), One) => evalPlus(RB(xs), RB(ys))
            case (x, y) if isOneOrNegOne(x) => evalPlus (RB(xs) ,(RB(Plus (x, (Plus(y, ys))))))
            case (x, y) if isVarOrNegation(x) => evalPlus (RB(xs) , evalInsert(RB(x), RB(Plus(y, ys))))
            
        
    
}.ensuring(res => hasVariables(Plus(t1.x, t2.x)) ==> hasVariables(res.x) 
                && !hasVariables(Plus(t1.x, t2.x)) ==> !hasVariables(res.x)  )
def evalIncr(x : RB): RB =  {
    require(isLinear(x.x)) 
    require(!isZero(x.x))
    x match
        case RB(Neg(One)) => RB(Zero)
        case RB(Plus(Neg(One), xs)) => RB(xs)
        case RB(xs) => RB (Plus(One, xs))
}.ensuring(res => hasVariables(x.x) ==> hasVariables(res.x) 
                && !hasVariables(x.x) ==> !hasVariables(res.x)  )

def evalDecr(x : RB): RB = {
    require(isLinear(x.x))
    require(!isZero(x.x))
    x match
    case RB(One) => RB(Zero)
    case RB(Plus(One, xs)) => RB(xs)
    case RB(xs) => RB (Plus(Neg(One), xs))
    }

def plus_rb_xs(xs: Tree): Unit = {
    decreases(treeDepth(xs))
    require(xs match {
        case Plus(l, r) => true
        case _ => false
    })
    require(isRightBiased(xs))
    xs match
        case Plus(One, xs) if isVarOrNegation(xs) || isOne(xs) => {
            assert(isRightBiased(xs))
        }
        case Plus(Neg(One), xs) if isVarOrNegation(xs) || isNegOne(xs) => {
            assert(isRightBiased(xs))
        }
        case Plus(x, xs) if isVarOrNegation(xs) || isOne(xs) || isNegOne(xs) => {
            assert(isVarOrNegation(x))
            assert(isRightBiased(xs))
        }
        case Plus(l, r) => {
            assert(isVarOrNegation(l) || isOneOrNegOne(l))
            plus_rb_xs(r)
        }
        case _ => ()
    

}.ensuring(xs match
    case Plus(l, r) => isRightBiased(l) && isRightBiased(r)
    case _ => true
)

def evalInsert(t1 : RB, t2: RB): RB = {
    decreases(treeDepth(t2.x))
    require(isVarOrNegation(t1.x))
    require(isLinear(Plus(t1.x, t2.x)))
    (t1, t2) match {
        case (RB(xs), RB(Zero)) if isVarOrNegation(xs) => RB(xs)
        case (RB(xs), RB(ys)) if isOneOrNegOne(ys) => RB(Plus(ys, xs)) 
        case (RB(xs@Var(xsx)), RB(ys@Var(ysy))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx <= ysy => RB(Plus(xs, ys))
                case (xsx, ysy) if xsx > ysy => RB(Plus(ys, xs)) 
            }
        }
        case (RB(xs@Neg(Var(xsx))), RB(ys@Neg(Var(ysy)))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx <= ysy => RB(Plus(xs, ys))
                case (xsx, ysy) if xsx > ysy => RB(Plus(ys, xs)) 
            }
        }
        case (RB(xs@(Var(xsx))), RB(ys@Neg(Var(ysy)))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx == ysy => RB(Zero)
                case (xsx, ysy) if xsx < ysy => RB(Plus(xs, ys))
                case (xsx, ysy) if xsx > ysy => RB(Plus(ys, xs)) 
            }
        }
        case (RB(xs@Neg(Var(xsx))), RB(ys@(Var(ysy)))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx == ysy => RB(Zero)
                case (xsx, ysy) if xsx < ysy => RB(Plus(xs, ys))
                case (xsx, ysy) if xsx > ysy => RB(Plus(ys, xs)) 
            }
        }
        case (RB(xs), RB(Plus(y, ys))) if isOneOrNegOne(y) => {
            evalPlus(RB(y), evalInsert(RB(xs), RB(ys)))

            evalInsert(RB(xs), RB(ys)) match {
                case RB(Zero) => RB(y)
                case RB(t) if isVarOrNegation(t) => RB(Plus(y, t))
                case RB(Plus(t1, t2)) => RB(Plus(y, Plus(t1, t2)))
            }
        } 
        case (RB(xs@Var(xsx)), RB(Plus(ys@Var(ysy), yss))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx <= ysy => RB(Plus(xs, Plus(ys, yss)))
                case (xsx, ysy) if xsx > ysy => evalInsert(RB(xs), RB(yss)) match {
                    case RB(Zero) => RB(ys)
                    case RB(t) if isVarOrNegation(t) => RB(Plus(ys, t))
                    case RB(Plus(t1, t2)) => RB(Plus(ys, Plus(t1, t2)))
                }
            }
        }
        case (RB(xs@Neg(Var(xsx))), RB(Plus(ys@Neg(Var(ysy)), yss))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx <= ysy => RB(Plus(xs, Plus(ys, yss)))
                case (xsx, ysy) if xsx > ysy =>  evalInsert(RB(xs), RB(yss)) match {
                    case RB(Zero) => RB(ys)
                    case RB(t) if isVarOrNegation(t) => RB(Plus(ys, t))
                    case RB(Plus(t1, t2)) => RB(Plus(ys, Plus(t1, t2)))
                }
            }
        }
        case (RB(xs@Neg(Var(xsx))), RB(Plus(ys@Var(ysy), yss))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx == ysy => RB(yss)
                case (xsx, ysy) if xsx < ysy => RB(Plus(xs, Plus(ys, yss)))
                case (xsx, ysy) if xsx > ysy =>  evalInsert(RB(xs), RB(yss)) match {
                    case RB(Zero) => RB(ys)
                    case RB(t) if isVarOrNegation(t) => RB(Plus(ys, t))
                    case RB(Plus(t1, t2)) => RB(Plus(ys, Plus(t1, t2)))
                }
            }
        }
        case (RB(xs@Var(xsx)), RB(Plus(ys@Neg(Var(ysy)), yss))) => {
            (xsx, ysy) match {
                case (xsx, ysy) if xsx == ysy => RB(yss)
                case (xsx, ysy) if xsx < ysy => RB(Plus(xs, Plus(ys, yss)))
                case (xsx, ysy) if xsx > ysy => evalInsert(RB(xs), RB(yss)) match {
                    case RB(Zero) => RB(ys)
                    case RB(t) if isVarOrNegation(t) => RB(Plus(ys, t))
                    case RB(Plus(t1, t2)) => RB(Plus(ys, Plus(t1, t2)))
                }
            }
        }
        

    }

}
def evalNeg(x: RB): RB = {
    decreases(treeDepth(x.x))
    require(isLinear(Neg(x.x)))
    def evalNegHelper(s: Sign, xs : RB): RB = {
        decreases(treeDepth(xs.x))
        require(xs match {
            case RB(One) => s == P
            case RB(Neg(One)) => s == M
            case RB(Plus(One, xs)) => s == P
            case RB(Plus(Neg(One), xs)) => s == M
            case RB(t) if isVarOrNegation(t) => true
            case RB(Plus(x, xs)) if isVarOrNegation(x) => true
            case _ => false
        })
        require(x != RB(Zero))
        (s, xs) match
            case (_, RB(Var(s))) => RB(Neg(Var(s)))
            case (_, RB(Neg(Var(s)))) => RB(Var(s))
            case (_, RB(Plus(Var(s), xss))) => RB(Plus(Neg(Var(s)), evalNegHelper(P, RB(xss)).x))
            case (_, RB(Plus(Neg(Var(s)), xss))) => RB(Plus(Var(s), evalNegHelper(P, RB(xss)).x))
            case (P, RB(One)) => RB(Neg(One))
            case (P, RB(Plus(One, xss))) => RB(Plus(Neg(One), evalNegHelper(P, RB(xss)).x)) 
            case (M, RB(Neg(One))) => RB(One)
            case (M, RB(Plus(Neg(One), xss))) => RB(Plus((One), evalNegHelper(M, RB(xss)).x)) 
    }       
    x match
        case RB(Zero) => x
        case RB(One) => RB(Neg(One))
        case RB(Neg(One)) => RB(One)
        case RB(Var(s)) => RB(Neg(Var(s)))
        case RB(Neg(Var(s))) => RB(Var(s))
        case v@RB(Plus(One, b)) => evalNegHelper(P, v)
        case v@RB(Plus(Neg(One), b)) => evalNegHelper(M, v)
        case v@RB(Plus(t, b)) if isVarOrNegation(t) => evalNegHelper(P, v)     
    
}.ensuring(res => hasVariables(Neg(x.x)) ==> hasVariables(res.x) 
                && !hasVariables(Neg(x.x)) ==> !hasVariables(res.x)  )

def evalMult(t1 : RB, t2: RB): RB = {
    decreases(treeDepth(t1.x) + treeDepth(t2.x))
    require(isLinear(Mult(t1.x, t2.x)))
    (t1, t2) match {
        case (RB(Zero), x) => RB(Zero)
        case (x, RB(Zero)) => RB(Zero) 
        case (RB(One), x) => x
        case (x, RB(One)) => x
        case (RB(Neg(One)), x) => evalNeg(x)
        case (x, RB(Neg(One))) => evalNeg(x)
        case (t, RB(Plus(a, b))) if isVarOrNegation(t.x) => evalPlus(evalMult(RB(a), t), evalMult(RB(b), t))
        case (RB(Plus(a, b)), t) =>  evalPlus(evalMult(RB(a), t), evalMult(RB(b), t))
    }
}.ensuring(res => hasVariables(Mult(t1.x, t2.x)) ==> hasVariables(res.x) 
                && !hasVariables(Mult(t1.x, t2.x)) ==> !hasVariables(res.x)  )
