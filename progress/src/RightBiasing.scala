import stainless.lang.* 
import stainless.collection.*
import stainless.collection.ListSpecs.*
import ListUtils.*

object RightBiasing {
    sealed trait Tree


    case object Zero extends Tree
    case object One extends Tree
    case class Var(s: BigInt) extends Tree
    case class Plus(l: Tree, r: Tree) extends Tree
    case class Neg(l: Tree) extends Tree
    case class Mult(l: Tree, r : Tree) extends Tree


    sealed trait Sign
    case object P extends Sign
    case object M extends Sign


    inline def isVariable(x: Tree) = x match {
                                        case Var(_) => true
                                        case _ => false 
                                    }
    inline def isNegVariable(x: Tree) = x match {
                                        case Neg(Var(_)) => true
                                        case _ => false 
                                    }
    inline def isVarOrNegation(x: Tree) = isVariable(x) || isNegVariable(x)
    inline def isOne(x: Tree) = x == One
    inline def isNegOne(x: Tree) = x == Neg(One)
    inline def isOneOrNegOne(x: Tree) = isOne(x) || isNegOne(x)
    inline def isZero(x: Tree) = x == Zero
    inline def isBaseTerm(x: Tree) = isVarOrNegation(x) || isOneOrNegOne(x) || isZero(x)


    



    case class VarList(data: List[Tree]){
        require(data.forall(x => isVarOrNegation(x) || isOneOrNegOne(x)))
    }

    def rbhelper(x: Tree, list : VarList): Boolean = x match {
            case Mult(_, _) => false
            case Zero => list.data.isEmpty
            case One => !list.data.contains(Neg(One)) && list.data.forall(!isVarOrNegation(_))
            case Neg(One) => !list.data.contains((One)) && list.data.forall(!isVarOrNegation(_))
            case Var(s) => !list.data.contains(Neg(Var(s))) 
            case Neg(Var(s)) => !list.data.contains((Var(s))) 
            case Plus(t1@One, t2) => {
                if list.data.contains(Neg(One)) || list.data.exists(isVarOrNegation(_)) then false else 
                t2 match {
                    case One => true
                    case Var(s) => rbhelper(t2, VarList(list.data.::(t1)))
                    case Neg(Var(s)) => rbhelper(t2, VarList(list.data.::(t1)))
                    case Plus(One, t3) => rbhelper(t2, VarList(list.data.::(t1)))
                    case Plus(Neg(One), t3) => false
                    case Plus(t, t3) if isVarOrNegation(t) => {
                        rbhelper(t2, VarList(list.data.::(t)))
                    }
                    case _ => false
                }
            }
            case Plus(t1@Neg(One), t2) => {
                if list.data.contains(One) || list.data.exists(isVarOrNegation(_))  then false else 
                t2 match {
                    case Neg(One) => true
                    case Var(s) => rbhelper(t2, VarList(list.data.::(t1)))
                    case Neg(Var(s)) =>  rbhelper(t2, VarList(list.data.::(t1)))
                    case Plus(Neg(One), t3) => rbhelper(t2, VarList(list.data.::(t1)))
                    case Plus(One, t3) => false
                    case Plus(t, t3) if isVarOrNegation(t) => {
                        rbhelper(t2, VarList(list.data.::(t)))
                    }
                    case _ => false
                }
            }
            case Plus(t1@Var(s), t2) => {
                if list.data.contains(Neg(Var(s))) then false else
                t2 match {
                    case Var(sp) => if s > sp then false else rbhelper(t2, VarList(list.data.::(t1)))
                    case Neg(Var(sp)) => if s > sp then false else rbhelper(t2, VarList(list.data.::(t1)))
                    case Plus(Neg(One), t3) => false
                    case Plus(One, t3) => false
                    case Plus(t@Var(sp), t3) => {
                        if s > sp then false else
                        rbhelper(t2, VarList(list.data.::(t)))
                    }
                    case Plus(t@Neg(Var(sp)), t3) => {
                        if s > sp then false else
                        rbhelper(t2, VarList(list.data.::(t)))
                    }
                    case _ => false
                }
            }
            case Plus(t1@Neg(Var(s)), t2) => {
                if list.data.contains(Var(s)) then false else
                t2 match {
                    case Var(sp) => if s > sp then false else rbhelper(t2, VarList(list.data.::(t1)))
                    case Neg(Var(sp)) => if s > sp then false else rbhelper(t2, VarList(list.data.::(t1)))
                    case Plus(Neg(One), t3) => false
                    case Plus(One, t3) => false
                    case Plus(t@Var(sp), t3) => {
                        if s > sp then false else
                        rbhelper(t2, VarList(list.data.::(t)))
                    }
                    case Plus(t@Neg(Var(sp)), t3) => {
                        if s > sp then false else
                        rbhelper(t2, VarList(list.data.::(t)))
                    }
                    case _ => false
                }
            }
            case _ => false
        }

    def isRightBiased(x: Tree): Boolean = {
        
        rbhelper(x, VarList(List.empty))
    }



    case class RB(x : Tree){
        require(isRightBiased(x))
    }


    def rb_plus_is_plus(x: Tree): Unit = {
        decreases(treeDepth(x))
        require(x match {
            case t if isBaseTerm(t) => true
            case Plus(_, _) => true
            case _ => false
        })
        require(isRightBiased(x))
        x match
            case t if isBaseTerm(t) => ()
            case Plus(l, r) => {
                assert(isVarOrNegation(l) || isOneOrNegOne(l))
                unfold(isRightBiased(r))
                assert(r match {
                    case t if isBaseTerm(t) => true
                    case Plus(_, _) => true
                    case _ => false
                })
                rb_plus_both_rb(x, VarList(List.empty))
                rb_plus_is_plus(r)
            }

    }.ensuring(x match
        case t if isBaseTerm(t) => true
        case Plus(l, r) => (isVarOrNegation(l) || isOneOrNegOne(l)) && {r match {
            case t if isVarOrNegation(t) || isOneOrNegOne(t) => true
            case Plus(lp, rp) => true
            case _ => false
        }}
    )


    def rb_empty(x: Tree, list: VarList) : Unit = {
        decreases(treeDepth(x) + list.data.size)
        require(rbhelper(x, list))
        
        list.data.match
            case Cons(h, cdr) => {
                x match {
                    case Mult(_, _) => assert(!rbhelper(x, list))
                    case Zero => assert(!rbhelper(x, list))
                    case One =>  {
                        assert(h != Neg(One))
                        assert(!isVarOrNegation(h))
                        // assert(!list.data.exists(isVarOrNegation(_)))
                        // nexistsImpliesForall(list.data, isVarOrNegation)
                        assert(list.data.forall(!isVarOrNegation(_)))
                        assert(cdr == list.data.drop(1))
                        dropForAll(list.data, 1, x => !isVarOrNegation(x))
                        rb_empty(x, VarList(cdr))

                    }
                        
                    case Neg(One) => {
                        assert(h != (One))
                        assert(!isVarOrNegation(h))
                        // assert(!list.data.exists(isVarOrNegation(_)))
                        // nexistsImpliesForall(list.data, isVarOrNegation)
                        assert(list.data.forall(!isVarOrNegation(_)))
                        assert(cdr == list.data.drop(1))
                        dropForAll(list.data, 1, x => !isVarOrNegation(x))
                        rb_empty(x, VarList(cdr))

                    }
                    case Var(s) => {
                            assert(!list.data.contains(Neg(Var(s))))
                            dropNoContains(list.data, Neg(Var(s)))
                            assert(cdr == list.data.drop(1))
                            rb_empty(x, VarList(cdr))
                        }
                        
                    case Neg(Var(s)) => {
                        assert(!list.data.contains((Var(s))))
                        dropNoContains(list.data, (Var(s)))
                        assert(cdr == list.data.drop(1))
                        rb_empty(x, VarList(cdr))
                        } 
                    case Plus(t1@One, t2) => {
                        if list.data.contains(Neg(One)) || list.data.exists(isVarOrNegation(_)) then assert(!rbhelper(x, list)) else 
                        t2 match {
                            case One => {
                                assert(!list.data.contains(Neg(One)))
                                dropNoContains(list.data, Neg(One))
                                assert(cdr == list.data.drop(1))
                                assert(!list.data.exists(isVarOrNegation(_)))
                                unfold(!list.data.exists(isVarOrNegation(_))); nexistsImpliesForall(list.data, isVarOrNegation);
                                assert(list.data.forall(!isVarOrNegation(_)))
                                dropForAll(list.data, 1, x => !isVarOrNegation(x))
                                rb_empty(x, VarList(cdr))
                            }
                            case Var(s) => {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))
                                rb_empty(x, VarList(cdr))
                            }
                            case Neg(Var(s)) => {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))    
                                rb_empty(x, VarList(cdr))
                            }
                            case Plus(One, t3) => {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))   
                                rb_empty(x, VarList(cdr)) 
                            }
                            case Plus(Neg(One), t3) => assert(!rbhelper(x, list))
                            case Plus(t, t3) if isVarOrNegation(t) => {
                                assert(rbhelper(t2, VarList(list.data.::(t))))
                                rb_empty(t, VarList(list.data)) 
                                rb_empty(x, VarList(cdr))   
                            }
                            case _ => assert(!rbhelper(x, list))
                        }
                    }
                    case Plus(t1@Neg(One), t2) => {
                        if list.data.contains(One) || list.data.exists(isVarOrNegation(_))  then assert(!rbhelper(x, list)) else 
                        t2 match {
                            case Neg(One) => {
                                assert(!list.data.contains((One)))
                                dropNoContains(list.data, (One))
                                assert(cdr == list.data.drop(1))
                                assert(!list.data.exists(isVarOrNegation(_)))
                                unfold(!list.data.exists(isVarOrNegation(_))); nexistsImpliesForall(list.data, isVarOrNegation)
                                assert(list.data.forall(!isVarOrNegation(_)))
                                dropForAll(list.data, 1, x => !isVarOrNegation(x))
                                rb_empty(x, VarList(cdr))
                            }
                            case Var(s) => {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))  
                                rb_empty(x, VarList(cdr))  
                            }
                            case Neg(Var(s)) =>  {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))   
                                rb_empty(x, VarList(cdr)) 
                            }
                            case Plus(Neg(One), t3) => {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))  
                                rb_empty(x, VarList(cdr))  
                            }
                            case Plus(One, t3) => assert(!rbhelper(x, list))
                            case Plus(t, t3) if isVarOrNegation(t) => {
                                assert(rbhelper(t2, VarList(list.data.::(t))))
                                rb_empty(t, VarList(list.data))  
                                rb_empty(x, VarList(cdr))  
                            }
                            case _ => assert(!rbhelper(x, list))
                        }
                    }
                    case Plus(t1@Var(s), t2) => {
                        if list.data.contains(Neg(Var(s))) then assert(!rbhelper(x, list)) else
                        t2 match {
                            case Var(sp) => if s > sp then assert(!rbhelper(x, list)) else {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))   
                                rb_empty(x, VarList(cdr)) 
                            }
                            case Neg(Var(sp)) => if s > sp then assert(!rbhelper(x, list)) else {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))   
                                rb_empty(x, VarList(cdr)) 
                            }
                            case Plus(Neg(One), t3) => assert(!rbhelper(x, list))
                            case Plus(One, t3) => assert(!rbhelper(x, list))
                            case Plus(t@Var(sp), t3) => {
                                if s > sp then assert(!rbhelper(x, list)) else
                                {
                                assert(rbhelper(t2, VarList(list.data.::(t))))
                                rb_empty(t2, VarList(list.data))
                                rb_empty(x, VarList(cdr))    
                            }
                            }
                            case Plus(t@Neg(Var(sp)), t3) => {
                                if s > sp then assert(!rbhelper(x, list)) else
                                {
                                assert(rbhelper(t2, VarList(list.data.::(t))))
                                rb_empty(t2, VarList(list.data))   
                                rb_empty(x, VarList(cdr)) 
                            }
                            }
                            case _ => assert(!rbhelper(x, list))
                        }
                    }
                    case Plus(t1@Neg(Var(s)), t2) => {
                        if list.data.contains(Var(s)) then assert(!rbhelper(x, list)) else
                        t2 match {
                            case Var(sp) => if s > sp then assert(!rbhelper(x, list)) else {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))  
                                rb_empty(x, VarList(cdr))  
                            }
                            case Neg(Var(sp)) => if s > sp then assert(!rbhelper(x, list)) else {
                                assert(rbhelper(t2, VarList(list.data.::(t1))))
                                rb_empty(t2, VarList(list.data))    
                                rb_empty(x, VarList(cdr))
                            }
                            case Plus(Neg(One), t3) => assert(!rbhelper(x, list))
                            case Plus(One, t3) => assert(!rbhelper(x, list))
                            case Plus(t@Var(sp), t3) => {
                                if s > sp then assert(!rbhelper(x, list)) else
                               {
                                assert(rbhelper(t2, VarList(list.data.::(t))))
                                rb_empty(t2, VarList(list.data))    
                                rb_empty(x, VarList(cdr))
                            }
                            }
                            case Plus(t@Neg(Var(sp)), t3) => {
                                if s > sp then assert(!rbhelper(x, list)) else
                                {
                                assert(rbhelper(t2, VarList(list.data.::(t))))
                                rb_empty(t2, VarList(list.data))   
                                rb_empty(x, VarList(cdr)) 
                            }
                            }
                            case _ => assert(!rbhelper(x, list))
                        }
                    }
                    case _ => assert(!rbhelper(x, list))
                
                }
            }
            case Nil() => assert(rbhelper(x, list) == rbhelper(x, VarList(list.data.drop(1))))

    }.ensuring(rbhelper(x, VarList(list.data.drop(1))))

    def rb_empty2(x: Tree, list: VarList) : Unit = {
        decreases(treeDepth(x) + list.data.size)
        require(rbhelper(x, list))
        list.data match
            case Cons(h, t) => {
                rb_empty(x, list)
                assert(t == list.data.drop(1))
                assert(rbhelper(x, VarList(list.data.drop(1))))
                rb_empty2(x, VarList(list.data.drop(1)))
            }
            case Nil() => ()
        

    }.ensuring(isRightBiased(x))

    def rb_plus_both_rb_h(x: Tree, list: VarList) : Unit = {
            require(rbhelper(x, list))
            x match
                case Mult(l, r) => assert(!rbhelper(x, list))
                case Zero => ()
                case One => ()
                case Neg(One) => ()
                case t if isVarOrNegation(t) => ()
                case Plus(l, r) if isVarOrNegation(r) || isOneOrNegOne(r) => ()  
                case Plus(t1@One, t2) => {
                    if list.data.contains(Neg(One)) || list.data.exists(isVarOrNegation(_)) then  assert(!rbhelper(x, list)) else 
                    t2 match {
                        case One => assert(!rbhelper(x, list))
                        case Var(s) => {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t1))))

                            rb_empty2(t2, VarList(list.data.::(t1)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Neg(Var(s)) => {
                            assert(rbhelper(t2, VarList(list.data.::(t1))))

                            rb_empty2(t2, VarList(list.data.::(t1)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Plus(One, t3) => {
                            assert(rbhelper(t2, VarList(list.data.::(t1))))

                            rb_empty2(t2, VarList(list.data.::(t1)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Plus(Neg(One), t3) =>  assert(!rbhelper(x, list))
                        case Plus(t, t3) if isVarOrNegation(t) => {
                            assert(rbhelper(t2, VarList(list.data.::(t))))

                            rb_empty2(t2, VarList(list.data.::(t)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case _ =>  assert(!rbhelper(x, list))
                    }
                    assert(isRightBiased(t1))
                    assert(isRightBiased(t2))
                }
                case Plus(t1@Neg(One), t2) => { 
                    
                    if list.data.contains(One) || list.data.exists(isVarOrNegation(_))  then  assert(!rbhelper(x, list)) else 
                    t2 match {
                        case Neg(One) =>  assert(!rbhelper(x, list))
                        case Var(s) => {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t1))))
                            rb_empty2(t2, VarList(list.data.::(t1)))

                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Neg(Var(s)) =>  {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t1))))
                            rb_empty2(t2, VarList(list.data.::(t1)))

                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Plus(Neg(One), t3) => {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t1))))
                            rb_empty2(t2, VarList(list.data.::(t1)))

                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                            
                        }
                        case Plus(One, t3) =>  assert(!rbhelper(x, list))
                        case Plus(t, t3) if isVarOrNegation(t) => {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t))))
                            rb_empty2(t2, VarList(list.data.::(t)))

                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case _ => assert(!rbhelper(x, list))
                    }
                    assert(isRightBiased(t1))
                    assert(isRightBiased(t2))
                }
                case Plus(t1@Var(s), t2) => {
                    if list.data.contains(Neg(Var(s))) then () else
                    t2 match {
                        case Var(sp) => if s > sp then () else {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t1))))
                            rb_empty2(t2, VarList(list.data.::(t1)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Neg(Var(sp)) => if s > sp then () else {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t1))))
                            rb_empty2(t2, VarList(list.data.::(t1)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        case Plus(Neg(One), t3) => ()
                        case Plus(One, t3) => ()
                        case Plus(t@Var(sp), t3) => {
                            if s > sp then () else
                            {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t))))
                            rb_empty2(t2, VarList(list.data.::(t)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        }
                        case Plus(t@Neg(Var(sp)), t3) => {
                            if s > sp then () else
                            {
                            
                            assert(rbhelper(t2, VarList(list.data.::(t))))
                            rb_empty2(t2, VarList(list.data.::(t)))
                            assert(isRightBiased(t1))
                            assert(isRightBiased(t2))
                        }
                        }
                        case _ =>  assert(!rbhelper(x, list))
                    }
                    assert(isRightBiased(t1))
                    assert(isRightBiased(t2))
                }
                case Plus(t1@Neg(Var(s)), t2) => {
                if list.data.contains(Var(s)) then  assert(!rbhelper(x, list)) else
                t2 match {
                    case Var(sp) => if s > sp then  assert(!rbhelper(x, list)) else {
                        assert(rbhelper(t2, VarList(list.data.::(t1))))
                        rb_empty2(t2, VarList(list.data.::(t1)))
                        assert(isRightBiased(t1))
                        assert(isRightBiased(t2))
                    }
                    case Neg(Var(sp)) => if s > sp then  assert(!rbhelper(x, list)) else {
                        assert(rbhelper(t2, VarList(list.data.::(t1))))
                        rb_empty2(t2, VarList(list.data.::(t1)))
                        assert(isRightBiased(t1))
                        assert(isRightBiased(t2))
                    }
                    case Plus(Neg(One), t3) =>  assert(!rbhelper(x, list))
                    case Plus(One, t3) =>  assert(!rbhelper(x, list))
                    case Plus(t@Var(sp), t3) => {
                        if s > sp then () else
                        {
                        assert(rbhelper(t2, VarList(list.data.::(t))))
                        rb_empty2(t2, VarList(list.data.::(t)))
                        assert(isRightBiased(t1))
                        assert(isRightBiased(t2))
                        
                        
                    }
                    }
                    case Plus(t@Neg(Var(sp)), t3) => {
                        if s > sp then () else
                        {
                        assert(rbhelper(t2, VarList(list.data.::(t))))
                        rb_empty2(t2, VarList(list.data.::(t)))
                        assert(isRightBiased(t1))
                        assert(isRightBiased(t2))
                    }
                    }
                    case _ =>  assert(!rbhelper(x, list))
                }
                assert(isRightBiased(t1))
                assert(isRightBiased(t2))
            }
                case Neg(l) =>  assert(!rbhelper(x, list))
            
    }.ensuring(
    x match {
        case Plus(l, r) => isRightBiased(l) && isRightBiased(r)
        case _ => true
    })


    def rb_plus_both_rb(x: Tree, l: VarList): Unit = {
        decreases(treeDepth(x))
        require(x match {
            case Plus(_, _) => true
            case _ => false
        })
        require(isRightBiased(x))
        require(l.data.isEmpty)
        
        
        rb_plus_both_rb_h(x, l)

    }.ensuring(
        x match {
            case Plus(l, r) => isRightBiased(l) && isRightBiased(r)
            case _ => true
        }
    )

    def hasVariables(x: Tree): Boolean = {
        x match
            case Zero => false
            case One => false
            case Var(s) => true 
            case Plus(l, r) => hasVariables(l) || hasVariables(r)
            case Neg(l) => hasVariables(l) 
            case Mult(l, r) => hasVariables(l) || hasVariables(r)
    }
    def isLinear(x: Tree): Boolean = {

        x match
            case Zero => true
            case One => true 
            case t if isVarOrNegation(t) => true
            case Plus(l, r) => isLinear(l) && isLinear(r)
            case Neg(l) => isLinear(l)
            case Mult(l, r) => isLinear(l) && isLinear(r) && !(hasVariables(l) && hasVariables(r))
        
    }
    def rb_implies_linearity(x: RB): Unit = {
        decreases(treeDepth(x.x))
        x.x match
            case Zero => ()
            case One => ()
            case Neg(One) => ()
            case t if isVarOrNegation(t) => ()
            case Plus(l, r) => {
                rb_plus_both_rb(x.x, VarList(List.empty))
                assert(isRightBiased(l)) 
                assert(isRightBiased(r))
                rb_implies_linearity(RB(l))
                rb_implies_linearity(RB(r))
            } 
            case Neg(l) => ()
            case Mult(l, r) => ()
        
    }.ensuring(isLinear(x.x))


    def isLinearMatch(x: Tree): Unit = {
        decreases(treeDepth(x))
        require(isLinear(x))
        x match
            case Zero => ()
            case One => ()
            case Var(s) => ()
            case Plus(l, r) => 
                assert(treeDepth(l) < treeDepth(x))
                assert(treeDepth(r) < treeDepth(x))
                isLinearMatch(l)
                isLinearMatch(r)
            case Neg(l) => 
                assert(treeDepth(l) < treeDepth(x))
                isLinearMatch(l)
            case Mult(l, r) =>
                assert(treeDepth(l) < treeDepth(x))
                assert(treeDepth(r) < treeDepth(x))
                isLinearMatch(l)
                isLinearMatch(r)
        
    }.ensuring(x match
        case Zero => isLinear(x)
        case One => isLinear(x)
        case Var(s) => isLinear(x)
        case Plus(l, r) => isLinear(l) && isLinear(r)
        case Neg(l) => isLinear(l)
        case Mult(l, r) => isLinear(l) && isLinear(r)
    )




    def treeDepth(x : Tree): BigInt = {
        x match
            case Zero => BigInt(1)
            case One => BigInt(1)
            case Var(s) => BigInt(1)
            case Plus(l, r) => if treeDepth(l) + BigInt(1) > treeDepth(r) + BigInt(1) then treeDepth(l) + BigInt(1) else treeDepth(r) + BigInt(1)
            case Neg(l) => treeDepth(l) + BigInt(1)
            case Mult(l, r) => if treeDepth(l) + BigInt(1) > treeDepth(r) + BigInt(1) then treeDepth(l) + BigInt(1) else treeDepth(r) + BigInt(1)
        
        
    }.ensuring(res => res >= BigInt(0))

}
