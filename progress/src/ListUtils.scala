import stainless.lang.*
import stainless.collection.*
import stainless.collection.ListSpecs.*
import stainless.proof.*

object ListUtils {

    


    def dropComm(l: List[BigInt], i: BigInt, j: BigInt) : Unit = {
        require(0 <= i)
        require(0 <= j)
        decreases(i)

        (i, j, l) match {
            case (_, _, Nil())                  => ()
            case (BigInt(0), BigInt(0), el)     => ()
            case (ip, BigInt(0), el)            => ()
            case (BigInt(0), jp, el)            => ()
            case (ip, jp, Cons(x, Nil()))       => (assert(l.drop(i).drop(j) == l.drop(i + j)))
            case (BigInt(1), jp, el)            => (assert(l.drop(i).drop(j) == l.drop(i + j)))
            case (ip,jp, Cons(x, xs))     => {
                assert(l.drop(1) == xs)
                dropComm(l, 1, i - 1)
                assert(l.drop(i) == l.drop(1).drop(i - 1))
                assert(l.drop(1).drop(i-1).drop(j) == xs.drop(i - 1).drop(j))
                dropComm(xs, i - 1, j)
                assert(xs.drop(i - 1).drop(j) == xs.drop(i - 1 + j))
                assert(l.drop(1).drop(i - 1).drop(j) == l.drop(1).drop(i - 1 + j))
                dropComm(l, 1, i - 1 + j)
                assert(l.drop(1).drop(i - 1 + j) == l.drop(i + j) )
                assert(l.drop(i).drop(j) == l.drop(i + j))
            }
        }

    }.ensuring(res => l.drop(i).drop(j) == l.drop(i + j))


    
    def dropCommTail(l: List[BigInt], k : BigInt) : Unit = {
        require(BigInt(0) <= k && k < l.length && BigInt(1) <= l.length)
        decreases(k)
        dropComm(l, k, 1)
        assert(l.drop(k).tail == l.drop(k).drop(1))
    }.ensuring(res => l.drop(k).tail == l.drop(k+1))

    // def nexistsImpliesForall[T](l: List[T], p: T => Boolean): Unit
    
    def applyForallNot0(l: List[BigInt], k : BigInt) : Unit = {
        require(0 <= k && k < l.length)
        require(l.forall(x => x != BigInt(0)))
        assert(applyForAll[BigInt](l, k, x => x != BigInt(0)))
       
    }.ensuring(_ => l(k) != BigInt(0))

    
    def dropForAll[T](l: List[T], i: BigInt, p: T => Boolean): Boolean = {
        require(l.forall(p))
        decreases(l.length)

        (i, l) match {
        case (_,Nil()) => trivial
        case (i, Cons(head, tail)) if i <= 0 => assert(l.drop(i) == l)
        case (i, Cons(head, tail)) if i > 0  => if(i == 0) p(head) else dropForAll(l.tail, i - 1, p)
        }

        l.drop(i).forall(p)
    }.holds

    


    
    def appendForAll[A](l: List[A], elem: A, p: A => Boolean): Unit = {
        require(l.forall(p))
        require(p(elem))
    }.ensuring(_ => Cons(elem, l).forall(p))

    


    //Lemma probably somewhere in list lemmas stainless??
    // was applyThenDrop
    
    def applyThenDrop(l: List[BigInt], i : BigInt) : Unit = {
        require(0 <= i && i < l.length)
        decreases(i)
        if l == Nil() || i == 0 then ()
        else
            applyThenDrop(l.tail, i-1)
    }.ensuring(_ => (l(i) :: l.drop(i+1)) == l.drop(i))

    
    def indexDrop(l: List[BigInt], i: BigInt) : Unit = {
        require(0 <= i && i < l.length)
        decreases(i)
        if l == Nil() || i == 0 then ()
        else
            indexDrop(l.tail, i-1)
    }.ensuring(_ => l.drop(i)(0) == l(i))

    
    def consInj[A](x : A, y1: List[A], y2: List[A], y3: List[A]): Unit = {
        require(y1 == Cons(x, y2))
        require(y2 == y3)
        
    }.ensuring(_ => y1 == Cons(x, y3))
    
    def dropNoContains[T](l: List[T], v: T): Unit = {
        require(!l.contains(v))

        l match
            case Nil() => ()
            case Cons(h, t) => dropNoContains(t, v)
        
    }.ensuring(!l.drop(1).contains(v))
   
  
}

