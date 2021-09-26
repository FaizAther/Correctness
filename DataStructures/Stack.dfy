class Node<T> {
    ghost var S: seq<T>;
    ghost var Repr: set<object>;

    var value: T
    var next: Node?<T>

    predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
        decreases Repr
    {
        this in Repr &&
        (next != null ==>
            next in Repr && next.Repr <= Repr &&
            this !in next.Repr &&
            next.Valid() &&
            S == [value] + next.S &&
            S[0] == this.value &&
            next.S == S[1..] &&
            Repr == {this} + next.Repr) &&
        (next == null ==> Repr == {this} && S == [value])
    }

    constructor (v: T)
        ensures Valid() && fresh(Repr)
        ensures this.value == v
        ensures this.next == null
        ensures S == [v]
    {
        value := v;
        next := null;
        Repr := {this};
        S := [v];
    }

    method SetNext(n: Node<T>)
        modifies Repr
        requires this !in n.Repr
        requires Valid() && n.Valid()
        ensures Valid()
        ensures value == old(value)
        ensures fresh(Repr - old(Repr) - n.Repr)
        ensures this.next == n
    {
        next := n;
        Repr := {this} + n.Repr;
        S := [this.value] + n.S;
    }

    method GetValue() returns (v: T)
        requires Valid()
        ensures Valid()
        ensures Repr == old(Repr)
        ensures this == old(this)
        ensures S[0] == v
    {
        v := value;
    }

    method GetNext() returns (n: Node?<T>)
        requires Valid()
        ensures Valid()
        ensures Repr == old(Repr)
        ensures this == old(this)
        ensures n == this.next
    {
        n := next;
    }
}

class Stack<T> {
    ghost var S: seq<T>;
    ghost var Repr: set<object>;

    var top: Node?<T>;

    predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    {
        this in Repr &&
        ((|S| == 0) ==> top == null) &&
        ((|S| != 0) ==> top != null &&
            top in Repr && top.Repr <= Repr &&
            this !in top.Repr &&
            top.Valid() &&
            top.S == S && S[0] == top.value)
    }


    constructor () 
        ensures Valid()
        ensures fresh(Repr)
        ensures S == []
    {
        top := null;
        S := [];
        Repr := {this};
    }

    method IsEmpty() returns (r: bool)
        requires Valid()
        ensures Valid()
        ensures (|S| == 0) <==> r
    {
        r := top == null;
    }

    method Push(v: T) 
        modifies Repr
        requires Valid()
        ensures Valid()
        ensures fresh(Repr - old(Repr))
        ensures S == [v] + old(S)
    {
        var newNode := new Node(v);
        if top != null {
            newNode.SetNext(top);
        }
        top := newNode;
        Repr := Repr + {top};
        S := [v] + S;
    }

    method Pop() returns (v: T)
        modifies Repr
        requires |S| != 0
        requires Valid()
        ensures Valid()
        ensures old(S)[0] == v
        ensures S == old(S)[1..]
        ensures Repr <= old(Repr) &&
                old(top) !in Repr &&
                fresh(Repr - old(Repr))
    {
        Repr := Repr - {top};
        S := S[1..];
        v := top.GetValue();
        top := top.GetNext();
    }
}

method Check()
{
    var s: Stack<nat> := new Stack<nat>();
    s.Push(1);
    var n := 0;
    n := s.Pop();
    assert n == 1 && |s.S| == 0;
    //n := s.Pop(); //error
    s.Push(1);
    assert |s.S| == 1;
    s.Push(2);
    assert |s.S| == 2;
    n := s.Pop();
    assert n == 2 && |s.S| == 1;
    s.Push(3);
    assert |s.S| == 2;
    n := s.Pop();
    assert |s.S| == 1 && n == 3;
}