class Node<T> {
    var value: T
    var next: Node?<T>

    ghost var list: seq<T>
    ghost var Repr: set<object>

    predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    {
        this in Repr &&
        (next != null ==> next in Repr &&
                          next.Repr <= Repr &&
                          this !in next.Repr &&
                          next.Valid()) &&
        list == Union([value], next)
    }

    function Union(v: seq<T>, n: Node?<T>): seq<T>
        reads n
    {
        if n == null then v
        else v + n.list
    }

    constructor (v: T)
        ensures Valid() && fresh(Repr)
    {
        value := v;
        next := null;
        list := [v];
        Repr := {this};
    }

    method SetNext(n: Node<T>)
        modifies Repr
        requires n !in Repr
        requires Valid()
        requires (n.Repr <= Repr &&
                  this !in n.Repr &&
                  n.Valid()) &&
                  list == Union([value], next)
        ensures Valid()
    {
        next := n;
        Repr := Repr + {n};
        list := list + n.list;
    }

    method GetValue() returns (v: T)
        requires Valid()
        ensures Valid()
    {
        v := value;
    }

    method GetNext() returns (n: Node?<T>)
        requires Valid()
        ensures Valid()
    {
        n := next;
    }
}

class Stack<T> {
    var top: Node?<T>;

    ghost var Repr: set<object>

    predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    {
        this in Repr &&
        (top != null ==> top in Repr &&
                        top.Repr <= Repr &&
                        this !in top.Repr &&
                        top.Valid())
    }

    constructor () 
        // creates an empty stack (REPLACE THIS AND OTHER COMMENTS WITH
        // DAFNY SPECIFICATIONS)
        ensures Valid()
    {
        top := null;
        Repr := {this};
    }

    method IsEmpty() returns (r: bool) 
        // returns true when the stack is empty
        requires Valid()
        ensures Valid()
    {
        r := top == null;
    }

    method Push(v: T) 
        // adds v to the top of the stack
        modifies Repr
        requires Valid()
        ensures Valid()
        ensures fresh(Repr - old(Repr))
    {
        var newNode := new Node(v);
        Repr := Repr + {newNode};
        if top != null {
            newNode.SetNext(top); 
        }
        top := newNode;
    }

    method Pop() returns (v: T)
        // returns the top element provided the stack is non-empty
    /*
        modifies Repr
        requires Valid() && top != null
        ensures Valid()
        ensures Repr == old(Repr) - {top}
    {
        v := top.GetValue();
        top := top.GetNext();
        Repr := Repr - {top};
    }
    */
}
