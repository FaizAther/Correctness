
datatype Value = Pair(n: nat, d: nat, pos: int)

datatype Tree = Null | Node(Tree, Value, Tree)

function method GenerateRoot(): Tree
{
  Node(Null, Pair(1,1,1), Null)
}

function method GenerateLeft(p: Value): Tree
{
  match p
  case Pair(n, d,pos) => Node(Null, Pair(n,n+d,2*pos), Null)
}

function method GenerateRight(p: Value): Tree
{
  match p
  case Pair(n, d,pos) => Node(Null, Pair(n+d,d, (2*pos)+1), Null)
}

function method GenerateNode(l: Tree, p: Value, r: Tree): Tree
{
  Node(l,p,r)
}

function method GenerateLevel(t: Tree): Tree
{
  match t
  case Null => Null
  case Node(Null, v, Null) => GenerateNode(GenerateLeft(v), v, GenerateRight(v))
  case Node(l,v,r) => Node(GenerateLevel(l), v, GenerateLevel(r))
}

method ShowPair(p: Value)
{
  match p {
    case Pair(n,d,pos) =>
      print("([");
      print(pos);
      print("]");
      print(n);
      print("/");
      print(d);
      print(")");
  }
}

method Show(t: Tree)
{
  match t {
    case Null =>
      print(" X ");
    case Node(l,p,r) =>
      print("(");
      Show(l);
      ShowPair(p);
      Show(r);
      print(")");
  }
}

function method CalkinWilf(N: nat, t: Tree): Tree
{
  if (N == 0) then t
  else CalkinWilf(N-1,GenerateLevel(t))
}


function method Power(a: nat, x: nat) : nat
  decreases x
{
  if x == 0 then 1 else a * Power(a, x-1)
}

function method Log2(b:nat, x: nat): nat
  requires Power(2,x) > 0
  decreases b / Power(2,x)
{
  if ((b / Power(2,x)) == 0) then x
  else Log2(b,x+1)
}

function method GetNth(t: Tree, N: nat): Value
{
  match t
  case Null
    => Pair(0,0,-1)
  case Node(Null,Pair(n,d,pos), Null) =>
    if pos == N
    then Pair(n,d,pos)
    else Pair(0,0,-1)
  case Node(l,Pair(n,d,pos),r) =>
    if pos == N
    then Pair(n,d,pos)
    else
      match GetNth(l,N)
      case Pair(n,d,pos) =>
        if pos == N
        then Pair(n,d,pos)
        else
          match GetNth(r, N)
          case Pair(n,d,pos) =>
            if pos == N
            then Pair(n,d,pos)
            else Pair(0,0,-1)
}



function method fusc(N: nat): nat
{
  if (N == 0) then 0
  else
  match GetNth(CalkinWilf(Log2(N,0), GenerateRoot()),N)
  case Pair(n,d,pos) => n
}

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule3_1(n:nat)
  ensures n % 2 == 0 && fusc(n) == fusc(n/2)

lemma rule3_2(n:nat)
  ensures n % 2 == 1 && fusc(n-1) == fusc((n-1)/2)

lemma rule3_3(n:nat)
  ensures n % 2 == 1 && fusc(n+1) == fusc((n+1)/2)

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)

lemma rule4_1(n:nat)
  ensures n % 2 == 0 && fusc(n+1) == fusc(n/2) + fusc(n/2 + 1)

lemma rule4_2(n:nat)
  ensures n % 2 == 1 && fusc(n) == fusc((n-1)/2) + fusc(((n-1)/2)+1)
/*
method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{
  b := 0;
  var n, a := N, 1;
  while (n != 0)
    invariant 0 <= n <= N // J
    invariant fusc(N) == a * fusc(n) + b * fusc(n + 1) // J
    decreases n // D
  {
    ghost var d := n;

    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

    //assert n % 2 != 0 && fusc(N) == a * fusc(n) + b * fusc(n + 1);
    //assert n % 2 == 0 && fusc(N) == a * fusc(n) + b * fusc(n + 1);


    assert n % 2 != 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert n % 2 == 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    
    assert n % 2 == 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert n % 2 != 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);

    if (n % 2 == 0)
    {
      rule4_1(n);
      assert fusc((n/2) + 1) == fusc(n+1) - fusc(n/2);
      rule3_1(n);
      assert fusc(n/2) == fusc(n);
      assert fusc(N) == (a + b) * fusc(n / 2) + b * fusc((n / 2) + 1);
      a := a + b;
      assert fusc(N) == a * fusc(n / 2) + b * fusc((n / 2) + 1);
      n := n / 2;
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    } else {
      rule4_2(n);
      assert fusc(n) - fusc((n-1)/2) == fusc(((n-1)/2)+1);
      rule3_2(n);
      assert fusc((n-1)/2) == fusc(n-1);

      assert fusc(((n-1)/2)+1) == fusc((n+1)/2);
      rule3_3(n);
      assert fusc((n+1)/2) == fusc(n+1);

      assert fusc(N) == b * fusc(n+1) + a * fusc(n);

      assert fusc(N) == b * fusc(((n-1)/2)+1) + a * fusc(n);

      assert fusc(N) == b * fusc(n) - b  * fusc(n) + b  * fusc(((n-1)/2)+1) + a * fusc(n);
      assert fusc(N) == b * fusc(n) - b  * (fusc(n) - fusc(((n-1)/2)+1)) + a * fusc(n);
      assert fusc(N) == b * fusc(n) - b  * fusc((n-1)/2) + a * fusc(n);
      assert fusc(N) == b * fusc(n) - b  * fusc(n-1) + a * fusc(n);
      assert fusc(N) == b * fusc(n) - b  * fusc(n-1) + a * fusc(n);
      assert fusc(N) == a * fusc(n - 1) + b  * fusc(n) - b  * fusc(n-1) + a * fusc(n) - a * fusc(n-1);
      assert fusc(N) == a * fusc(n - 1) + (b + a) * (fusc(n) - fusc(n-1));
 
      assert fusc(N) == a * fusc((n - 1)) + (b + a) * (fusc(n) - fusc((n-1)/2));

      assert fusc(N) == a * fusc((n - 1) / 2) + (b + a) * fusc(((n - 1) / 2) + 1);
      b := b + a;
      assert fusc(N) == a * fusc((n - 1) / 2) + b * fusc(((n - 1) / 2) + 1);
      n := (n - 1) / 2;
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    }
    assert n < d;
    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
  }
  assert n == 0; // !B
  rule1();
  assert fusc(0) == 0;
  rule2();
  assert fusc(1) == 1;
  assert fusc(N) == a * fusc(0) + b * fusc(0 + 1);  // J
  assert fusc(N) == a * 0 + b * 1; // J
  assert b == fusc(N);
}
*/


method ComputePos(num: int, den: int) returns (n: int)
  requires num > 0 && den > 0
  ensures n > 0 && num == fusc(n) && den == fusc(n + 1)
{
  var nu, de := 1, 1;
  n := 1;
  assert n == 1;
  rule2();
  assert fusc(n) == nu;
  //rule6_1();
  assert fusc(n + 1) == de;
  while nu != num && de != den
    invariant n > 0
    invariant nu == fusc(n)
    invariant de == fusc(n + 1)
    decreases num + den - (nu + den)
  {
    assert nu == fusc(n) && de == fusc(n + 1);
    // numerator of n + 1 is denominator of n
    // numerator of n is denominator of n - 1 
    if (n % 2 == 0) {
      //rule5_1(n);
      assert fusc(n + 1) - fusc(n) == fusc(n + 2);
      assert de == fusc(n+1) && nu == fusc(n);
      assert de - nu == fusc(n + 2);
      nu, de := de, de - nu;
      assert nu == fusc(n + 1);
      assert de == fusc(n + 2);
    } else {
      nu := de;
      assert nu == fusc(n+1);
      assert de == fusc(n + 2);
    }

    assert nu == fusc(n+1) && de == fusc(n + 2);
    n := n + 1;
    assert nu == fusc(n) && de == fusc(n + 1);

  }

  assert nu == fusc(n) && de == fusc(n + 1);
  assert nu == num && de == den;

}
/*
method Main()
{
  //var t := CalkinWilf(3, GenerateRoot());
  //Show(t);
  var n : nat;
  print(fusc(11));
  var x := ComputeFusc(11);
  assert fusc(11) == x;
  //var x := GetNth(t, 3, 0);
  //print('\n', x);
}
*/