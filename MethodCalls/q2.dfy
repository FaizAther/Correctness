/**
  (b) Derive a program that
      returns the position in the above list of rational numbers
      with numerator numand denominator den.
      Your program must be shown to satisfy
      partial correctness with respect
      to the following specification.
      Your program should call ComputeFusc but
      must not call it more than once with the same argument.
  
  (b) Derived code (3marks)
      Weakest precondition proof (4mark)
*/

function fusc(n: int): nat

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule4(n:nat)
  ensures fusc(2*n + 1) == fusc(n) + fusc(n + 1)


method ComputePos(num: int, den: int) returns (n: int)
  requires num > 0 && den > 0
  ensures n > 0 && num == fusc(n) && den == fusc(n + 1)
{
  var nu, de := 1, 1;
  n := 1;
  assert n == 1;

  rule2();
  assert fusc(n) == nu;

  rule3(n);
  assert fusc(n + 1) == de;

  assert nu == fusc(n) && de == fusc(n + 1);

  while !(nu == num && de == den)
    invariant n > 0
    invariant nu == fusc(n)
    invariant de == fusc(n + 1)
  {
    assert nu == fusc(n) && de == fusc(n + 1);

    assert nu == fusc(n);
    assert de == fusc(n + 1);

    var tmp := ComputeFusc(n+2);

    assert tmp == fusc(n+2);

    nu, de := de, tmp;

    assert nu == fusc(n + 1);
    assert de == fusc(n + 2);

    assert nu == fusc(n + 1) && de == fusc(n + 2);

    n := n + 1;

    assert nu == fusc(n) && de == fusc(n + 1);
  }

  assert nu == fusc(n) && de == fusc(n + 1);
  assert nu == num && de == den;
}


method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{
  b := 0;
  var n, a := N, 1;
  assert 0 <= n <= N;
  assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

  while (n != 0)
    invariant 0 <= n <= N // J
    invariant fusc(N) == a * fusc(n) + b * fusc(n + 1) // J
    decreases n // D
  {
    ghost var d := n; // termination metric

    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

    assert n != 0;

    assert (n % 2 != 0 && n % 2 == 0) || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert (n % 2 != 0 || n % 2 == 0) ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);

    assert n % 2 != 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert n % 2 == 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    
    assert n % 2 == 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert n % 2 != 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);

    if (n % 2 == 0)
    {
      rule4(n/2);
      assert fusc((n/2) + 1) == fusc(n + 1) - fusc(n/2);
      
      rule3(n/2);
      assert fusc(n/2) == fusc(n);
      
      assert fusc(N) == (a + b) * fusc(n/2) + b * fusc((n/2) + 1);
      
      a := a + b;
      
      assert fusc(N) == a * fusc(n/2) + b * fusc((n/2) + 1);
      
      n := n / 2;
      
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    } else {
      rule4((n-1)/2);
      assert fusc(n) - fusc((n-1)/2) == fusc(((n-1)/2)+1);
      
      rule3((n-1)/2);
      assert fusc((n-1)/2) == fusc(n-1);

      assert fusc(((n-1)/2)+1) == fusc((n+1)/2);
      
      rule3((n+1)/2);
      assert fusc((n+1)/2) == fusc(n+1);

      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

      assert fusc(N) == b * fusc(((n-1)/2)+1) + a * fusc(n);

      assert fusc(N) ==
              b * fusc(n) - b  * fusc(n) + b  * fusc(((n-1)/2)+1) + a * fusc(n);
      
      assert fusc(N) ==
              b * fusc(n) - b  * (fusc(n) - fusc(((n-1)/2)+1)) + a * fusc(n);
      
      assert fusc(N) == b * fusc(n) - b  * fusc((n-1)/2) + a * fusc(n);
      
      assert fusc(N) == b * fusc(n) - b  * fusc(n-1) + a * fusc(n);
      
      assert fusc(N) == b * fusc(n) - b  * fusc(n-1) + a * fusc(n);
      
      assert fusc(N) ==
              a * fusc(n - 1) + b  * fusc(n) - b  * fusc(n-1) + a * fusc(n) - a * fusc(n-1);
      assert fusc(N) == a * fusc(n - 1) + (b + a) * (fusc(n) - fusc(n-1));
 
      assert fusc(N) == a * fusc((n - 1)) + (b + a) * (fusc(n) - fusc((n-1)/2));

      assert fusc(N) == a * fusc((n - 1) / 2) + (b + a) * fusc(((n - 1) / 2) + 1);
      
      b := b + a;
      
      assert fusc(N) == a * fusc((n - 1) / 2) + b * fusc(((n - 1) / 2) + 1);
      
      n := (n - 1) / 2;

      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    }
    assert n < d; // termination metric
    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);  // J
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