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

lemma rule5_1(n:nat)
  ensures n % 2 == 0 && fusc(n + 1) - fusc(n) == fusc(n + 2)

lemma rule6_1()
  ensures fusc(2) == 1


lemma rule7_1(n: nat)
  ensures n % 2 == 0 && fusc(n) < fusc(n + 1)

lemma rule7_2(n: nat)
ensures n % 2 == 1 && fusc(n) > fusc(n + 1)

lemma rule8_1(num: nat, den: nat)
  ensures num == den && fusc(1) == num && fusc(1) == den

function method abs(x:int): nat
{
  if x < 0 then -1 * x else x
}

method ComputePos(num: int, den: int) returns (n: int)
  requires num > 0 && den > 0 // && gcd(num, den) == 1
  ensures n > 0 && num == fusc(n) && den == fusc(n + 1)
  decreases num, den
{
  if (num == 1 && den == 1)
  {
    rule2();
    n := 1;
    rule3(n);
    assert num == fusc(n) && den == fusc(n + 1);
  } else if (num == den) // or gcd is not 1 then return 0
  {
    n := 1;
    assert num == den;
    assert num / den == 1;
    rule8_1(num, den);
    assert num == fusc(n) && den == fusc(n + 1);
  }
  else {
    if (num < den) { // left
      assert num < den;

      n := ComputePos(num, den - num);

      rule7_1(n);
      assert fusc(n/2) == num;
      assert fusc(den-num) == fusc((n/2) + 1);
      assert n % 2 == 0;
      assert n * 2 > 0 && num == fusc(n * 2) && den == fusc(n * 2 + 1);
      // { n * 2 > 0 && num == fusc(n * 2) && den == fusc(n * 2 + 1) }

      n := n * 2;

      // { n > 0 && num == fusc(n) && den == fusc(n + 1) }
    } else { // right
      assert num > den;

      n := ComputePos(num - den, den);

      rule7_2(n);
      assert n % 2 == 1;
      assert (n * 2) + 1 > 0 && num == fusc((n * 2) + 1) && den == fusc((n * 2) + 1 + 1);
      // { (n * 2) + 1 > 0 && num == fusc((n * 2) + 1) && den == fusc((n * 2) + 1 + 1) }

      n := (n * 2) + 1;

      // { n > 0 && num == fusc(n) && den == fusc(n + 1) }
    }
    // { n > 0 && num == fusc(n) && den == fusc(n + 1) }
  }
}
// { n > 0 && num == fusc(n) && den == fusc(n + 1) }