method Tangent(r: array<int>, x: array<int>)
  returns (b: bool)
  requires forall i, j :: 0 <= i < j < x.Length ==> x[i] < x[j]
  ensures x.Length == 0 || r.Length == 0 ==> b == false
  ensures x.Length > 0 && r.Length > 0 && b == true ==>
            exists ri :: 0 <= ri < r.Length &&
            exists xi :: 0 <= xi < x.Length &&
            r[ri] == x[xi]
            
  ensures b == false ==> forall xi :: 0 <= xi < x.Length ==>
            forall ri :: 0 <= ri < r.Length ==>
              r[ri] != x[xi]
{
  if (x.Length == 0 || r.Length == 0) {
    b := false;
  } else {

    assert x.Length > 0 && r.Length > 0;
    b := false;
    var xMin, xMax := x[0], x[x.Length-1];
    var n, N := 0, -1;
    var f := -1;

    while n != r.Length && b
      invariant -1 <= f <= x.Length
      invariant 0 <= n <= r.Length
      invariant N != -1 ==>
                  0 <= N < r.Length &&
                  0 <= f < x.Length &&
                  x[f] == r[N];
      invariant b == true ==>
            exists ri :: 0 <= ri < r.Length &&
            exists xi :: 0 <= xi < x.Length &&
            r[ri] == x[xi]
      invariant b == false ==> forall xi :: 0 <= xi < n ==>
            forall ri :: 0 <= ri < r.Length ==>
              r[ri] != x[xi]
      decreases r.Length - n
      {
        f := BinarySearch(x, r[n]);

        if (f == x.Length || x[f] != r[n]) {
          f := -1;
          b := false;
          N := n;
        } else {
          assert x[f] == r[n];
          b := true;
        }

        n := n + 1;
      }
      assert n == r.Length || !b;
    //assert false;
  }
}


// method Find(r: int, arr: array<int>, min: int, max: int) returns (index: int)
//   requires 0 <= min < arr.Length
//   requires 0 <= max <= arr.Length
//   requires min <= max
//   requires forall i, j :: 0 <= i < j < arr.Length ==> j > i
//   ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != r
//   ensures index != -1 && 0 <= index < arr.Length && arr[index] == r
//   decreases max-min



method BinarySearch(a: array<int>, circle: int)
  returns (n: int)
  requires forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < circle
  ensures forall i :: n <= i < a.Length ==> circle <= a[i]
{
  var lo, hi := 0, a.Length;
  
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < circle
    invariant forall i :: hi <= i < a.Length ==> a[i] >= circle
  {
    var mid := (lo + hi) / 2;
    calc {
      lo;
    ==
      (lo + lo) / 2;
    <= { assert lo <= hi; }
      (lo + hi) / 2;
    < { assert lo < hi; }
      (hi + hi) / 2;
    ==
      hi;
    }
    if (a[mid] < circle) {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  
  n := lo;
}



/**
(1)
  Let the integer array r of length M
  represent a set of distinct circles in the (x,y)-plane.
  Circle i ( for 0 <= i < M) has centre (0, 0) and radius r[i].
  Let the integer array x of length N
  represent a set of distinct vertical lines.
  Line i (for 0 <= i < N) has equation x = x[i] where x[i] >= 0.

(a)
  Assuming the values of x increase
  as we move from position 0 to x.Length -1,
  write a specification and implementation
  of a Dafny method Tangent that,
  given r and x as parameters,
  returns a boolean value
  indicating whether or not there exists a line in x
  that is tangent to a circle in r.
  The implementation should not
    x)
      iterate over either array
      once a tangent has been found
    x)
      for a given circle in r,
      should not iterate over array x
      once it can be deduced that
      no tangent will be found for that circle.
    x)
      Also, it must not use return or break statements.
  
  Verify your implementation using the Dafny verifier.
  The following lemma maybe necessary
  depending on your approach to the
  specification and implementation.
  There is no requirement to use it.

  i)    Pre and postconditions  (1.5 marks)
  ii)   Loop invariants         (4.5 marks)
  iii)  Termination metrics     (1.5 marks)
  iv)   Code                    (2.5 marks)
*/