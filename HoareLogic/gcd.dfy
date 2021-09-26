function method abs(a:int): int
{
    if a < 0 then -1 * a
    else a
}

function method max(a:int, b:int): int
{
    if (a > b) then a
    else b
}

function method min(a:int, b:int): int
{
    if (b < a) then b
    else a
}

function method quotient(p:int, q:int): int
{
    if min(p, q) == 0 then abs(max(p, q))
    else max(p, q) / min(p, q)
}

function method remainder(p:int, q:int): int
{
    if min(p, q) == 0 then abs(max(p, q))
    else max(p, q) - quotient(p, q) * min(p, q)
}

function method gcd_h(a:nat, b:nat): nat
decreases b
{
    if (min(a,b) == 0) then max(a,b)
    else if (a == b) then a
    else if (min(a, b) == 1) then 1 
    else if remainder(a,b) == 0 then min(a,b)
    else gcd_h(min(a, b), remainder(a, b))
}

function method gcd(a:int, b:int): nat
{
    gcd_h(abs(a), abs(b))
}

method Main()
{
    var x := remainder(-2, 5);
    print(x);
}
