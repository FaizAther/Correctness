method GCD2(a: int, b: int) returns (r: int)
requires a >= 0 && b >= 0
decreases b
//ensures gcd(a,b)
{
/*
    a >= 0
    &&
    b => 0

    a >= 0
    &&
    b == 0 && TRUE
    ||
    b > 0 && TRUE

    a >= 0
    &&
    b == 0 && TRUE
    ||
    b > 0 && TRUE
    
    a >= 0
    &&
    b == 0 && a == a
    ||
    b > 0 && gcd(a,b) == gcd(a,b)

    + APPLY RULE i. AND iv. +

    a >= 0
    &&
    b == 0 && a == gcd(a,0)
    ||
    b > 0 && gcd(a,b) == gcd(b,a%b)
    
    + RULE i. AND RULE iv. need a >= 0 && b >= 0 +
    
    b == 0 && a == gcd(a,b)
    ||
    b > 0 && gcd(a,b) == gcd(b,a%b)

    D && C
    ||
    B && E

    C && D
    ||
    ((A || B) && (D || E)

    + ONLY KEEP WHAT IS RELEVENT +

    (A || B) || C
    &&
    D || E

    ( b < 0 || b > 0 ) || a == gcd(a,b) 
    &&
    b == 0 || ( b >= 0 && a % b >= 0 ) &&
              ( gcd(b,(a % b)) == gcd(a,b) )

    b == 0 ==> a == gcd(a,b) 
    &&
    b != 0 ==> 
        ( b >= 0 && a % b >= 0 ) &&
        ( gcd(b,(a % b)) == gcd(a,b) )
*/
    if (b == 0) {
        // a == gcd(a,b)
        r := a;
        // r == gcd(a,b)
    } else {
/*
        ( b >= 0 && a % b >= 0 ) &&
        ( gcd(b,(a % b)) == gcd(a,b) )

        + One Point Rule +
        ( b >= 0 && a % b >= 0 ) &&
            forall r' ::
                ( r' == gcd(b,(a % b)) )
        ==> ( r' == gcd(a,b) )

       ( a >= 0 && b >= 0 )[a,b\b,a%b] &&
            forall r' ::
                ( r == gcd(a,b) )[a,b,r\b,(a % b),r']
        ==> ( r == gcd(a,b) )[r\r']

        wp(r := M(E1,E2), Q)
            <===>
        P[a,b\E1,E2] &&
            forall r' ::
                R[a,b,r\E1,E2,r']
        ==> Q[r\r']

        + Method Rule +
 */
        r := GCD2(b, a % b);
        // r == gcd(a,b)
    }
    // r == gcd(a,b)
}
// r == gcd(a,b)