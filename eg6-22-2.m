
/*

202307190902
a computation in example 6.22.

** this only works for quadratic k/F **

*/

function n_lcm(F)
    d := Degree(F);
    PF := { [p, Valuation(Ceiling( 2*d/(p-1)) ,p) + 1] 
        : p in PrimesUpTo(2*d + 1)
        | IsDivisibleBy(2*d, EulerPhi(p)) };

    return &*[ pf[1]^Max( { m : m in [0..pf[2]]
        | Degree( Compositum( F, CyclotomicField(pf[1]^m) ) ) le 2*d } ) 
        : pf in PF ];
end function;

P_Q<T_Q> := PolynomialRing(Rationals());
F := SplittingField(T_Q^3 - T_Q^2 - 2*T_Q + 1);
d := Degree(F);
O := IntegerRing(F);
IB := IntegralBasis(F, O);
"F is:", F;

P_F<T_F> := PolynomialRing(F);
k := SplittingField(T_F^2 + 17);
h_k := ClassNumber(k);
"k is:", k;
"Is k/Q normal?", IsNormal(k);
"h_k =", h_k;
"n_lcm =", n_lcm(F);

ell_sup := 40;
Nice_ells := [p : p in PrimesUpTo(ell_sup)
    | #Decomposition(k, p) eq Degree(k) and not IsDivisibleBy(n_lcm(F)*h_k, p)];

Nicer_ells := {};

for ell in Nice_ells do;
    X := [];
    for i in [1..d] do;
        X[i] := Floor( AbsoluteValue(
            2*Sqrt(ell)/RealEmbeddings(IB[i])[1] ) );
    end for;

    S := { &+[x[i]*IB[i] : i in [1..d]]
          : x in CartesianProduct([ [-X[i]..X[i]] : i in [1..d] ])
          | &and[ AbsoluteValue( RealEmbeddings( &+[x[i]*IB[i] : i in [1..d]] )[j] )
                le 2*Sqrt(ell) : j in [1..d]
              ]
    };
    // S = {b in O_F : for every real infinite place v of F, |b|_v <= 2\sqrt{ell}}.

    AA := {SplittingField(T_F^2 + b*T_F + ell) : b in S};
    if not &or[IsIsomorphic(k,K) : K in AA] then;
        Nicer_ells := Nicer_ells join {ell};
    end if;
end for;

"The set of primes <=", ell_sup, "satisfying the condition 1 of thm. 6.20 is:", Nicer_ells;




/*

////////////////////////////////////
//OUTPUT
////////////////////////////////////

F is: Number Field with defining polynomial T_Q^3 - T_Q^2 - 2*T_Q + 1 over the
Rational Field
k is: Number Field with defining polynomial x^6 - 2*x^5 + 48*x^4 - 62*x^3 +
    903*x^2 - 616*x + 6461 over the Rational Field
Is k/Q normal? true
h_k = 36
n_lcm = 84
The set of primes <= 40 satisfying the condition 1 of thm. 6.20 is: { 13 }


*/