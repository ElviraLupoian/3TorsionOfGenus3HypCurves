// we verify that the 3 orbits previously computed are sufficient to generate the entire 3-torsion subgroup of J0(40) 


Zxy< x, y> := PolynomialRing(Integers(),2 );

// we work with the following model of the curve

f := y^2 - ( x^8 +8*x^6 - 2*x^4 + 8*x^2 + 1 ) ;
A2 := AffineSpace(Zxy) ;
X := Curve(A2, f) ;

// we found that all 3 orbits are defined over the following degree 48 number field 

Zx<x> := PolynomialRing(Integers()) ;
f :=  x^48 - 22*x^47 + 220*x^46 - 1298*x^45 + 4840*x^44 - 10758*x^43 + 7848*x^42 + 30564*x^41 - 90644*x^40 - 54378*x^39 + 983934*x^38 - 3228430*x^37 + 6037118*x^36 - 6706868*x^35 + 3859158*x^34 - 6290682*x^33 + 41469355*x^32 - 151827480*x^31 + 375328308*x^30 - 727099012*x^29 + 1204881284*x^28 - 1812362612*x^27 + 2558319144*x^26 - 3402905364*x^25 + 4192192588*x^24 - 4669768140*x^23 + 4602283152*x^22 - 3939374364*x^21 + 2873125672*x^20 - 1738390504*x^19 + 830314684*x^18 - 275496188*x^17 + 30094447*x^16 + 31178478*x^15 - 22364652*x^14 + 5362086*x^13 + 2307708*x^12 - 2995626*x^11 + 1676724*x^10 - 615660*x^9 + 121728*x^8 + 25686*x^7 - 31194*x^6 + 9162*x^5 + 1458*x^4 - 2088*x^3 + 738*x^2 - 126*x + 9 ;

K := NumberField(f) ;
OK := MaximalOrder(K) ;

PP := PrimesUpTo(400, K) ;
P := PP[13] ;

F343, pi := ResidueClassField(P) ;
X343 := BaseChange(X, F343) ;
Cl343,phi,psi := ClassGroup(X343) ;
Z := FreeAbelianGroup(1);
degr := hom<Cl343 -> Z | [ Degree(phi(g)) : g in OrderedGenerators(Cl343)]>;

// the points of J0(40) over F_13^2
J343 := Kernel(degr) ;

// note that reduction modulo P is injective on torsion 
// we will compute the image of our torsion subgroup under the reduction modulo P map


FX343 := FunctionField(X343) ; 
ZX<x> := PolynomialRing(K) ;
f1 := x^6 + 4*x^4 - 8*x^2 + 12;
Zu<u> := PolynomialRing(K) ;
s1 := u + 1 ;
s2 := (-1/9)*(u^5 + u^3 + 16*u  + 18) ;
s3 := (-1/3)*(u^5 + u^3 + 4*u  + 3) ;
s4 := (-1/3)*(u^5 + u^3 + u  - 6) ;
s5 := (-1/9)*(u^5 + u^3 + 7*u  + 9) ;

R := Roots(f1, K) ;
r1 := R ;
a := [ [R[i,1] , Evaluate(s1, R[i,1]), Evaluate(s2, R[i,1]), Evaluate(s3, R[\
i,1]), Evaluate(s4, R[i,1]), Evaluate(s5, R[i,1]) ] : i in [1..#R] ] ; 

a1 := a;

ZX<x> := PolynomialRing(K) ;
f1 := x^6 - 6*x^5 + 4*x^4 + 24*x^3 + 256*x^2 - 576*x + 324 ;
Zu<u> := PolynomialRing(K) ;
s1 := 1/198*(-u^4 + 4*u^3 + 58*u^2 - 124*u + 126); 
s2 := (-1/99)*(u^4 - 4*u^3 - 58*u^2 + 322*u  + 468) ;
s3 := (-1/99)*(u^4 - 4*u^3 - 58*u^2 - 74*u + 765) ;
s4 := (-1/99)*(u^4 - 4*u^3 - 58*u^2 - 173*u  + 468) ;
s5 := (1/198)*(u^4 - 4*u^3 - 58*u^2 + 520*u  - 522 ) ;

R := Roots(f1, K) ;
r2 := R ;
a := [ [R[i,1] , Evaluate(s1, R[i,1]), Evaluate(s2, R[i,1]), Evaluate(s3, R[\
i,1]), Evaluate(s4, R[i,1]), Evaluate(s5, R[i,1]) ] : i in [1..#R] ] ; 

a2 := a;

ZX<x> := PolynomialRing(K) ;
f1 := x^8 - 126*x^4 - 648*x^2 - 1323 ;
Zu<u> := PolynomialRing(K) ;
s2 := (1/189)*(u^7 - 63*u^3 - 648*u );
s4 := -u ;
R := Roots(f1, K) ;
r3 := R ;
a := [ [R[i,1] , -1, Evaluate(s2, R[i,1]),3, Evaluate(s4, R[i,1]), 1 ] : i in [1..#R] ] ; 
a3 := a ;

ZX<x> := PolynomialRing(K) ;
f1 := x^6 + x^4 + 67*x^2 + 363 ;
Zu<u> := PolynomialRing(K) ;
s2 := (1/99)*(u^5 + 34*u^3 - 197*u ) ;
s4 := -u ;
R := Roots(f1, K) ;
r4 := R ;
a := [ [R[i,1] , 1, Evaluate(s2, R[i,1]),-5, Evaluate(s4, R[i,1]), -1 ] : i in [1..#R] ] ; 
a4 := a ;

a := a1 cat a2 cat a3 ;
a := [ [1] cat b : b in a ];
add := [ [ Denominator(b) : b in c ] : c in a ] ;
addl := [ Lcm(b)  : b in add ];
aa := [ [addl[i]*c : c in a[i] ] : i in [1..#a] ] ;
aao := [ [OK ! b : b in c ] : c in aa ] ;

Zxy<x,y> := PolynomialRing(F343,2) ;
g1 := x^2*y - x^6 -4*x^4 ;
g2 := x*y - x^5  ;
g3 := y - x^4 ;

A := aao ;
D := [] ;
A2 := [] ;

for i in [1..#A] do ;
a1 := A[i] ;
a1 :=  [ [ Integers() ! a : a in Eltseq(b) ] : b in a1 ];
ga1 := [ Gcd(a) : a in a1 ];
g := Gcd(ga1) ;
a1g := [ [ 1/g*a : a in b ] : b in a1 ];
a1 := [ OK ! a : a in a1g ];
a1f23 := [ pi(a) : a in a1 ];
a1 := a1f23;
A2[i] := a1 ;
l1 := a1[1]* g1 + a1[2]*g2 + a1[3]*g3 + a1[4]*x^3 + a1[5]*x^2 + a1[6]*x + a1[7] ;
ll1 := Evaluate( l1, [ FX343.1, FX343.2] ) ;
d1 := Divisor(ll1) ;
D[i] := d1;
end for ;

divs := [] ;

for i in [1..#D] do ;
d1 := D[i];
d1d := [ a[2] : a in Decomposition(d1) ] ;
d1d := [ 1/3*a : a in d1d ] ;
d1d := [ Integers() ! a : a in d1d] ;
pd1 := [ a[1] : a in Decomposition(d1) ];
D1 := &+ [ d1d[i]*pd1[i] : i in [1..#d1d ] ];
divs[i] := D1 ;
end for ;

H := [ psi(a) : a in divs];
ZN := FreeAbelianGroup(#H) ;
hh := hom< ZN -> J343 | [ a : a in H ] >;
ihh := Image(hh) ;
 
m := #ihh ;

assert m eq 3^6;

// thus the 3 orbits computed generate the entire 3-torsion subgroup 


// through experimentation we find a basis for the three torsion 

HH := [ psi(divs[1]), psi(divs[2]), psi(divs[7]), psi(divs[8]), psi(divs[13]), psi(divs[14])] ;
ZNN := FreeAbelianGroup(#HH) ;
hhh := hom< ZNN -> J343 | [ a : a in HH ] >;
ihhh := Image(hhh) ;

assert #ihhh eq 3^6;

// relations 

assert psi(2*divs[1] + 2*divs[2]) eq psi(divs[3]);
assert psi(divs[1] + divs[2]) eq psi(divs[4]);
assert psi(2*divs[2]) eq psi(divs[5]);
assert psi(2*divs[1]) eq psi(divs[6]);


assert psi(2*divs[7] + 2*divs[8]) eq psi(divs[9]);
assert psi(divs[1] + 2*divs[2] +  2*divs[8]) eq psi(divs[10]);
assert psi(divs[1] + 2*divs[2] +  2*divs[7]) eq psi(divs[11]);
assert psi(divs[1] + 2*divs[2] +  divs[7] + divs[8]) eq psi(divs[12]);

assert psi(2*divs[13] + 2*divs[14]) eq psi(divs[15]);
assert psi(divs[13] + 2*divs[14]) eq psi(divs[16]);
assert psi(2*divs[13] + divs[14]) eq psi(divs[17]);
assert psi(divs[13] + divs[14]) eq psi(divs[18]);
assert psi(2*divs[14]) eq psi(divs[19]);
assert psi(2*divs[13]) eq psi(divs[20]);


