// we compute the action of the Galois group and ramification groups on roots of polynomials defining three torsion 


// we first match roots /Q to roots /Q2

Zx<x> := PolynomialRing(Rationals());
Q2 := pAdicField(2, 500) ;
f :=  x^48 - 22*x^47 + 220*x^46 - 1298*x^45 + 4840*x^44 - 10758*x^43 + 7848*x^42
+ 30564*x^41 - 90644*x^40 - 54378*x^39 + 983934*x^38 - 3228430*x^37 + 
6037118*x^36 - 6706868*x^35 + 3859158*x^34 - 6290682*x^33 + 41469355*x^32 - 
151827480*x^31 + 375328308*x^30 - 727099012*x^29 + 1204881284*x^28 - 
1812362612*x^27 + 2558319144*x^26 - 3402905364*x^25 + 4192192588*x^24 - 
4669768140*x^23 + 4602283152*x^22 - 3939374364*x^21 + 2873125672*x^20 - 
1738390504*x^19 + 830314684*x^18 - 275496188*x^17 + 30094447*x^16 + 
31178478*x^15 - 22364652*x^14 + 5362086*x^13 + 2307708*x^12 - 2995626*x^11 + 
1676724*x^10 - 615660*x^9 + 121728*x^8 + 25686*x^7 - 31194*x^6 + 9162*x^5 + 
1458*x^4 - 2088*x^3 + 738*x^2 - 126*x + 9 ;

K := NumberField(f) ;
L := LocalField(Q2, f) ;

// given a polynomial g, the following matches the roots of g/K to  the roots of g/L  
// input = g, output = [i,j] interpreted to mean when computed  by magma the ith root/K = jth root over L 

G,a,b := AutomorphismGroup(L) ;
t1 := a(G.2);
s1 := a(G.3);
s2 := a(G.4);
h := a(G.5);
t2 := a(G.6);

[G.2, G.6, G.3, G.4, G.5] ;




rootsmatch := function(g) ;
r1 := Roots(g, K);
r2 := Roots(g, L) ;
d := Degree(L) ;
r1 := [a[1] : a in r1] ;
rr1 := [ Eltseq(a) : a in r1];
RR1 := [ &+[ a[i]*L.1^(i-1) : i in [1..d] ] : a in rr1 ];
R2 := [a[1] : a in r2] ; 
vv := [ [Valuation(RR1[i] - R2[j]) : j in [1..#r1] ] : i in [1..#r1] ] ;
dd := [] ;
for i in [1..#r1] do ;
b := vv[i] ;
m := [ j : j in [1..#r1] | b[j] eq Maximum(b) ] ;
dd[i] := [ i, m[1] ];
end for;
at1 := [] ;
for i in [1..#R2] do ;
T := [ Valuation(t1(R2[i]) - R2[j]) : j in [1..#R2] ] ;
m := Maximum(T) ;
mm := [ i : i in [1..#R2] | T[i] eq m ] ;
at1[i] := mm[1] ;
end for ;
at2 := [] ;
for i in [1..#R2] do ;
T := [ Valuation(t2(R2[i]) - R2[j]) : j in [1..#R2] ] ;
m := Maximum(T) ;
mm := [ i : i in [1..#R2] | T[i] eq m ] ;
at2[i] := mm[1] ;
end for ;
as1 := [] ;
for i in [1..#R2] do ;
T := [ Valuation(s1(R2[i]) - R2[j]) : j in [1..#R2] ] ;
m := Maximum(T) ;
mm := [ i : i in [1..#R2] | T[i] eq m ] ;
as1[i] := mm[1] ;
end for ;
as2 := [] ;
for i in [1..#R2] do ;
T := [ Valuation(s2(R2[i]) - R2[j]) : j in [1..#R2] ] ;
m := Maximum(T) ;
mm := [ i : i in [1..#R2] | T[i] eq m ] ;
as2[i] := mm[1] ;
end for ;
ah := [] ;
for i in [1..#R2] do ;
T := [ Valuation(h(R2[i]) - R2[j]) : j in [1..#R2] ] ;
m := Maximum(T) ;
mm := [ i : i in [1..#R2] | T[i] eq m ] ;
ah[i] := mm[1] ;
end for ;
return <dd, at1, at2, as1, as2, ah>;
end function ;

// our torsion polynomials 
f1 := x^6 + 4*x^4 - 8*x^2 + 12;
f2 := x^6 - 6*x^5 + 4*x^4 + 24*x^3 + 256*x^2 - 576*x + 324 ;
f3 := x^8 - 126*x^4 - 648*x^2 - 1323 ;

mf1 := rootsmatch(f1) ;
mf2 := rootsmatch(f2);
mf3 := rootsmatch(f3);

