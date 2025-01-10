

// we use the 3-torsion  subgroup previously computed to compute the wild conductor exponent at 2

load  "J040ThreeTorsionSubgroup.m";

Q2 := pAdicField(2, 500) ;
Zx<x> := PolynomialRing(Q2) ;
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

L := LocalField(Q2, f) ;

// we compute the action of the ramification groups on the 3-torsion by computing it on the minimal polynomials of the  3-torsion 

Zx<x> := PolynomialRing(Q2) ;
f1 := x^6 + 4*x^4 - 8*x^2 + 12;
f2 := x^6 - 6*x^5 + 4*x^4 + 24*x^3 + 256*x^2 - 576*x + 324 ;
f3 := x^8 - 126*x^4 - 648*x^2 - 1323 ;

R1 := Roots(f1,L) ;
R2 := Roots(f2,L) ;
R3 := Roots(f3,L) ;

// compute the ramification subgroups 
G,a,b := AutomorphismGroup(L) ;
G0 := RamificationGroup(L, 0) ;
Gg := Generators(G);
Gg := SetToSequence(Gg) ;

t1 := G.2;
s1 := G.3;
s2 := G.4;
b := G.5 ;

G1 := RamificationGroup(L, 1) ;
G2 := RamificationGroup(L, 2) ;
G3 := RamificationGroup(L, 3) ;
G4 := RamificationGroup(L,4);

assert #G4 eq 1 ;

// we find generators of the  ramification groups //
GG0 := sub<G | t1, b,s1,s2>;

assert GG0 eq G0 ;

GG1 := sub< G |  t1, s1, s2>;

assert GG1 eq G1 ;

GG2  :=  sub< G  | t1 >;

assert GG2 eq G2 ;

GG3 := sub< G  |  t1 >;

assert GG3 eq G3 ;



// we compute the action of  t1, s1, s2,  b on the set of roots of  f1,f2,f3 and compute invariants 
// note that we compute the action  on the roots of the polynomials  over L, and then determine the permuation of these  which corresponds to the roots over the number field K (this is done with a simple valuation computation)
//  the computation is completed over the finite field F_13^2  and using the reduction map 

// the action of t1 and invariant subgroup is a follows :


cpt := [ ZN.1, ZN.2,ZN.3, ZN.4, ZN.5, ZN.6, ZN.7, ZN.8, ZN.9, ZN.10, ZN.11, ZN.12, ZN.20, ZN.19, ZN.18, ZN.17, ZN.16, ZN.15, ZN.12, ZN.13 ];
conj := hom< ZN -> ZN | cpt>;
mu := hom< ZN -> J343 | [ hh(ZN.i) - hh(conj(ZN.i)) : i in [1..20]]>;
ker := Kernel(mu);
K1 := sub<J343 | [hh(k) : k in Generators(ker)]>;


// action of  b and invariants 

cpt := [ ZN.2, ZN.3, ZN.1, ZN.6, ZN.4, ZN.5, ZN.8, ZN.9, ZN.7, ZN.12, ZN.10, ZN.11, ZN.17, ZN.20, ZN.15, ZN.14, ZN.19, ZN.18, ZN.13, ZN.16] ;
conj := hom< ZN -> ZN | cpt>;
mu := hom< ZN -> J343 | [ hh(ZN.i) - hh(conj(ZN.i)) : i in [1..20]]>;
ker := Kernel(mu);
K2 := sub<J343 | [hh(k) : k in Generators(ker)]>;



// action of  s1 and  invariants 

cpt :=  [ ZN.1, ZN.2,ZN.3, ZN.4, ZN.5, ZN.6, ZN.7, ZN.8, ZN.9, ZN.10, ZN.11, ZN.12, ZN.19, ZN.13, ZN.17, ZN.15, ZN.18, ZN.16, ZN.20, ZN.14] ;
conj := hom< ZN -> ZN | cpt>;
mu := hom< ZN -> J343 | [ hh(ZN.i) - hh(conj(ZN.i)) : i in [1..20]]>;
ker := Kernel(mu);
K3 := sub<J343 | [hh(k) : k in Generators(ker)]>;

// action of s2 and invariants 

cpt := [  ZN.1, ZN.2,ZN.3, ZN.4, ZN.5, ZN.6, ZN.7, ZN.8, ZN.9, ZN.10, ZN.11, ZN.12, ZN.16, ZN.15, ZN.19, ZN.20, ZN.13, ZN.14, ZN.18, ZN.17 ];
conj := hom< ZN -> ZN | cpt>;
mu := hom< ZN -> J343 | [ hh(ZN.i) - hh(conj(ZN.i)) : i in [1..20]]>;
ker := Kernel(mu);
K4 := sub<J343 | [hh(k) : k in Generators(ker)]>;



// thus the invariant subgroup under G0 is:

J040G0 := K1 meet K2 meet K3 meet K4 ;

J040G1 := K1 meet  K3 meet K4 ;

J040G2 :=  K1 ;
J040G3 := K1 ;


// hence the wild conductor exponent at 2 is 

inds := [ #J040G0, #J040G1, #J040G2, #J040G3] ;
valinds := [ Valuation(inds[i], 3) : i in [1..4] ] ;
nums := [ 6 - valinds[i] : i in [1..4] ];

dens := [ 24/(#G0), 24/(#G1), 24/(#G2), 24/(#G3) ];

summ := [ nums[i]/dens[i] : i in [2..4] ];

print "the wild conductor exponent of X0(40)  at 2 is";
&+summ ;


