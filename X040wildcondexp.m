// we use the  3-torsion  subgroup previously computed to compute the wild conductor exponent at 2
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

Zx<x> := PolynomialRing(Q2) ;
f1 := x^6 + 4*x^4 - 8*x^2 + 12;
f2 := x^6 - 6*x^5 + 4*x^4 + 24*x^3 + 256*x^2 - 576*x + 324 ;
f3 := x^8 - 126*x^4 - 648*x^2 - 1323 ;

R1 := Roots(f1,L) ;
R2 := Roots(f2,L) ;
R3 := Roots(f3,L) ;

G,a,b := AutomorphismGroup(L) ;

assert IsIsomorphic(G, GeneralLinearGroup(2,3));
print "Galois group = GL(2,3)";
G0 := RamificationGroup(L, 0) ;
t1 := a(G.2);
s1 := a(G.3);
s2 := a(G.4);
h := a(G.5) ;
t2 := a(G.6);


// we compute ramifcation groups  

G0 := RamificationGroup(L, 0);
G1 := RamificationGroup(L, 1) ;
G2 := RamificationGroup(L, 2) ;
G3 := RamificationGroup(L, 3) ;
G4 := RamificationGroup(L,4);

assert #G4 eq 1 ;
GG0 := sub<G | G.2, G.5,G.3,G.4>;

assert GG0 eq G0 ;
assert IsIsomorphic(G0, SpecialLinearGroup(2,3));

print "G0 = SL(2,3)";

GG1 := sub< G |  G.2, G.3, G.4>;

assert GG1 eq G1 ;

assert IsIsomorphic(G1, SmallGroup(8,4));
print "G1 =Q8";

GG2  :=  sub< G  | G.2 >;

assert GG2 eq G2 ;

GG3 := sub< G  |  G.2 >;

assert GG3 eq G3 ;

assert #G2 eq 2 ;
assert #G3 eq 2;
print "G2=G3=C2";
print "Higher ramification groups are trivial";


// we compute the Galois action on the roots of  f1, f2, f3 

// we first match roots /Q to roots /Q2 and then compute the action of t1, t2, s1, s2, h on the roots over L
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

G,a,b := AutomorphismGroup(L) ;
t1 := a(G.2);
s1 := a(G.3);
s2 := a(G.4);
h := a(G.5);
t2 := a(G.6);


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
dd[i] := m[1] ;
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

f1 := x^6 + 4*x^4 - 8*x^2 + 12;
f2 := x^6 - 6*x^5 + 4*x^4 + 24*x^3 + 256*x^2 - 576*x + 324 ;
f3 := x^8 - 126*x^4 - 648*x^2 - 1323 ;

mf1 := rootsmatch(f1) ;
mf2 := rootsmatch(f2);
mf3 := rootsmatch(f3);

// to ensure the ordering does not change we assert the following:
assert mf1[1] eq [6,4,1,2,3,5];
assert mf1[2] eq  [1,2,3,4,5,6];
assert mf1[3] eq [2,1,6,5,4,3];
assert mf1[4] eq [1,2,3,4,5,6];
assert mf1[5] eq  [1,2,3,4,5,6];
assert mf1[6] eq  [6,5,2,1,3,4];

assert mf2[1] eq [4,2,6,5,1,3];
assert mf2[2] eq [1,2,3,4,5,6];
assert mf2[3] eq [2,1,6,5,4,3];
assert mf2[4] eq [1,2,3,4,5,6];
assert mf2[5] eq [1,2,3,4,5,6];
assert mf2[6] eq [5,6,1,2,3,4];

assert mf3[1] eq [8,5,1,3,4,2,6,7];
assert mf3[2] eq [2,1,4,3,6,5,8,7];
assert mf3[3] eq [1,2,4,3,8,7,6,5];
assert mf3[4] eq [4,3,1,2,8,7,5,6];
assert mf3[5] eq [6,5,7,8,1,2,4,3];
assert mf3[6] eq [1,2,5,6,7,8,3,4];


// we match this with the action on the generating set of J0(40) and compute Galois invariant as follows:

// action of t1

// the action of t1 and invariant subgroup is a follows :


cpt := [ ZN.1, ZN.2,ZN.3, ZN.4, ZN.5, ZN.6, ZN.7, ZN.8, ZN.9, ZN.10, ZN.11, ZN.12, ZN.20, ZN.19, ZN.18, ZN.17, ZN.16, ZN.15, ZN.12, ZN.13 ];
conj := hom< ZN -> ZN | cpt>;
mu := hom< ZN -> J343 | [ hh(ZN.i) - hh(conj(ZN.i)) : i in [1..20]]>;
ker := Kernel(mu);
K1 := sub<J343 | [hh(k) : k in Generators(ker)]>;

// action of  h and invariants 

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

J040G0 := K1 meet K2 meet K3 meet K4 ;

J040G1 := K1 meet  K3 meet K4 ;

J040G2 :=  K1 ;
J040G3 := K1 ;

inds := [ #J040G0, #J040G1, #J040G2, #J040G3] ;
valinds := [ Valuation(inds[i], 3) : i in [1..4] ] ;
nums := [ 6 - valinds[i] : i in [1..4] ];

dens := [ 24/(#G0), 24/(#G1), 24/(#G2), 24/(#G3) ];

summ := [ nums[i]/dens[i] : i in [2..4] ];
print "the wild conductor exponent of X0(40)  at 2 is";
&+summ ;


