load "X040Scheme.m";
load "X040Approx.m";

Zaa<[a]> := PolynomialRing(CC, 10) ;
E := [] ;


for i in [1..10] do ;
E[i] := Zaa ! CE[i] ;
end for ;

J := JacobianMatrix(E) ;

load "generalprogs.m";

// we compute the first orbit  of 3-torsion pts //

a1  := AP[1] ;

a1 := [ CC ! b : b in a1 ];
N := [a1] ;


// we perform 900 steps of NR //


for i in [2..900] do ;
a := N[i-1] ;
a := [ CC ! b : b in a] ;
N[i] := nr(a) ;
end for ;

// we compute the minimal polynomial of the first coordinate //

m1 :=  lllcoord(N[900][1],1200,6) ;
Zy<y> := PolynomialRing(Integers()) ;

t := &+[ m1[i]*y^(7-i) : i in [1..7] ] ;


// we find relations between the coordinates 
r2 := relllcoord([ N[900][1], N[900][3]], 1200, 6) ;

Zuv<u,v> := PolynomialRing(Rationals(),2) ;
s2 := [ r2[i]*u^(6-i) : i in [1..6] ] cat [ r2[7]*v] ;
s2 := &+s2 ;


r3 := relllcoord([ N[900][1], N[900][4]], 1200, 6) ;
s3 := [ r3[i]*u^(6-i) : i in [1..6] ] cat [ r3[7]*v] ;
s3 := &+s3 ;

r4 := relllcoord([ N[900][1], N[900][5]], 1200, 6) ;
s4 := [ r4[i]*u^(6-i) : i in [1..6] ] cat [ r4[7]*v] ;
s4 := &+s4 ;


r5 := relllcoord([ N[900][1], N[900][6]], 1200, 6) ;
s5 := [ r5[i]*u^(6-i) : i in [1..6] ] cat [ r5[7]*v] ;
s5 := &+s5 ;


// to compute the relations between the first two coordiantes we compute the minimal polynomial of the second coordinate and factorise this over the number field defined by the minimal polynomail of the first coordinate

K := NumberField(t) ;
tt := lll1coord(Real(N[900][2]), 1200,3) ;
Zy<y> := PolynomialRing(Rationals()) ;
tt := &+[ tt[i]*y^(4-i) : i in [1..4] ] ;
Rts := Roots(tt,K) ;
Rtss := [ a[1] : a in Rts] ;

Rtss := [ Eltseq(a) : a in Rtss] ;
Z<y> := PolynomialRing(Rationals());
eqs := [ [ a[i]*y^(i-1) : i in [1..6]] : a in Rtss] ;
T := [ &+b : b in eqs];
 TT := [ Evaluate(a, N[900][1]) : a in T ] ;
TT := [ TT[i] - N[900][2] : i in [1..3] ] ;

ind := [ i : i in [1..3] | Real(TT[i]) le 1/1000];
ind := ind[1] ;
s1 := Evaluate(T[ind], u) - v ;

// we verify that the above expression define points on our scheme //

// we begin by computing relations for the other coordinates 


r6 := relllcoord([ N[900][1], N[900][7]], 1200, 6) ;
s6 := [ r6[i]*u^(6-i) : i in [1..6] ] cat [ r6[7]*v] ;
s6 := &+s6 ;

// from the approximation we guess that the 8th coordinate is 1 - we'll verify this later //

r8 := relllcoord([ N[900][1], N[900][9]], 1200, 6) ;
s8 := [ r8[i]*u^(6-i) : i in [1..6] ] cat [ r8[7]*v] ;
s8 := &+s8 ;

r9 := relllcoord([ N[900][1], N[900][10]], 1200, 6) ;
s9 := [ r9[i]*u^(6-i) : i in [1..6] ] cat [ r9[7]*v] ;
s9 := &+s9 ;


Sp := SplittingField(t) ;
RR := Roots(t,Sp) ;
RR := [ a[1] : a in RR];

rels := [s1, s2, s3, s4, s5, s6, s8, s9] ;

c1 := MonomialCoefficient(s1, v) ;
s1 := s1 - c1*v ;
s1 := (-1/c1)*s1;


c2 := MonomialCoefficient(s2, v) ;
s2 := s2 - c2*v ;
s2 := (-1/c2)*s2;

c3 := MonomialCoefficient(s3, v) ;
s3 := s3 - c3*v ;
s3 := (-1/c3)*s3;

c4 := MonomialCoefficient(s4, v) ;
s4 := s4 - c4*v ;
s4 := (-1/c4)*s4;


c5 := MonomialCoefficient(s5, v) ;
s5 := s5 - c5*v ;
s5 := (-1/c5)*s5;

c6 := MonomialCoefficient(s6, v) ;
s6 := s6 - c6*v ;
s6 := (-1/c6)*s6;


c8 := MonomialCoefficient(s8, v) ;
s8 := s8 - c8*v ;
s8 := (-1/c8)*s8;

c9 := MonomialCoefficient(s9, v) ;
s9 := s9 - c9*v ;
s9 := (-1/c9)*s9;

Evs := [ [a] cat [ Evaluate(e,[a,1]) :e in [s1,s2,s3,s4,s5,s6]] cat [1] cat [ Evaluate(e,[a,1]) : e in [s8,s9]] : a in RR];

Evs2 := [ [Evaluate(e,rr) : e in CE]  : rr in Evs] ;

assert Evs2 eq [ [0 : i in [1..10]  ]: i in [1..6]] ;

// thus  t, s1, s2, s3, s4, s5 give one orbit of 3 torsion points //

// we compute a second orbit //

a1  := AP[2] ;

a1 := [ CC ! b : b in a1 ];
N := [a1] ;


// we perform 900 steps of NR //


for i in [2..900] do ;
a := N[i-1] ;
a := [ CC ! b : b in a] ;
N[i] := nr(a) ;
end for ;

// we compute the minimal polynomial of the first coordinate //

m1 :=  lllcoord(N[900][1],1200,8) ;
Zy<y> := PolynomialRing(Integers()) ;

t := &+[ m1[i]*y^(9-i) : i in [1..9] ] ;

// from the complex approximation we guess that the second coordinate is -1,  the 4th coordinate is 3, the 6th coordinate is 1, and we compute relations for the rest 


r2 := relllcoord([ N[900][1], N[900][3]], 1200, 8) ;

Zuv<u,v> := PolynomialRing(Rationals(),2) ;
s2 := [ r2[i]*u^(8-i) : i in [1..8] ] cat [ r2[9]*v] ;
s2 := &+s2 ;

r4 := relllcoord([ N[900][1], N[900][5]], 1200, 8) ;
s4 := [ r4[i]*u^(8-i) : i in [1..8] ] cat [ r4[9]*v] ;
s4 := &+s4 ;

// we verify that these define points on our scheme //

// from the approximation we guess that the 8th coordinate is -1, the 9th coordinate is 0 //
// we compute relations for the others 

r6 := relllcoord([ N[900][1], N[900][7]], 1200, 8) ;

s6 := [ r6[i]*u^(8-i) : i in [1..8] ] cat [ r6[9]*v] ;
s6 := &+s6 ;

r9 := relllcoord([ N[900][1], N[900][10]], 1200, 8) ;
s9 := [ r9[i]*u^(8-i) : i in [1..8] ] cat [ r9[9]*v] ;
s9 := &+s9 ;



c2 := MonomialCoefficient(s2, v) ;
s2 := s2 - c2*v ;
s2 := (-1/c2)*s2;

c4 := MonomialCoefficient(s4, v) ;
s4 := s4 - c4*v ;
s4 := (-1/c4)*s4;


c6 := MonomialCoefficient(s6, v) ;
s6 := s6 - c6*v ;
s6 := (-1/c6)*s6;

c9 := MonomialCoefficient(s9, v) ;
s9 := s9 - c9*v ;
s9 := (-1/c9)*s9;


Sp := SplittingField(t) ;
RR := Roots(t,Sp) ;
RR := [ a[1] : a in RR];


Evs := [ [a] cat [-1, Evaluate(s2, [a,1]), 3, Evaluate(s4, [a,1]), 1, Evaluate(s6,[a,1]), -1,0, Evaluate(s9, [a,1])] : a in RR];

Evs2 := [ [Evaluate(e,rr) : e in CE]  : rr in Evs] ;

assert Evs2 eq [ [0 : i in [1..10]  ]: i in [1..8]] ;


// thus t, -1, s2, 3, s4,1 define a orbit of 3 torsion points //


// we compute another orbit of 3 torsion points 


a1  := AP[3] ;

a1 := [ CC ! b : b in a1 ];
N := [a1] ;


// we perform 900 steps of NR //

for i in [2..900] do ;
a := N[i-1] ;
a := [ CC ! b : b in a] ;
N[i] := nr(a) ;
end for ;

// we compute the minimal polynomial of the first coordinate //

m1 :=  lllcoord(N[900][1],1200,6) ;
Zy<y> := PolynomialRing(Integers()) ;

t := &+[ m1[i]*y^(7-i) : i in [1..7] ] ;

// we compute  coefficient relations 



Zuv<u,v> := PolynomialRing(Rationals(),2) ;

r1 := relllcoord([N[900][1], N[900][2]], 1200, 6) ;
s1 := [ r1[i]*u^(6-i) : i in [1..6] ] cat [ r1[7]*v] ;
s1 := &+s1 ;


r2 := relllcoord([N[900][1], N[900][3]], 1200, 6) ;
s2 := [ r2[i]*u^(6-i) : i in [1..6] ] cat [ r2[7]*v] ;
s2 := &+s2 ;


r3 := relllcoord([ N[900][1], N[900][4]], 1200, 6) ;
s3 := [ r3[i]*u^(6-i) : i in [1..6] ] cat [ r3[7]*v] ;
s3 := &+s3 ;

r4 := relllcoord([ N[900][1], N[900][5]], 1200, 6) ;
s4 := [ r4[i]*u^(6-i) : i in [1..6] ] cat [ r4[7]*v] ;
s4 := &+s4 ;


r5 := relllcoord([ N[900][1], N[900][6]], 1200, 6) ;
s5 := [ r5[i]*u^(6-i) : i in [1..6] ] cat [ r5[7]*v] ;
s5 := &+s5 ;


// we verify that the above define points on our scheme 

// we begin my computing the remaining relations amongst the coefficients 


r6 := relllcoord([ N[900][1], N[900][7]], 1200, 6) ;
s6 := [ r6[i]*u^(6-i) : i in [1..6] ] cat [ r6[7]*v] ;
s6 := &+s6 ;

r7 := relllcoord([ N[900][1], N[900][8]], 1200, 6) ;
s7 := [ r7[i]*u^(6-i) : i in [1..6] ] cat [ r7[7]*v] ;
s7 := &+s7 ;

r8 := relllcoord([ N[900][1], N[900][9]], 1200, 6) ;
s8 := [ r8[i]*u^(6-i) : i in [1..6] ] cat [ r8[7]*v] ;
s8 := &+s8 ;

r9 := relllcoord([ N[900][1], N[900][10]], 1200, 6) ;
s9 := [ r9[i]*u^(6-i) : i in [1..6] ] cat [ r9[7]*v] ;
s9 := &+s9 ;




Sp := SplittingField(t) ;
RR := Roots(t,Sp) ;
RR := [ a[1] : a in RR];

rels := [s1, s2, s3, s4, s5, s6, s8, s9] ;

c1 := MonomialCoefficient(s1, v) ;
s1 := s1 - c1*v ;
s1 := (-1/c1)*s1;


c2 := MonomialCoefficient(s2, v) ;
s2 := s2 - c2*v ;
s2 := (-1/c2)*s2;

c3 := MonomialCoefficient(s3, v) ;
s3 := s3 - c3*v ;
s3 := (-1/c3)*s3;

c4 := MonomialCoefficient(s4, v) ;
s4 := s4 - c4*v ;
s4 := (-1/c4)*s4;


c5 := MonomialCoefficient(s5, v) ;
s5 := s5 - c5*v ;
s5 := (-1/c5)*s5;

c6 := MonomialCoefficient(s6, v) ;
s6 := s6 - c6*v ;
s6 := (-1/c6)*s6;

c7 := MonomialCoefficient(s7, v) ;
s7 := s7 - c7*v ;
s7 := (-1/c7)*s7;


c8 := MonomialCoefficient(s8, v) ;
s8 := s8 - c8*v ;
s8 := (-1/c8)*s8;

c9 := MonomialCoefficient(s9, v) ;
s9 := s9 - c9*v ;
s9 := (-1/c9)*s9;

Evs := [ [a] cat [ Evaluate(e,[a,1]) :e in [s1,s2,s3,s4,s5,s6, s7, s8, s9]] : a in RR];

Evs2 := [ [Evaluate(e,rr) : e in CE]  : rr in Evs] ;

assert Evs2 eq [ [0 : i in [1..10]  ]: i in [1..6]] ;

// thus t, s1, s2, s3, s4, s5 defines an orbit of 3 torsion points 
