// this is the NR implementation to increase the precision of our computations 


nr := function
(x) ;
J0 := Evaluate(J, x) ;
H0 := Evaluate(E,x) ;
IJ0 := J0^-1 ;
HH0 := Matrix(CC, 10, 1, H0);
xx := Matrix(CC, 10, 1, x); 
nx := xx - IJ0*HH0 ;
nnx := Eltseq(nx) ;
return nnx ;
end function ;

// the following is used to compute minimal polynomials 

ll := function(x,p,d) ;
r := [] ;
for i in [1..d-1] do ;
r[i] := [] ;
for j in [1..d+1 ] do ;
if i eq j then 
r[i][j] := 1 ;
else r[i][j] := 0 ;
end if ;
end for ;
end for ;
r1 := [] ;
for i in [1..d+1] do ;
r1[i] := (10^p)*Real(x^(d+1-i)) ;
end for ;
r[d] := [ Round(a) : a in r1 ] ;
r2 := [] ;
for i in [1..d+1] do ;
r2[i] := (10^p)*Real(-CC.1*(x^(d+1-i))) ;
end for ;
r[d+1] := [ Round(a) : a in r2] ; 
return r;
end function ; 

lll := function(x,p,d) ; 
r := ll(x,p,d) ;
MM := Matrix(Integers(), d+1, d+1, r ) ;
M := Transpose(MM) ; 
L := Lattice(M) ;
v := ShortestVector(L) ;
return v ;
end function ;



lllcoord := function(x,p,d) ;
v := Eltseq(lll(x,p,d)) ;
r := ll(x,p,d) ;
r1 := r[d] ;
r2 := r[d+1] ;
a := [] ;
for i in [1..d-1] do ;
a[i] := v[i] ;
end for ;
v1 := &+[ a[i]*r2[i] : i in [1..d-1] ] ;
adC := v[d+1] - v1 ;
ad := adC/r2[d] ;
a[d] := ad; 
v2 := [ a[i]*r1[i] : i in [1..d] ] ;
vv2 := &+v2 ;
ad2C := v[d] - vv2 ;
ad2 := ad2C/r1[d+1] ;
a[d+1] := ad2 ;
return a ;
end function ;


// the following is used to compute polynomial relations 

rell := function(pt,p,d) ;
x := pt[1] ;
y := pt[2] ;
r := [] ;
for i in [1..d-1] do ;
r[i] := [] ;
for j in [1..d+1 ] do ;
if i eq j then 
r[i][j] := 1 ;
else r[i][j] := 0 ;
end if ;
end for ;
end for ;
r1 := [] ;
for i in [1..d] do ;
r1[i] := (10^p)*Real(x^(d-i)) ;
end for ;
r1[d+1] := (10^p)*Real(y) ;
r[d] := [ Round(a) : a in r1 ] ;
r2 := [] ;
for i in [1..d] do ;
r2[i] := (10^p)*Real(-CC.1*(x^(d-i))) ;
end for ;
r2[d+1] := (10^p)*Real(-CC.1*y) ;
r[d+1] := [ Round(a) : a in r2] ; 
return r;
end function ; 

relll := function(x,p,d) ; 
r := rell(x,p,d) ;
MM := Matrix(Integers(), d+1, d+1, r ) ;
M := Transpose(MM) ; 
L := Lattice(M) ;
v := ShortestVector(L) ;
return v ;
end function ;




relllcoord := function(x,p,d) ;
v := Eltseq(relll(x,p,d)) ;
r := rell(x,p,d) ;
r1 := r[d] ;
r2 := r[d+1] ;
a := [] ;
for i in [1..d-1] do ;
a[i] := v[i] ;
end for ;
v1 := &+[ a[i]*r2[i] : i in [1..d-1] ] ;
adC := v[d+1] - v1 ;
ad := adC/r2[d+1] ;
a[d+1] := ad; 
v2 := [ a[i]*r1[i] : i in [1..d-1] ] cat [ a[d+1]*r1[d+1] ]  ;
vv2 := &+v2 ;
ad2C := v[d] - vv2 ;
ad2 := ad2C/r1[d] ;
a[d] := ad2 ;
return a ;
end function ;


// this computes the minimal polynomial when the  imaginary part of the approximation is very small and we are probably approximating a real number 

ll1 := function(x,p,d) ;
r := [] ;
for i in [1..d] do ;
r[i] := [] ;
for j in [1..d+1 ] do ;
if i eq j then 
r[i][j] := 1 ;
else r[i][j] := 0 ;
end if ;
end for ;
end for ;
r1 := [] ;
for i in [1..d+1] do ;
r1[i] := (10^p)*(x^(d+1-i)) ;
end for ;
r[d+1] := [ Round(a) : a in r1 ] ;
return r;
end function ; 

lll1 := function(x,p,d) ; 
r := ll1(x,p,d) ;
MM := Matrix(Integers(), d+1, d+1, r ) ;
M := Transpose(MM) ; 
L := Lattice(M) ;
v := ShortestVector(L) ;
return v ;
end function ;




lll1coord := function(x,p,d) ;
v := Eltseq(lll1(x,p,d)) ;
r := ll1(x,p,d) ;
r2 := r[d+1] ;
a := [] ;
for i in [1..d] do ;
a[i] := v[i] ;
end for ;
v1 := &+[ a[i]*r2[i] : i in [1..d] ] ;
adC := v[d+1] - v1 ;
ad := adC/r2[d+1] ;
a[d+1] := ad; 
return a ;
end function ;


