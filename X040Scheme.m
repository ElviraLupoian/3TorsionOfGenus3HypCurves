// this is the magma code used to compute the set of equations whose solutions correspond to 3-torsion points of the Jacobian of X0(40)

Za<[a]> := PolynomialRing(Rationals(), 10) ;
Zx<x> := PolynomialRing(Za) ;


f := x^8 +8*x^6 - 2*x^4 + 8*x^2 + 1 ;
// we work with the model of the curve y^2 = f(x) 

l := x^2 + a[1]*x + a[2];
s := -x^6 -4*x^4 -a[1]*x^5 -a[2]*x^4 + a[3]*x^3 + a[4]*x^2 + a[5]*x + a[6] ;
e := x^3 + a[7]*x^2 + a[8]*x + a[9];
E := f*l^2 - s^2 -a[10]*e^3 ;
CE := Coefficients(E) ;

// CE are the required equations 
