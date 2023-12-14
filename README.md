# 3TorsionOfGenus3HypCurves

This is the MAGMA code used to compute the 3-torsion subgroups of the modular Jacobian J0(40), as described in https://arxiv.org/abs/2210.02225v2.


This directory contains 5 files:

X040Scheme.m - this is the MAGMA code used to derive the equations whose solutions correspond to 3-torsion points 
X040Approx.m - the some approximate solutions required to compute the 3-torsion subgroup - these are computed in Julia, using the package HomotopyContinuation.jl
generalprogs.m - this contains an implementation of Newton Raphson and some functions required to compute algebraic expressions for the 3-torsion points 
X040ThreeTorsion.m - this computes 3 orbits corresponding to 3-torsion points 
J040ThreeTorsionSubgroup.m - this verifies that the 3 orbits computed above generate the enture 3-torsion subgroup of the Jacobian 
X040wildcond3exp.m - this uses the previous file to compute the wild conductor exponent at 2.


