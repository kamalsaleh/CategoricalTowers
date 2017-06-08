#! @System Hom

LoadPackage( "FunctorCategories" );

#! @Example
q := RightQuiver( "q(1)[t:1->1]" );
#! q(1)[t:1->1]
Q := HomalgFieldOfRationals( );
#! Q
Qq := PathAlgebra( Q, q );
#! Q * q
B := Algebroid( Qq, [ Qq.t^3 - Qq.1 ] );
#! Algebra generated by the right quiver q(1)[t:1->1]
RelationsOfAlgebroid( B );
#! [ (1)-[1*(t*t*t) - 1*(1)]->(1) ]
counit := rec( t := 1 );
#! rec( t := 1 )
B2 := B^2;
#! Algebra generated by the right quiver qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]
comult := rec( t := PreCompose( B2.tx1, B2.1xt ) );
#! rec( t := (1x1)-[{ 1*(1xt*tx1) }]->(1x1) )
AddBialgebroidStructure( B, counit, comult );
#! Bialgebra generated by the right quiver q(1)[t:1->1]
counit := Counit( B );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Algebra generated by
#! the right quiver *(1)[]
ApplyFunctor( counit, B.1 );
#! (1)
ApplyFunctor( counit, B.t );
#! (1)-[1*(1)]->(1)
comult := Comultiplication( B );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Algebra generated by
#! the right quiver qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]
ApplyFunctor( comult, B.1 );
#! (1x1)
ApplyFunctor( comult, B.t );
#! (1x1)-[{ 1*(1xt*tx1) }]->(1x1)
LoadPackage( "LinearAlgebraForCAP" );
#! true
A := MatrixCategory( Q );
#! Category of matrices over Q
H := Hom( B, A );
#! The category of functors from Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Category of matrices over Q
z := ZeroObject( H );
#! <A zero object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
z( B.1 );
#! <A vector space object over Q of dimension 0>
z( B.t );
#! <A zero, isomorphism in Category of matrices over Q>
idz := IdentityMorphism( z );
#! <A zero, identity morphism in The category of functors from Bialgebra
#!  generated by the right quiver q(1)[t:1->1] -> Category of matrices over Q>
idz( B.1 );
#! <A zero, identity morphism in Category of matrices over Q>
DirectSum( z, z );
#! <A zero object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
phi := HomalgMatrix( [ 0, 1, 0,  0, 0, 1,  1, 0, 0 ], 3, 3, Q );
#! <A 3 x 3 matrix over an internal ring>
V := VectorSpaceObject( 3, Q );
#! <A vector space object over Q of dimension 3>
V := rec( 1 := V, t := VectorSpaceMorphism( V, phi, V ) );
#! rec( 1 := <A vector space object over Q of dimension 3>,
#!      t := <A morphism in Category of matrices over Q> )
V := AsObjectInHomCategory( B, V );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( V );
#! true
V( B.1 );
#! <A vector space object over Q of dimension 3>
V( B.t );
#! <A morphism in Category of matrices over Q>
Display( V( B.t ) );
#! [ [  0,  1,  0 ],
#!   [  0,  0,  1 ],
#!   [  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
IsZero( V );
#! false
W := DirectSum( V, V );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
W( B.1 );
#! <A vector space object over Q of dimension 6>
W( B.t );
#! <A morphism in Category of matrices over Q>
Display( W( B.t ) );
#! [ [  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
pi1 := ProjectionInFactorOfDirectSum( [ V, V ], 1 );
#! <A morphism in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
pi1 = -pi1;
#! false
pi1( B.1 );
#! <A morphism in Category of matrices over Q>
Display( pi1( B.1 ) );
#! [ [  1,  0,  0 ],
#!   [  0,  1,  0 ],
#!   [  0,  0,  1 ],
#!   [  0,  0,  0 ],
#!   [  0,  0,  0 ],
#!   [  0,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
IsWellDefined( pi1 );
#! true
IsEpimorphism( pi1 );
#! true
IsMonomorphism( pi1 );
#! false
V1 := KernelObject( pi1 );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( V1 );
#! true
V1 = V;
#! true
pi2 := ProjectionInFactorOfDirectSum( [ V, V ], 2 );
#! <A morphism in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
pi1 = pi2;
#! false
psi := HomalgMatrix( [ 0, 1,  -1, -1 ], 2, 2, Q );
#! <A 2 x 2 matrix over an internal ring>
U := VectorSpaceObject( 2, Q );
#! <A vector space object over Q of dimension 2>
U := rec( 1 := U, t := VectorSpaceMorphism( U, psi, U ) );
#! rec( 1 := <A vector space object over Q of dimension 2>,
#!      t := <A morphism in Category of matrices over Q> )
U := CapFunctor( B, U );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Category of matrices over Q
U := AsObjectInHomCategory( U );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( U );
#! true
U( B.1 );
#! <A vector space object over Q of dimension 2>
U( B.t );
#! <A morphism in Category of matrices over Q>
Display( U( B.t ) );
#! [ [   0,   1 ],
#!   [  -1,  -1 ] ]
#! 
#! A morphism in Category of matrices over Q
IsZero( U );
#! false
eta := HomalgMatrix( [ 1, 0,  0, 1,  -1, -1 ], 3, 2, Q );
#! <A 3 x 2 matrix over an internal ring>
eta := rec( 1 := VectorSpaceMorphism( V( B.1 ), eta, U( B.1 ) ) );
#! rec( 1 := <A morphism in Category of matrices over Q> )
eta := NaturalTransformation( eta,
               UnderlyingCapTwoCategoryCell( V ),
               UnderlyingCapTwoCategoryCell( U ) );
#! Natural transformation from Functor from finitely presented Bialgebra
#! generated by the right quiver q(1)[t:1->1] -> Category of matrices
#! over Q -> Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Category of matrices over Q
eta := AsMorphismInHomCategory( H, eta );
#! <A morphism in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( eta );
#! true
eta( B.1 );
#! <A morphism in Category of matrices over Q>
Display( eta( B.1 ) );
#! [ [   1,   0 ],
#!   [   0,   1 ],
#!   [  -1,  -1 ] ]
#! 
#! A morphism in Category of matrices over Q
IsEpimorphism( eta );
#! true
IsMonomorphism( eta );
#! false
K := KernelObject( eta );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
K( B.1 );
#! <A vector space object over Q of dimension 1>
K( B.t );
#! <A morphism in Category of matrices over Q>
Display( K( B.t ) );
#! [ [  1 ] ]
#! 
#! A morphism in Category of matrices over Q
I := TensorUnit( H );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
I( B.1 );
#! <A vector space object over Q of dimension 1>
I( B.t );
#! <A morphism in Category of matrices over Q>
Display( I( B.t ) );
#! [ [  1 ] ]
#! 
#! A morphism in Category of matrices over Q
I = K;
#! true
VV := TensorProductOnObjects( V, V );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
VV( B.1 );
#! <A vector space object over Q of dimension 9>
VV( B.t );
#! <A morphism in Category of matrices over Q>
Display( VV( B.t ) );
#! [ [  0,  0,  0,  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0,  0,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
Vs := DualOnObjects( V );
#! <An object in The category of functors from Bialgebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
Vs( B.1 );
#! <A vector space object over Q of dimension 3>
Vs( B.t );
#! <A morphism in Category of matrices over Q>
Display( Vs( B.t ) );
#! [ [  0,  0,  1 ],
#!   [  1,  0,  0 ],
#!   [  0,  1,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
InternalHomOnObjects( V, V ) = TensorProductOnObjects( Vs, V );
#! true
InternalHomOnObjects( V, V ) = TensorProductOnObjects( V, Vs );
#! false
#! @EndExample
