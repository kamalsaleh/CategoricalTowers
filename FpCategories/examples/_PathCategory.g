#! @BeginChunk TensorProductOfPathCategoriesAndTheirQuotients

#! @Example
LoadPackage( "FpCategories", false );

q1 := FinQuiver( "q1(0,1,2)[x1:0->1,x2:0->1,y1:1->2,y2:1->2]" );
q2 := FinQuiver( "q2(0,1)[m:0->1,n:0->1]" );

P1 := PathCategory( q1 );
P2 := PathCategory( q2 );
T := TensorProductOfPathCategories( P1, P2 );
U := UnderlyingCategory( T ) / DefiningRelations( T );
t := MorphismsOfExternalHom( First( SetOfObjects( T ) ), Last( SetOfObjects( T ) ) );
u := MorphismsOfExternalHom( First( SetOfObjects( U ) ), Last( SetOfObjects( U ) ) );
Assert( 0, List( t, x -> MorphismIndices( CanonicalRepresentative( x ) ) ) = List( u, x -> MorphismIndices( CanonicalRepresentative( x ) ) ) );

P1 := PathCategory( q1 : admissible_order := "Dp" );
P2 := PathCategory( q2 : admissible_order := "Dp" );
T := TensorProductOfPathCategories( P1, P2 );
U := UnderlyingCategory( T ) / DefiningRelations( T );
t := MorphismsOfExternalHom( First( SetOfObjects( T ) ), Last( SetOfObjects( T ) ) );
u := MorphismsOfExternalHom( First( SetOfObjects( U ) ), Last( SetOfObjects( U ) ) );
Assert( 0, List( t, x -> MorphismIndices( CanonicalRepresentative( x ) ) ) = List( u, x -> MorphismIndices( CanonicalRepresentative( x ) ) ) );

q3 := FinQuiver( "q3(0..2)[l:0->0,x:0->1,y:1->2,s:2->2]" );
P3 := PathCategory( q3 );
C3 := P3 / [ [ P3.l^4, P3.l ], [ P3.s^4, P3.s^2 ] ];

q4 := FinQuiver( "q4(0,1)[a:0->1,b:1->1]" );
P4 := PathCategory( q4 );
C4 := P4 / [ [ P4.b^3, P4.b ] ];
#! @EndExample

