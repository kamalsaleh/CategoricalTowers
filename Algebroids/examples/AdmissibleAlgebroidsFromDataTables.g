#! @BeginChunk AdmissibleAlgebroidFromDataTables
#! @Example
LoadPackage( "Algebroids" );
#! true
q := RightQuiver( "q(0,1,2)[x:0->1,y:1->2,z:0->2]" );
#! q(0,1,2)[x:0->1,y:1->2,z:0->2]
F := FreeCategory( q );
#! FreeCategory( RightQuiver( "q(0,1,2)[x:0->1,y:1->2,z:0->2]" ) )
k := HomalgFieldOfRationals( );
#! Q
kF := k[F];
#! Algebroid( Q, FreeCategory( RightQuiver( "q(0,1,2)[x:0->1,y:1->2,z:0->2]" ) ) )
A := kF / [ kF.xy - kF.z ];
#! Algebroid( Q, FreeCategory( RightQuiver( "q(0,1,2)[x:0->1,y:1->2,z:0->2]" ) ) )
#! / relations
B := AlgebroidFromDataTables( A );
#! Algebroid( Q, q(0,1,2)[x:0-≻1,y:1-≻2,z:0-≻2] ) defined by data tables on 3 objects
#! and 3 generating morphisms
IsAdmissibleAlgebroid( B );
#! false
q := RightQuiver( "q(*)[x:*->*,y:*->*]" );
#! q(*)[x:*->*,y:*->*]
F := FreeCategory( q );
#! FreeCategory( RightQuiver( "q(*)[x:*->*,y:*->*]" ) )
kF := k[F];
#! Algebra( Q, FreeCategory( RightQuiver( "q(*)[x:*->*,y:*->*]" ) ) )
A := kF / [ kF.xy - kF.yx, kF.x^3, kF.y^3 ];
#! Algebra( Q, FreeCategory( RightQuiver( "q(*)[x:*->*,y:*->*]" ) ) ) / relations
B := AlgebroidFromDataTables( A );
#! Algebroid( Q, q(*)[x:*-≻*,y:*-≻*] ) defined by data tables on 1 object and
#! 2 generating morphisms
IsAdmissibleAlgebroid( B );
#! true
A := kF / [ kF.xy - kF.yx, kF.x^3 - kF.x, kF.y^3 ];
#! Algebra( Q, FreeCategory( RightQuiver( "q(*)[x:*->*,y:*->*]" ) ) ) / relations
B := AlgebroidFromDataTables( A );
#! Algebroid( Q, q(*)[x:*-≻*,y:*-≻*] ) defined by data tables on 1 object and
#! 2 generating morphisms
IsAdmissibleAlgebroid( B );
#! false
#! @EndExample
#! @EndChunk
