#! @BeginChunk NerveTruncatedInDegree2

LoadPackage( "FunctorCategories", false );

#! We compute the nerve of the full subcategory of the simplicial category $\Delta$ on the objects $[0], [1], [2]$.

#! @Example
Delta2 := SimplicialCategoryTruncatedInDegree( 2 );
#! PathCategory( FinQuiver(
#!   "Delta(C0,C1,C2)[id:C1-≻C0,s:C0-≻C1,t:C0-≻C1,
#!                    is:C2-≻C1,it:C2-≻C1,
#!                    ps:C1-≻C2,pt:C1-≻C2,mu:C1-≻C2]" ) )
#! / [ s⋅id = id(C0), t⋅id = id(C0), ps⋅is = id(C1), ... ]
DefiningRelations( Delta2 );
#! [ [ s⋅id:(C0) -≻ (C0), id(C0):(C0) -≻ (C0) ],
#!   [ t⋅id:(C0) -≻ (C0), id(C0):(C0) -≻ (C0) ],
#!   [ ps⋅is:(C1) -≻ (C1), id(C1):(C1) -≻ (C1) ],
#!   [ pt⋅it:(C1) -≻ (C1), id(C1):(C1) -≻ (C1) ],
#!   [ is⋅id:(C2) -≻ (C0), it⋅id:(C2) -≻ (C0) ],
#!   [ pt⋅is:(C1) -≻ (C1), id⋅t:(C1) -≻ (C1) ],
#!   [ ps⋅it:(C1) -≻ (C1), id⋅s:(C1) -≻ (C1) ],
#!   [ s⋅pt:(C0) -≻ (C2), t⋅ps:(C0) -≻ (C2) ],
#!   [ s⋅mu:(C0) -≻ (C2), s⋅ps:(C0) -≻ (C2) ],
#!   [ t⋅mu:(C0) -≻ (C2), t⋅pt:(C0) -≻ (C2) ],
#!   [ mu⋅is:(C1) -≻ (C1), id(C1):(C1) -≻ (C1) ],
#!   [ mu⋅it:(C1) -≻ (C1), id(C1):(C1) -≻ (C1) ] ]
Size( Delta2 );
#! 31
N := NerveTruncatedInDegree2( Delta2 );
#! <An object in PreSheaves( PathCategory( FinQuiver(
#!   "Delta(C0,C1,C2)[id:C1-≻C0,s:C0-≻C1,t:C0-≻C1,
#!                    is:C2-≻C1,it:C2-≻C1,
#!                    ps:C1-≻C2,pt:C1-≻C2,mu:C1-≻C2]" ) )
#! / [ s⋅id = id(C0), t⋅id = id(C0), ps⋅is = id(C1), ... ],
#!  SkeletalFinSets )>
IsWellDefined( N );
#! true
N.C0;
#! |3|
Display( N.C0 );
#! { 0, 1, 2 }
N.C1;
#! |31|
Display( N.C1 );
#! { 0,..., 30 }
N.C2;
#! |393|
Display( N.C2 );
#! { 0,..., 392 }
N.id;
#! |3| → |31|
Display( N.id );
#! { 0, 1, 2 } ⱶ[ 0, 5, 21 ]→ { 0,..., 30 }
IntCat := CategoryOfInternalCategories(
                  RangeCategoryOfHomomorphismStructure( Delta2 ) );
#! FullSubcategoryByObjectMembershipFunction(
#! PreSheaves( PathCategory( FinQuiver(
#!   "Delta(C0,C1,C2)[id:C1-≻C0,s:C0-≻C1,t:C0-≻C1,
#!                    is:C2-≻C1,it:C2-≻C1,
#!                    ps:C1-≻C2,pt:C1-≻C2,mu:C1-≻C2]" ) )
#! / [ s⋅id = id(C0), t⋅id = id(C0), ps⋅is = id(C1), ... ],
#! SkeletalFinSets ), ObjectMembershipFunction )
IsWellDefined( N / IntCat );
#! true
#! @EndExample
#! @EndChunk
