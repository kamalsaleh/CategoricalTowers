#! @BeginChunk PathCategory

#    x
#     ⭮
#      0
#     s ⭝   a
#        1 ----🡢 2
#        | ⭝     |
#       c|   ⭝ e |b
#        🡣     ⭝ 🡣
#        3 ----🡢 4
#            d    ⭝ t
#                  5
#                   ⭯
#                    y


#! @Example
LoadPackage( "FpCategories", false );
#! true
str :=
  "q(0..5)[x:0->0,s:0->1,a:1->2,c:1->3,e:1->4,b:2->4,d:3->4,t:4->5,y:5->5]";;
q := FinQuiver( str );
#! FinQuiver( "q(0,1,2,3,4,5)[x:0-≻0,s:0-≻1,a:1-≻2,c:1-≻3,e:1-≻4,b:2-≻4,d:3-≻4,
#! t:4-≻5,y:5-≻5]" )
C := PathCategory( q : admissible_order := "Dp" );
#! PathCategory( FinQuiver( "q(0,1,2,3,4,5)[x:0-≻0,s:0-≻1,a:1-≻2,c:1-≻3,e:1-≻4,
#! b:2-≻4,d:3-≻4,t:4-≻5,y:5-≻5]" ) )
Display( C );
#! A CAP category with name PathCategory( FinQuiver( "q(0,1,2,3,4,5)[x:0-≻0,s:0-≻1,
#! a:1-≻2,c:1-≻3,e:1-≻4,b:2-≻4,d:3-≻4,t:4-≻5,y:5-≻5]" ) ):
#!
#! 17 primitive operations were used to derive 32 operations for this category
#! which algorithmically
#! * IsFinitelyPresentedCategory
Display( SetOfObjects( C ) );
#! [ (0), (1), (2), (3), (4), (5) ]
Display( SetOfGeneratingMorphisms( C ) );
#! [ x:(0) -≻ (0), s:(0) -≻ (1), a:(1) -≻ (2), c:(1) -≻ (3), e:(1) -≻ (4),
#!   b:(2) -≻ (4), d:(3) -≻ (4), t:(4) -≻ (5), y:(5) -≻ (5) ]
"5" / C;
#! (5)
ObjectIndex( "5" / C );
#! 6
C.id_5 = "id(5)" / C;
#! true
m := "x^2*s*a*b*t*y^2" / C;
#! x^2⋅s⋅a⋅b⋅t⋅y^2:(0) -≻ (5)
m := "x^2sabty^2" / C;
#! x^2⋅s⋅a⋅b⋅t⋅y^2:(0) -≻ (5)
IsWellDefined( m );
#! true
MorphismLength( m );
#! 8
Display( MorphismIndices( m ) );
#! [ 1, 1, 2, 3, 6, 8, 9, 9 ]
Perform( MorphismSupport( m ), Display );
#! x:(0) -≻ (0)
#! x:(0) -≻ (0)
#! s:(0) -≻ (1)
#! a:(1) -≻ (2)
#! b:(2) -≻ (4)
#! t:(4) -≻ (5)
#! y:(5) -≻ (5)
#! y:(5) -≻ (5)
m = MorphismConstructor( C, Source( m ), [ MorphismLength( m ), MorphismIndices( m ) ], Target( m ) );
#! true
relations := [ [ C.x^5, C.x ], [ C.y^5, C.y^2 ] ];;
qC := QuotientCategory( C, relations );
#! PathCategory( FinQuiver( "q(0,1,2,3,4,5)[x:0-≻0,s:0-≻1,a:1-≻2,c:1-≻3,e:1-≻4,
#! b:2-≻4,d:3-≻4,t:4-≻5,y:5-≻5]" ) ) / [ x^5 = x, y^5 = y^2 ]
Display( qC );
#! A CAP category with name PathCategory( FinQuiver( "q(0,1,2,3,4,5)[x:0-≻0,s:0-≻1,
#! a:1-≻2,c:1-≻3,e:1-≻4,b:2-≻4,d:3-≻4,t:4-≻5,y:5-≻5]" ) ) / [ x^5 = x, y^5 = y^2 ]:
#!
#! 24 primitive operations were used to derive 65 operations for this category
#! which algorithmically
#! * IsCategoryWithDecidableColifts
#! * IsCategoryWithDecidableLifts
#! * IsFiniteCategory
#! * IsEquippedWithHomomorphismStructure
"0" / qC;
#! (0)
ObjectIndex( "0" / qC );
#! 1
qC.x^7;
#! [x^3]:(0) -≻ (0)
CanonicalRepresentative( qC.x^7 );
#! x^3:(0) -≻ (0)
HomomorphismStructureOnObjects( "0" / qC, "5" / qC );
#! |75|
Display( List( SetOfGeneratingMorphisms( qC ), IsMonomorphism ) );
#! [ false, true, true, true, true, true, true, true, false ]
Display( List( SetOfGeneratingMorphisms( qC ), IsEpimorphism ) );
#! [ false, true, true, true, true, true, true, true, false ]
#! @EndExample
