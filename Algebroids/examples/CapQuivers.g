#! @BeginChunk CapQuivers

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
LoadPackage( "Algebroids" );
#! true
str := "q(0,1,2,3,4,5)[x:0->0,s:0->1,a:1->2,c:1->3,e:1->4,b:2->4,d:3->4,t:4->5,y:5->5]";;
q := CreateCapQuiver( str );
#! Quiver( "q(0,1,2,3,4,5)[x:0-≻0,s:0-≻1,a:1-≻2,c:1-≻3,e:1-≻4,b:2-≻4,d:3-≻4,
#! t:4-≻5,y:5-≻5]" )
NumberOfObjects( q );
#! 6
LabelsOfObjects( q );
#! [ "0", "1", "2", "3", "4", "5" ]
QuiverName( q );
#! "q"
NumberOfMorphisms( q );
#! 9
LabelsOfMorphisms( q );
#! [ "x", "s", "a", "c", "e", "b", "d", "t", "y" ]
IndicesOfSources( q );
#! [ 1, 1, 2, 2, 2, 3, 4, 5, 6 ]
IndicesOfTargets( q );
#! [ 1, 2, 3, 4, 5, 5, 5, 6, 6 ]
SetOfObjects( q );
#! [ (0), (1), (2), (3), (4), (5) ]
SetOfMorphisms( q );
#! [ x:(0) -≻ (0), s:(0) -≻ (1), a:(1) -≻ (2), c:(1) -≻ (3), e:(1) -≻ (4),
#!   b:(2) -≻ (4), d:(3) -≻ (4), t:(4) -≻ (5), y:(5) -≻ (5) ]
o := q.0;
#! (0)
ObjectIndex( o );
#! 1
ObjectLabel( o );
#! "0"
m := q.y;
#! y:(5) -≻ (5)
MorphismIndex( m );
#! 9
MorphismLabel( m );
#! "y"
#! @EndExample

