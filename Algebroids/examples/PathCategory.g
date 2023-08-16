LoadPackage( "Algebroids" );

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

SizeScreen( [ 3000, 3000 ] );

K := HomalgFieldOfRationals( );
q := CreateCapQuiver( "q(0,1,2,3,4,5)[x:0->0,s:0->1,a:1->2,c:1->3,e:1->4,b:2->4,d:3->4,t:4->5,y:5->5]" : colors := true );

C := PathCategory( q );

qC := QuotientCategory( C, [ [ C.x^5, C.x ], [ C.y^5, C.y ] ] );
KqC := K[qC];
#qKqC := QuotientCategory( KqC, [ KqC.bt ] );

