#
# Bialgebroids: Bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Bialgebroids as preadditive categories generated by enhanced quivers

# our info class:
DeclareInfoClass( "InfoBialgebroids" );
SetInfoLevel( InfoBialgebroids, 1 );

####################################
#
#! @Section Categories
#
####################################

#! @Description
#!  The &GAP; category of objects in an algebroid.
DeclareCategory( "IsCapCategoryObjectInAlgebroid",
        IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in an algebroid.
DeclareCategory( "IsCapCategoryMorphismInAlgebroid",
        IsCapCategoryMorphism );

####################################
#
#! @Section Technical stuff
#
####################################

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The quiver underlying the algebroid <A>A</A>.
#! @Arguments A
#! @Returns a &QPA; quiver
DeclareAttribute( "UnderlyingQuiver",
        IsCapCategory );

#! @Description
#!  The quiver algebra (=path algebra with relations) underlying the algebroid <A>A</A>.
#! @Arguments A
#! @Returns a &QPA; path algebra
DeclareAttribute( "UnderlyingQuiverAlgebra",
        IsCapCategory );

#! @Description
#!  The vertex of the quiver underlying the object <A>obj</A> in an algebroid.
#! @Arguments obj
#! @Returns a vertex in a &QPA; quiver
DeclareAttribute( "UnderlyingVertex",
        IsCapCategoryObjectInAlgebroid );

#! @Description
#!  The quiver algebra element underlying the morphism <A>mor</A> in an algebroid.
#! @Arguments mor
#! @Returns an element in a &QPA; path algebra
DeclareAttribute( "UnderlyingQuiverAlgebraElement",
        IsCapCategoryMorphismInAlgebroid );

####################################
#
#! @Section Constructors
#
####################################

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_ALGEBROID" );

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_BIALGEBROID" );

DeclareOperation( "Algebroid_NonFinalized",
        [ IsHomalgRing, IsQuiver ] );

#! @Description
#!  Construct the algebroid generated by the quiver <A>q</A> as an <A>R</A>-linear category.
#! @Arguments R, q
#! @Returns a &CAP; category
DeclareOperation( "Algebroid",
        [ IsHomalgRing, IsQuiver ] );

#! @Description
#!  Construct the bialgebroid generated by the quiver <A>q</A> as an <A>R</A>-linear category.
#! @Arguments R, q
#! @Returns a &CAP; category
DeclareOperation( "Bialgebroid",
        [ IsHomalgRing, IsQuiver ] );

#! @Description
#!  The constructor of morphisms in an algebroid given the source <A>S</A>, the target <A>T</A>,
#!  and the underlying quiver algebra element <A>path</A>.
#! @Arguments S, path, T
#! @Returns a morphism in a &CAP; category
DeclareOperation( "MorphismInAlgebroid",
        [ IsCapCategoryObjectInAlgebroid, IsQuiverAlgebraElement, IsCapCategoryObjectInAlgebroid ] );
