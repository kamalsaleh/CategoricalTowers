#! @Chunk HeytingAlgebraOfRadicalIdeals

#! @Example
LoadPackage( "SubcategoriesForCAP", ">= 2024.02-11", false );
#! true
Q := HomalgFieldOfRationalsInSingular( );
#! Q
R := Q["x,y"];
#! Q[x,y]
F := CategoryOfRows( R );
#! Rows( Q[x,y] )
S := SliceCategoryOverTensorUnit( F );
#! SliceCategoryOverTensorUnit( Rows( Q[x,y] ) )
P := PosetOfCategory( S );
#! PosetOfCategory( SliceCategoryOverTensorUnit( Rows( Q[x,y] ) ) )
Display( P );
#! A CAP category with name
#! PosetOfCategory( SliceCategoryOverTensorUnit( Rows( Q[x,y] ) ) ):
#! 
#! 17 primitive operations were used to derive 276 operations for this category
#! which algorithmically
#! * IsCategoryWithDecidableColifts
#! * IsCategoryWithDecidableLifts
#! * IsEquippedWithHomomorphismStructure
#! * IsSymmetricClosedMonoidalLattice
L := StablePosetOfCategory( P );
#! StablePosetOfCategory( PosetOfCategory(
#! SliceCategoryOverTensorUnit( Rows( Q[x,y] ) ) ) )
Display( L );
#! A CAP category with name
#! StablePosetOfCategory( PosetOfCategory(
#! SliceCategoryOverTensorUnit( Rows( Q[x,y] ) ) ) ):
#! 
#! 16 primitive operations were used to derive 338 operations for this category
#! which algorithmically
#! * IsCategoryWithDecidableColifts
#! * IsCategoryWithDecidableLifts
#! * IsEquippedWithHomomorphismStructure
#! * IsHeytingAlgebra
#! * IsSymmetricClosedMonoidalLattice
#! and furthermore mathematically
#! * IsStableProset
I := HomalgMatrix( "[ x ]", 1, 1, R ) / F / S / P / L;
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
J := HomalgMatrix( "[ x, y ]", 2, 1, R ) / F / S / P / L;
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IJ := TensorProduct( I, J );
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IiJ := DirectProduct( I, J );
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IsHomSetInhabited( IJ, IiJ );
#! true
IsHomSetInhabited( IiJ, IJ );
#! true
IiJ = I;
#! true
IpJ := Coproduct( I, J );
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IpJ = J;
#! true
IJqJ := InternalHom( J, IJ ); ## this is the ideal quotient IJ : J
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IJqJ = I;
#! true
iota := InternalHom( UniversalMorphismIntoTerminalObject( J ), IJ );
#! A morphism in the stable poset given by: <An epi-, monomorphism in
#! PosetOfCategory( SliceCategoryOverTensorUnit( Rows( Q[x,y] ) ) )>
IsWellDefined( iota );
#! true
IsOne( iota );
#! true
IJJ := TensorProduct( IJ, J );
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IJJqJ := InternalHom( J, IJJ );
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IJJqJ = I;
#! true
IJJsJ := StableInternalHom( J, IJJ );
#! An object in the stable poset given by:
#! An object in the poset given by:
#! An object in the slice category given by: <A morphism in Rows( Q[x,y] )>
IJJsJ = I;
#! true
#! @EndExample
