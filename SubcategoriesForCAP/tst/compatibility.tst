# SubcategoriesForCAP, single 2
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been generated by AutoDoc. It contains examples extracted from
# the package documentation. Each example is preceded by a comment which gives
# the name of a GAPDoc XML file and a line range from which the example were
# taken. Note that the XML file in turn may have been generated by AutoDoc
# from some other input.
#
gap> START_TEST("subcategoriesforcap02.tst");

# /doc/_Chunks.xml:173-188
gap> LoadPackage( "SubcategoriesForCAP", false );
true
gap> T := TerminalCategoryWithMultipleObjects( );
TerminalCategoryWithMultipleObjects( )
gap> B := TerminalObject( T );
<A zero object in TerminalCategoryWithMultipleObjects( )>
gap> S := SliceCategory( B );
A slice category of TerminalCategoryWithMultipleObjects( )
gap> obj := IdentityMorphism( B ) / S;
An object in the slice category given by: <A zero, identity morphism in Termin\
alCategoryWithMultipleObjects( )>
gap> mor := ProjectionInFactorOfDirectProduct( [ obj, obj, obj ], 3 );
A morphism in the slice category given by: <A zero, isomorphism in TerminalCat\
egoryWithMultipleObjects( )>
gap> IsWellDefinedForMorphisms( mor );
true
gap> STOP_TEST("subcategoriesforcap02.tst", 1);
