# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Finite categories from data tables

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of categories from data tables.
DeclareCategory( "IsCategoryFromDataTables",
        IsCapCategory );

#! @Description
#!  The &GAP; category of cells in a category from data tables.
DeclareCategory( "IsCellInCategoryFromDataTables",
        IsCapCategoryCell );

#! @Description
#!  The &GAP; category of objects in a category from data tables.
DeclareCategory( "IsObjectInCategoryFromDataTables",
        IsCellInCategoryFromDataTables and IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in a category from data tables.
DeclareCategory( "IsMorphismInCategoryFromDataTables",
        IsCellInCategoryFromDataTables and IsCapCategoryMorphism );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The data tables used to create the category <A>C</A>.
#! @Arguments C
#! @Returns a pair of lists
DeclareAttribute( "DataTablesOfCategory",
        IsCategoryFromDataTables );

CapJitAddTypeSignature( "DataTablesOfCategory", [ IsCategoryFromDataTables ],
  function ( input_types )
    local V;
    
    V := RangeCategoryOfHomomorphismStructure( input_types[1].category );
    
    return rec( filter := IsNTuple,
                element_types :=
                [ rec( filter := IsNTuple,
                       element_types :=
                       [ # C0
                         CapJitDataTypeOfObjectOfCategory( V ),
                         # C1
                         CapJitDataTypeOfObjectOfCategory( V ) ] ),
                  rec( filter := IsNTuple,
                       element_types :=
                       [ # identity
                         rec( filter := IsList,
                              element_type := rec( filter := IsInt ) ),
                         # s
                         CapJitDataTypeOfMorphismOfCategory( V ),
                         # t
                         CapJitDataTypeOfMorphismOfCategory( V ),
                         # precompose
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type := rec( filter := IsInt ) ) ),
                         # hom_on_objs
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type := CapJitDataTypeOfObjectOfCategory( V ) ) ),
                         # hom_on_mors
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type := CapJitDataTypeOfMorphismOfCategory( V ) ) ),
                         # introduction
                         rec( filter := IsList,
                              element_type := CapJitDataTypeOfMorphismOfCategory( V ) ),
                         # elimination
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type :=
                                   rec( filter := IsList,
                                        element_type := rec( filter := IsInt ) ) ) ) ] )
                  ] );
    
end );

#! @Description
#!  The finite set of objects of the category <A>C</A> created from data tables.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfObjects",
        IsCategoryFromDataTables );

CapJitAddTypeSignature( "SetOfObjects", [ IsCategoryFromDataTables ],
  function ( input_types )
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfObjectOfCategory( input_types[1].category ) );
    
end );

DeclareAttribute( "SetOfMorphisms",
        IsCategoryFromDataTables );

CapJitAddTypeSignature( "SetOfMorphisms", [ IsCategoryFromDataTables ],
  function ( input_types )
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfMorphismOfCategory( input_types[1].category ) );
    
end );

#! @Description
#!  The finite set of morphisms generating the category <A>C</A> created from data tables.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfGeneratingMorphisms",
        IsCategoryFromDataTables );

CapJitAddTypeSignature( "SetOfGeneratingMorphisms", [ IsCategoryFromDataTables ],
  function ( input_types )
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfMorphismOfCategory( input_types[1].category ) );
    
end );

##
DeclareAttribute( "MapOfObject",
        IsObjectInCategoryFromDataTables );

CapJitAddTypeSignature( "MapOfObject", [ IsObjectInCategoryFromDataTables ],
  function ( input_types )
    local V;
    
    Assert( 0, IsCategoryFromDataTables( input_types[1].category ) );
    
    V := RangeCategoryOfHomomorphismStructure( input_types[1].category );
    
    return CapJitDataTypeOfMorphismOfCategory( V );
    
end );

##
DeclareAttribute( "MapOfMorphism",
        IsMorphismInCategoryFromDataTables );

CapJitAddTypeSignature( "MapOfMorphism", [ IsMorphismInCategoryFromDataTables ],
  function ( input_types )
    local V;
    
    Assert( 0, IsCategoryFromDataTables( input_types[1].category ) );
    
    V := RangeCategoryOfHomomorphismStructure( input_types[1].category );
    
    return CapJitDataTypeOfMorphismOfCategory( V );
    
end );

####################################
#
#! @Section Constructors
#
####################################

#! @Description
#!  Construct a category with name <A>str</A> from the given <A>data_tables</A>.
#! @Arguments str, data_tables, indices_of_generating_morphisms, labels
#! @Returns a &CAP; category
DeclareOperation( "CategoryFromDataTables",
        [ IsString, IsList, IsList, IsList ] );
#! @InsertChunk CategoryFromDataTables

#! @Description
#!  Construct the <A>o</A>-th object in the category <A>C</A> created from data tables.
#! @Arguments C, o
#! @Returns a &CAP; category
DeclareOperation( "CreateObject",
        [ IsCategoryFromDataTables, IsInt ] );

#! @Description
#!  Construct the <A>m</A>-th morphism <A>source</A>$\to$<A>range</A>
#!  in the category <A>C</A> created from data tables.
#! @Arguments C, m
#! @Returns a &CAP; category
#! @Group CreateMorphism
DeclareOperation( "CreateMorphism",
        [ IsCategoryFromDataTables, IsInt ] );

#! @Arguments source, m, range
#! @Group CreateMorphism
DeclareOperation( "CreateMorphism",
        [ IsObjectInCategoryFromDataTables, IsInt, IsObjectInCategoryFromDataTables ] );
