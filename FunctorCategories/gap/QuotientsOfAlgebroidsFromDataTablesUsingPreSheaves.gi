# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#

#
#  Interpret an algebroid defined by data tables A as an object in PreSheaves(A^op ⊗ A, k-rows).
#
#  For two morphims: g: X --> Y in A^op   &  f: U --> V in A
#
#  we send the following diagram in A^op ⊗ A
#                     _
#          _          X⊗f         _
#          X⊗U  ---------------≻  X⊗V
#      _    |                      |  _
#      g⊗U  |                      |  g⊗V
#           |         _            |
#          _⋎         Y⊗f         _⋎
#          Y⊗U  ---------------≻  Y⊗V
#
#  to the diagram in k-rows:
#
#                     hom(f,X)
#         hom(U,X)  ≺----------  hom(V,X)
#           ⋏                      ⋏
#           |                      |
# hom(U,g)  |                      |  hom(V,g)
#           |         hom(f,Y)     |
#         hom(U,Y)  ≺----------  hom(V,Y)
#
##
InstallOtherMethod( AlgebroidAsObjectInPreSheavesCategory,
          [ IsPreSheafCategory, IsFpAlgebroidFromDataTables ],
          
  function ( PSh, A )
    local q, nr_objs, nr_gmors, images_of_objs, images_of_gmorphisms;
    
    q := UnderlyingQuiver( A );
    
    nr_objs := NumberOfObjects( q );
    nr_gmors := NumberOfMorphisms( q );
    
    images_of_objs :=
      _ConcatenationLazyHLists_( LazyHList( [ 1 .. nr_objs ],
          l -> LazyHList( [ 1 .. nr_objs ],
            r -> HomomorphismStructureOnObjects( A, SetOfObjects( A )[r], SetOfObjects( A )[l] ) ) ) );
    
    images_of_gmorphisms :=
      _ConcatenationLazyHLists_(
           [ _ConcatenationLazyHLists_( LazyHList( [ 1 .. nr_objs ], l -> LazyHList( [ 1 .. nr_gmors ],
              r -> HomomorphismStructureOnMorphisms( A, SetOfGeneratingMorphisms( A )[r], IdentityMorphism( SetOfObjects( A )[l] ) ) ) ) ),
             _ConcatenationLazyHLists_( LazyHList( [ 1 .. nr_gmors ], l -> LazyHList( [ 1 .. nr_objs ],
              r -> HomomorphismStructureOnMorphisms( A, IdentityMorphism( SetOfObjects( A )[r] ), SetOfGeneratingMorphisms( A )[l] ) ) ) ) ] );
    
    return ObjectConstructor( PSh, Pair( images_of_objs, images_of_gmorphisms ) );
    
end );

##
InstallMethod( AlgebroidAsObjectInPreSheavesCategory,
          [ IsFpAlgebroidFromDataTables ],
  function ( A )
    local PSh;
    
    PSh := PreSheaves( TensorProductOfAlgebroids( OppositeOfObjectFiniteCategory( A ), A ) );
    
    return CallFuncListAtRuntime( AlgebroidAsObjectInPreSheavesCategory, [ PSh, A ] );
    
end );

##
InstallOtherMethod( AssociatedMorphismIntoAlgebroidAsObjectInPreSheavesCategory,
          [ IsPreSheafCategory, IsMorphismInFpAlgebroidFromDataTables ],
          
  function ( PSh, m )
    local A, A_op, A_op_objs;
    
    A := CapCategory( m );
    A_op := Source( PSh );
    
    A_op_objs := SetOfObjects( A_op );
    
    return MorphismFromRepresentableByYonedaLemma( PSh,
                ElementaryTensor( A_op_objs[ObjectIndex( Target( m ) )], Source( m ), Source( PSh ) ),
                InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( A, m ),
                AlgebroidAsObjectInPreSheavesCategory( A ) );
    
end );

##
InstallMethod( AssociatedMorphismIntoAlgebroidAsObjectInPreSheavesCategory,
          [ IsMorphismInFpAlgebroidFromDataTables ],
          
  function ( m )
    local A, PSh;
    
    A := CapCategory( m );
    
    PSh := PreSheaves( TensorProductOfAlgebroids( OppositeOfObjectFiniteCategory( A ), A ) );
    
    return CallFuncListAtRuntime( AssociatedMorphismIntoAlgebroidAsObjectInPreSheavesCategory, [ PSh, m ] );
    
end );
