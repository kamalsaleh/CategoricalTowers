# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations depending on the Algebroids package
#

## Hom(-,k): PreSheaves( B ) → CoPreSheaves( B )
InstallMethodForCompilerForCAP( NakayamaLeftAdjointData,
        "for a copresheaf category of a f.p. algebroid with a Hom-structure",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsCoPreSheafCategory ],
        
  function ( B, coPSh )
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, IsIdenticalObj( Source( coPSh ), B ) );
    
    return NAKAYAMA_LEFT_ADJOINT_DATA_FOR_COPRESHEAF_CATEGORY_OF_ALGEBROID_WITH_HOM_STRUCTURE( coPSh );
    
end );

##
InstallMethod( NakayamaLeftAdjoint,
        "for a f.p. algebroid with a Hom-structure",
        [ IsFpAlgebroidDefinedByQuiverAlgebra and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    
    return NakayamaLeftAdjoint( PreSheaves( B ), CoPreSheaves( B ) );
    
end );

## Hom(-,k): CoPreSheaves( B ) → PreSheaves( B )
InstallMethodForCompilerForCAP( NakayamaRightAdjointData,
        "for a category of presheaves a f.p. algebroid with a Hom-structure",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsPreSheafCategory ],
        
  function ( B, PSh )
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, IsIdenticalObj( Source( PSh ), B ) );
    
    return NAKAYAMA_RIGHT_ADJOINT_DATA_FOR_PRESHEAF_CATEGORY_OF_ALGEBROID_WITH_HOM_STRUCTURE( PSh );
    
end );

##
InstallMethod( NakayamaRightAdjoint,
        "for a f.p. algebroid with a Hom-structure",
        [ IsFpAlgebroidDefinedByQuiverAlgebra and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    
    return NakayamaRightAdjoint( CoPreSheaves( B ), PreSheaves( B ) );
    
end );
