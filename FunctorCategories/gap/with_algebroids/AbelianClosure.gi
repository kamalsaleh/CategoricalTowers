




##
InstallMethodWithCache( AbelianClosure,
        "for an algebroid defined by quiver algebra",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, FilterIntersection( IsCapCategory, IsAbCategory ) ],
        
    ABELIAN_CLOSURE_OF_ALGEBROID );

##
InstallMethod( AbelianClosure,
        "for a CAP category",
        [ FilterIntersection( IsFpAlgebroidDefinedByQuiverAlgebra, HasRangeCategoryOfHomomorphismStructure ) ],
        
  function( algebroid )
    
    return AbelianClosure( algebroid, RangeCategoryOfHomomorphismStructure( algebroid ) );
    
end );
