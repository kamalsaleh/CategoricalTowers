



##
InstallMethod( CreateCoPreSheaf,
        "for a copresheaf category and two lists",
        [ IsCoPreSheafCategory and HasRangeCategoryOfHomomorphismStructure, IsList, IsList ],
        
  function ( coPSh, dims, matrices )
    local kmat, objects, morphisms, k, mat;
    
    if dims = [ ] then
        Error( "the list of dimensions is empty\n" );
    elif not IsInt( dims[1] ) then
        Error( "expecting a list of integers as the second argument but received ", dims, "\n" );
    fi;
    
    kmat := RangeCategoryOfHomomorphismStructure( coPSh );
        
    if not ( IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) ) then
        TryNextMethod( );
    fi;
    
    objects := List( dims, dim -> dim / kmat );
    
    morphisms := SetOfGeneratingMorphisms( Source( coPSh ) );
    
    k := CommutativeSemiringOfLinearCategory( kmat );
    
    mat :=
      function ( m )
        local source, target;
        
        source := VertexIndex( UnderlyingVertex( Source( morphisms[m] ) ) );
        target := VertexIndex( UnderlyingVertex( Target( morphisms[m] ) ) );
        
        if IsHomalgMatrix( matrices[m] ) then
            m := matrices[m];
        else
            m := HomalgMatrix( One( k ) * matrices[m], dims[source], dims[target], k );
        fi;
        
        return m / kmat;
        
    end;
    
    morphisms := List( [ 1 .. Length( morphisms ) ], mat );
    
    return CreateCoPreSheafByValues( coPSh, objects, morphisms );
    
end );

##
InstallMethodWithCache( CoPreSheaves,
        "for a CAP category and a homalg field",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsHomalgRing and IsFieldForHomalg ],
        
  function ( B, k )
    local kmat, coPSh;
    
    if HasRangeCategoryOfHomomorphismStructure( B ) then
        
        kmat := RangeCategoryOfHomomorphismStructure( B );
        
    else
        
        kmat := CategoryOfRows( k );
        
    fi;
    
    Assert( 0, IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) );
    
    CapCategorySwitchLogicOn( kmat );
    
    coPSh := CoPreSheaves( B, kmat );
    
    CapCategorySwitchLogicOn( coPSh );
    
    return coPSh;
    
end );

####################################
#
# View, Print, Display and LaTeX methods:
#
####################################

##
InstallMethod( ViewString,
        [ IsObjectInCoPreSheafCategory ],
        
  function ( F )
    local algebroid, vertices, arrows, v_dim, v_string, a_dim, a_string, string;
    
    if not (IsMatrixCategory( Target( CapCategory( F ) ) ) or IsCategoryOfRows( Target( CapCategory( F ) ) )) then
        TryNextMethod();
    fi;
    
    algebroid := Source( CapCategory( F ) );
    
    vertices := List( SetOfObjects( algebroid ), UnderlyingVertex );
    
    v_dim := List( ValuesOfCoPreSheaf( F )[1], ObjectDatum );
    
    v_string := ListN( vertices, v_dim, { vertex, dim } -> Concatenation( "(", String( vertex ), ")->", String( dim ) ) );
    
    v_string := JoinStringsWithSeparator( v_string, ", " );
    
    arrows := List( SetOfGeneratingMorphisms( algebroid ), UnderlyingQuiverAlgebraElement );
    
    if not IsPathAlgebra( UnderlyingQuiverAlgebra( algebroid ) ) then
      
      arrows := List( arrows, a -> Paths( Representative( a ) )[ 1 ] );
      
    else
      
      arrows := List( arrows, a -> Paths( a )[ 1 ] );
      
    fi;
    
    a_dim := List( ValuesOfCoPreSheaf( F )[2], m -> [ ObjectDatum( Source( m ) ), ObjectDatum( Target( m ) ) ] );
    
    a_string := ListN( arrows, a_dim,
                  { arrow, dim } -> Concatenation(
                      "(", String( arrow ), ")->", String( dim[ 1 ] ), "x", String( dim[ 2 ] ) )
                    );
    
    a_string := JoinStringsWithSeparator( a_string, ", " );
    
    string := Concatenation( v_string, "; ", a_string );
    
    return Concatenation( "<", string, ">" );
    
end );

##
InstallMethod( ViewString,
        [ IsMorphismInCoPreSheafCategory ],
        
  function ( eta )
    local vertices, s_dim, r_dim, string;
    
    if not (IsMatrixCategory( Target( CapCategory( eta ) ) ) or IsCategoryOfRows( Target( CapCategory( eta ) ) )) then
        TryNextMethod();
    fi;
    
    vertices := List( SetOfObjects( Source( Source( eta ) ) ), UnderlyingVertex );
     
    s_dim := List( ValuesOfCoPreSheaf( Source( eta ) )[1], ObjectDatum );
    
    r_dim := List( ValuesOfCoPreSheaf( Target( eta ) )[1], ObjectDatum );
   
    string := ListN( vertices, s_dim, r_dim,
                { vertex, s, r } ->
                    Concatenation( "(", String( vertex ), ")->", String( s ), "x", String( r ) ) );
    
    string := JoinStringsWithSeparator( string, ", " );
    
    return Concatenation( "<", string, ">" );
    
end );
