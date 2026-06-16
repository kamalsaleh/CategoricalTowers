




##
InstallMethod( CreatePreSheaf,
        "for a presheaf category and two lists",
        [ IsPreSheafCategory and HasRangeCategoryOfHomomorphismStructure, IsList, IsList ],
        
  function ( PSh, dims, matrices )
    local kmat, objects, morphisms, k, mat;
    
    if dims = [ ] then
        Error( "the list of dimensions is empty\n" );
    elif not IsInt( dims[1] ) then
        Error( "expecting a list of integers as the second argument but received ", dims, "\n" );
    fi;
    
    kmat := RangeCategoryOfHomomorphismStructure( PSh );
    
    if not ( IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) ) then
        TryNextMethod( );
    fi;
    
    objects := List( dims, dim -> dim / kmat );
    
    morphisms := SetOfGeneratingMorphisms( Source( PSh ) );
    
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
    
    return CreatePreSheafByValues( PSh, objects, morphisms );
    
end );

##
InstallMethodWithCache( PreSheaves,
        "for a f.p. category and a category",
        [ IsFpCategoryDefinedByQuiverAlgebra, IsCapCategory ],
        
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
    [ "overhead", true ],
    [ "no_precompiled_code", false ],
  ],
  function( CAP_NAMED_ARGUMENTS, B, D )
    
    return PreSheavesOfFpEnrichedCategory( B, D : FinalizeCategory := CAP_NAMED_ARGUMENTS.FinalizeCategory, no_precompiled_code := CAP_NAMED_ARGUMENTS.no_precompiled_code );
    
end ) );
        
##
InstallMethodWithCache( PreSheaves,
        "for an algebroid and a category",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsCapCategory ],
        
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
    [ "overhead", true ],
    [ "no_precompiled_code", false ],
  ],
  function( CAP_NAMED_ARGUMENTS, B, D )
    
    return PreSheavesOfFpEnrichedCategory( B, D : FinalizeCategory := CAP_NAMED_ARGUMENTS.FinalizeCategory, no_precompiled_code := CAP_NAMED_ARGUMENTS.no_precompiled_code );
    
end ) );

##
InstallMethodWithCache( PreSheaves,
        "for a CAP category and a homalg field",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsHomalgRing and IsFieldForHomalg ],
        
  function ( B, k )
    local kmat, PSh;
    
    if HasRangeCategoryOfHomomorphismStructure( B ) then
        
        kmat := RangeCategoryOfHomomorphismStructure( B );
        
    else
        
        kmat := CategoryOfRows( k );
        
    fi;
    
    Assert( 0, IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) );
    
    CapCategorySwitchLogicOn( kmat );
    
    PSh := PreSheaves( B, kmat );
    
    CapCategorySwitchLogicOn( PSh );
    
    return PSh;
    
end );

##
InstallMethodForCompilerForCAP( ApplyObjectInPreSheafCategoryOfFpEnrichedCategoryToMorphism,
        "for a finitely presented category defined by a quiver algebra, a presheaf category of it, an object in it, and a CAP morphism",
        [ IsFpCategoryDefinedByQuiverAlgebra, IsPreSheafCategoryOfFpEnrichedCategory, IsObjectInPreSheafCategoryOfFpEnrichedCategory, IsCapCategoryMorphism ],
        
  function ( B, PSh, F, morB )
    local D, pos, F_datum;
    
    D := Target( PSh );
    
    pos := Position( SetOfGeneratingMorphisms( B ), morB );
    
    if IsInt( pos ) then
        return ValuesOfPreSheaf( F )[2][pos];
    elif IsEqualToIdentityMorphism( B, morB ) then
        return IdentityMorphism( D,
                       ApplyObjectInPreSheafCategoryOfFpEnrichedCategoryToObject( PSh, F, Source( morB ) ) );
    fi;
    
    F_datum := ObjectDatum( PSh, F );
    
    return PostComposeList( D,
                   F_datum[1][VertexIndex( UnderlyingVertex( Target( morB ) ) )],
                   ListOfValues( F_datum[2] ){1 + DecompositionIndicesOfMorphism( B, morB )},
                   F_datum[1][VertexIndex( UnderlyingVertex( Source( morB ) ) )] );
    
end );

##
InstallMethodForCompilerForCAP( ApplyObjectInPreSheafCategoryOfFpEnrichedCategoryToMorphism,
        "for an algebroid defined by a quiver algebra, a presheaf category of it, an object in it, and a CAP morphism",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsPreSheafCategoryOfFpEnrichedCategory, IsObjectInPreSheafCategoryOfFpEnrichedCategory, IsCapCategoryMorphism ],
        
  function ( B, PSh, F, morB )
    local D, pos, B_op, morB_op;
    
    D := Target( PSh );
    
    pos := Position( SetOfGeneratingMorphisms( B ), morB );
    
    if IsInt( pos ) then
        return ValuesOfPreSheaf( F )[2][pos];
    elif IsEqualToIdentityMorphism( B, morB ) then
        return IdentityMorphism( D,
                       ApplyObjectInPreSheafCategoryOfFpEnrichedCategoryToObject( PSh, F, Source( morB ) ) );
    fi;
    
    B_op := OppositeOfSource( PSh );
    
    morB_op := MorphismConstructor( B_op,
                       SetOfObjects( B_op )[VertexIndex( UnderlyingVertex( Target( morB ) ) )],
                       OppositeAlgebraElement( UnderlyingQuiverAlgebraElement( morB ) ),
                       SetOfObjects( B_op )[VertexIndex( UnderlyingVertex( Source( morB ) ) )] );
    
    return FunctorMorphismOperation( UnderlyingCapTwoCategoryCell( PSh, F ) )(
                   ApplyObjectInPreSheafCategoryOfFpEnrichedCategoryToObject( PSh, F, Target( morB ) ),
                   morB_op,
                   ApplyObjectInPreSheafCategoryOfFpEnrichedCategoryToObject( PSh, F, Source( morB ) ) );
    
end );

##
InstallMethod( WellDefinednessForObjectsCheckDataOrFail,
    "for a finitely presented category defined by a quiver algebra",
    [ IsFpCategoryDefinedByQuiverAlgebra ],

  function ( B )
    local B_op, kq, A, relations, is_respected;
    
    B_op := OppositeOfObjectFiniteCategory( B );
    
    kq := UnderlyingQuiverAlgebra( B_op );
    relations := RelationsOfFpCategoryDefinedByQuiverAlgebra( B_op );
    A := kq;
    
    if IsQuotientOfPathAlgebra( A ) then
      A := PathAlgebra( A );
    fi;
    
    relations := List( relations, a -> List( a, ai -> PathAsAlgebraElement( A, ai ) ) );
    is_respected := function ( PSh, F, relations )
        local D, cell;
    
        D := Target( PSh );
        cell := UnderlyingCapTwoCategoryCell( F );
    
        return ForAll( relations, m -> IsCongruentForMorphisms( D,
                       ApplyToQuiverAlgebraElement( cell, m[1] ),
                       ApplyToQuiverAlgebraElement( cell, m[2] ) ) );
    
    end;
    
    return Pair( relations, is_respected );
    
end );

##
InstallMethod( WellDefinednessForObjectsCheckDataOrFail,
    "for an algebroid defined by a quiver algebra",
    [ IsFpAlgebroidDefinedByQuiverAlgebra ],
    
  function ( B )
    local relations, is_respected;
    
    relations := List( RelationsOfAlgebroid( OppositeOfObjectFiniteCategory( B ) ), UnderlyingQuiverAlgebraElement );
    is_respected := function ( PSh, F, relations )
        local D, cell;
        
        D := Target( PSh );
        cell := UnderlyingCapTwoCategoryCell( F );
        
        return ForAll( relations, m -> IsZeroForMorphisms( D, ApplyToQuiverAlgebraElement( cell, m ) ) );
        
    end;
    
    return Pair( relations, is_respected );
    
end );

##
InstallMethod( AdditionalMonoidalPreSheafOperationNames,
    "for an algebroid defined by a quiver algebra",
    [ IsFpAlgebroidDefinedByQuiverAlgebra ],
    
  function ( B )
    local operation_names;
    
    if not ( HasCounit( B ) and HasComultiplication( B ) ) then
        return [ ];
    fi;
    
    operation_names := ShallowCopy( CAP_INTERNAL_METHOD_NAME_LIST_FOR_MONOIDAL_PRESHEAF_CATEGORY );
    
    if HasAntipode( B ) then
        Append( operation_names, CAP_INTERNAL_METHOD_NAME_LIST_FOR_MONOIDAL_PRESHEAF_CATEGORY_WITH_DUALS );
    fi;
    
    return operation_names;
    
end );

##
InstallMethod( AddAdditionalPrecompiledFunctionsToPreSheafCategory,
    "for a quiver algebra source, a category, and a presheaf category",
    [ IsFpCategoryDefinedByQuiverAlgebra, IsCapCategory, IsPreSheafCategory ],
    
  function ( B, D, PSh )
    
    if not IsSkeletalCategoryOfFiniteSets( D ) then
        return;
    fi;
    
    ADD_FUNCTIONS_FOR_PreSheavesOfFpCategoryDefinedByQuiverAlgebraInSkeletalFinSetsPrecompiled( PSh );
    
    ADD_FUNCTIONS_FOR_PreSheavesOfFpCategoryDefinedByQuiverAlgebraInSkeletalFinSetsSubobjectClassifierPrecompiled( PSh );
    
end );

##
InstallMethod( AddAdditionalPrecompiledFunctionsToPreSheafCategory,
    "for an algebroid defined by a quiver algebra, a category, and a presheaf category",
    [ IsFpAlgebroidDefinedByQuiverAlgebra, IsCapCategory, IsPreSheafCategory ],
    
  function ( B, D, PSh )
    local commutative_semiring;
    
    commutative_semiring := CommutativeSemiringOfLinearCategory( D );
    
    if IsCategoryOfRows( D ) and
       IsHomalgRing( commutative_semiring ) and
       HasIsFieldForHomalg( commutative_semiring ) and IsFieldForHomalg( commutative_semiring ) and
       not B!.over_Z then
        
        if IsQuotientOfPathAlgebra( UnderlyingQuiverAlgebra( B ) ) or
           ( HasIsMonoidalCategory( D ) and IsMonoidalCategory( D ) and
             HasCounit( B ) and HasComultiplication( B ) ) then
            
            ADD_FUNCTIONS_FOR_PreSheavesOfAlgebroidWithRelationsInCategoryOfRowsPrecompiled( PSh );
            
        else
            
            ADD_FUNCTIONS_FOR_PreSheavesOfFreeAlgebroidInCategoryOfRowsPrecompiled( PSh );
            
        fi;
        
    fi;
    
end );

##
InstallMethodForCompilerForCAP( NerveTruncatedInDegree2,
        [ IsFpCategoryDefinedByQuiverAlgebra ],
        
  function ( B )
    
    return CreatePreSheafByValues( PreSheaves( SimplicialCategoryTruncatedInDegree2 ), NerveTruncatedInDegree2Data( B ) );
    
end );

##
InstallMethod( ViewString,
        [ IsObjectInPreSheafCategoryOfFpEnrichedCategory ],
        
  function ( F )
    local PSh, B, vertices, v_dim, v_string, arrows, a_dim, a_string, string;
    
    PSh := CapCategory( F );
     
    if not ( IsFpAlgebroidDefinedByQuiverAlgebra( Source( PSh ) ) and ForAny( [ IsMatrixCategory, IsCategoryOfRows ], is -> is( Target( PSh ) ) ) ) then
        TryNextMethod();
    fi;
    
    B := Source( CapCategory( F ) );
    
    vertices := List( SetOfObjects( B ), UnderlyingVertex );
    
    v_dim := List( ListOfValues( ValuesOfPreSheaf( F )[1] ), ObjectDatum );
    
    v_string := ListN( vertices, v_dim, { vertex, dim } -> Concatenation( "(", String( vertex ), ")->", String( dim ) ) );
    
    v_string := JoinStringsWithSeparator( v_string, ", " );
    
    arrows := List( SetOfGeneratingMorphisms( B ), UnderlyingQuiverAlgebraElement );
    
    if not IsPathAlgebra( UnderlyingQuiverAlgebra( B ) ) then
      
      arrows := List( arrows, a -> Paths( Representative( a ) )[ 1 ] );
      
    else
      
      arrows := List( arrows, a -> Paths( a )[ 1 ] );
      
    fi;
    
    a_dim := List( ValuesOfPreSheaf( F )[2], m -> [ ObjectDatum( Source( m ) ), ObjectDatum( Target( m ) ) ] );
    
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
        [ IsMorphismInPreSheafCategoryOfFpEnrichedCategory ],
        
  function ( eta )
    local PSh, vertices, s_dim, r_dim, string;
    
    PSh := CapCategory( eta );
    
    if not ( IsFpAlgebroidDefinedByQuiverAlgebra( Source( PSh ) ) and ForAny( [ IsMatrixCategory, IsCategoryOfRows ], is -> is( Target( PSh ) ) ) ) then
        TryNextMethod();
    fi;
    
    vertices := List( SetOfObjects( Source( Source( eta ) ) ), UnderlyingVertex );
    
    s_dim := List( ValuesOfPreSheaf( Source( eta ) )[1], ObjectDatum );
    
    r_dim := List( ValuesOfPreSheaf( Target( eta ) )[1], ObjectDatum );
    
    string := ListN( vertices, s_dim, r_dim,
                { vertex, s, r } ->
                    Concatenation( "(", String( vertex ), ")->", String( s ), "x", String( r ) ) );
    
    string := JoinStringsWithSeparator( string, ", " );
    
    return Concatenation( "<", string, ">" );
    
end );
