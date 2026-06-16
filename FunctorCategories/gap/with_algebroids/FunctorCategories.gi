# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations depending on the Algebroids package
#

##
InstallMethod( AddAdditionalMonoidalStructureToFunctorCategory,
        "for a functor category with algebroid source",
        [ IsFunctorCategory, IsFpAlgebroidDefinedByQuiverAlgebra, IsCapCategory ],
        
  function ( Hom, B, D )
    local properties, doctrines, name;
    
    if not ( HasCounit( B ) and HasComultiplication( B ) ) then
        return;
    fi;
    
    properties := [ "IsMonoidalCategory",
                    #"IsBraidedMonoidalCategory",
                    #"IsSymmetricMonoidalCategory",
                    #"IsClosedMonoidalCategory",
                    #"IsSymmetricClosedMonoidalCategory",
                    #"IsRigidSymmetricClosedMonoidalCategory",
                    ];
    
    doctrines := CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "doctrines", [ ] );
    
    if not doctrines = [ ] and IsStringRep( doctrines ) then
        doctrines := [ doctrines ];
    fi;
    
    Append( properties, doctrines );
    
    for name in Intersection( ListKnownCategoricalProperties( D ), properties ) do
        name := ValueGlobal( name );
        
        Setter( name )( Hom, name( D ) );
        
    od;
    
    AddTensorUnit( Hom,
      function ( Hom )
        local B, D, I_D, functor_on_objects, counit, id, mors, functor_on_morphisms;
        
        B := Source( Hom );
        D := Target( Hom );
        
        I_D := TensorUnit( D );
        
        functor_on_objects := objB_index -> I_D;
        
        counit := Counit( B );
        
        id := IdentityMorphism( D, I_D );
        
        mors := SetOfGeneratingMorphisms( B );
        
        functor_on_morphisms :=
          function ( new_source, morB_index, new_range )
            local coef;
            
            coef := Coefficients( UnderlyingQuiverAlgebraElement( ApplyFunctor( counit, mors[morB_index] ) ) );
            
            if Length( coef ) = 1 then
                coef := coef[1];
            elif coef = [ ] then
                coef := 0;
            else
                Error( "the list coef has more than one entry\n" );
            fi;
            
            return coef * id;
            
        end;
        
        return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_morphisms );
        
    end );
    
    AddTensorProductOnObjects( Hom,
      function ( Hom, F, G )
        local B, D, F_o_vals, G_o_vals, functor_on_objects, comult, mors, functor_on_morphisms;
        
        B := Source( Hom );
        D := Target( Hom );
        
        F_o_vals := ValuesOfFunctor( F )[1];
        G_o_vals := ValuesOfFunctor( G )[1];
        
        functor_on_objects := objB_index -> TensorProductOnObjects( D, F_o_vals[objB_index], G_o_vals[objB_index] );
        
        comult := Comultiplication( B );
        
        mors := SetOfGeneratingMorphisms( B );
        
        functor_on_morphisms :=
          function ( new_source, morB_index, new_range )
            local Delta;
            
            Delta := ApplyFunctor( comult, mors[morB_index] );
            
            Delta := DecompositionOfMorphismInSquareOfAlgebroid( Delta );
            
            return Sum( List( Delta,
                           s -> s[1] * PreComposeList( D, List( s[2],
                                   t -> TensorProductOnMorphisms( D, F( t[1] ), G( t[2] ) ) ) ) ) );
        
        end;
        
        return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_morphisms );
        
    end );

    if not HasAntipode( B ) then
        return;
    fi;
    
    AddDualOnObjects( Hom,
      function ( Hom, F )
        local B, D, F_o_vals, functor_on_objects, antipode, mors, functor_on_morphisms;
        
        B := Source( Hom );
        D := Target( Hom );
        
        F_o_vals := ValuesOfFunctor( F )[1];
        
        functor_on_objects := objB_index -> DualOnObjects( D, F_o_vals[objB_index] );
        
        antipode := Antipode( B );
        
        mors := SetOfGeneratingMorphisms( B );
        
        functor_on_morphisms :=
          function ( new_source, morB_index, new_range )
            local S;
            
            S := DecompositionOfMorphismInAlgebroid( ApplyFunctor( antipode, mors[morB_index] ) );
            
            return Sum( List( S,
                           s -> s[1] * PreComposeList( D, List( s[2],
                                   t -> DualOnMorphisms( D, F( t ) ) ) ) ) );
        
        end;
        
        return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_morphisms );
        
    end );
    
end );

##
InstallMethod( AsObjectInFunctorCategory,
        "for a functor category and two lists",
        [ IsFunctorCategory and HasRangeCategoryOfHomomorphismStructure, IsList, IsList ],
        
  function ( Hom, dims, matrices )
    local kmat, objects, morphisms, k, mat;
    
    if dims = [ ] then
        Error( "the list of dimensions is empty\n" );
    elif not ForAll( dims, IsInt ) then
        Error( "expecting a list of integers as the second argument but received ", dims, "\n" );
    fi;
    
    kmat := RangeCategoryOfHomomorphismStructure( Hom );
    
    if not ( IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) ) then
        TryNextMethod( );
    fi;
    
    objects := List( dims, dim -> dim / kmat );
    
    morphisms := SetOfGeneratingMorphisms( Source( Hom ) );
    
    k := CommutativeSemiringOfLinearCategory( kmat );
    
    mat :=
      function ( m )
        local source, target;
        
        if MorphismFilter( kmat )( matrices[m] ) then
            return matrices[m];
        fi;
        
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
    
    return AsObjectInFunctorCategoryByValues( Hom, objects, morphisms );
    
end );

##
InstallMethodWithCache( FunctorCategory,
        "for a CAP category and a homalg field",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsHomalgRing and IsFieldForHomalg ],
        
  function ( B, k )
    local kmat, Hom;
    
    if HasRangeCategoryOfHomomorphismStructure( B ) then
        
        kmat := RangeCategoryOfHomomorphismStructure( B );
        
    else
        
        kmat := CategoryOfRows( k );
        
    fi;
    
    Assert( 0, IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) );
    
    CapCategorySwitchLogicOn( kmat );
    
    Hom := FunctorCategory( B, kmat );
    
    CapCategorySwitchLogicOn( Hom );
    
    return Hom;
    
end );

##
InstallMethod( Hom,
        "for a CAP category and a homalg field",
        [ IsFpAlgebroidDefinedByQuiverAlgebra, IsHomalgRing and IsFieldForHomalg ],
        
  FunctorCategory );

####################################
#
# View, Print, Display and LaTeX methods:
#
####################################

##
InstallMethod( ViewString,
        [ IsObjectInFunctorCategory ],
        
  function ( F )
    local algebroid, vertices, arrows, v_dim, v_string, a_dim, a_string, string;
    
    if not (IsMatrixCategory( Target( CapCategory( F ) ) ) or IsCategoryOfRows( Target( CapCategory( F ) ) )) then
        TryNextMethod();
    fi;
    
    algebroid := Source( CapCategory( F ) );
    
    vertices := List( SetOfObjects( algebroid ), UnderlyingVertex );
    
    v_dim := List( ValuesOfFunctor( F )[1], ObjectDatum );
    
    v_string := ListN( vertices, v_dim, { vertex, dim } -> Concatenation( "(", String( vertex ), ")->", String( dim ) ) );
    
    v_string := JoinStringsWithSeparator( v_string, ", " );
    
    arrows := List( SetOfGeneratingMorphisms( algebroid ), UnderlyingQuiverAlgebraElement );
    
    if not IsPathAlgebra( UnderlyingQuiverAlgebra( algebroid ) ) then
      
      arrows := List( arrows, a -> Paths( Representative( a ) )[ 1 ] );
      
    else
      
      arrows := List( arrows, a -> Paths( a )[ 1 ] );
      
    fi;
    
    a_dim := List( ValuesOfFunctor( F )[2], m -> [ ObjectDatum( Source( m ) ), ObjectDatum( Target( m ) ) ] );
    
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
        [ IsMorphismInFunctorCategory ],
        
  function ( eta )
    local vertices, s_dim, r_dim, string;
    
    if not (IsMatrixCategory( Target( CapCategory( eta ) ) ) or IsCategoryOfRows( Target( CapCategory( eta ) ) )) then
        TryNextMethod();
    fi;
    
    vertices := List( SetOfObjects( Source( Source( eta ) ) ), UnderlyingVertex );
     
    s_dim := List( ValuesOfFunctor( Source( eta ) )[1], ObjectDatum );
    
    r_dim := List( ValuesOfFunctor( Target( eta ) )[1], ObjectDatum );
   
    string := ListN( vertices, s_dim, r_dim,
                { vertex, s, r } ->
                    Concatenation( "(", String( vertex ), ")->", String( s ), "x", String( r ) ) );
    
    string := JoinStringsWithSeparator( string, ", " );
    
    return Concatenation( "<", string, ">" );
    
end );
