




##
InstallMethod( QuotientCategory,
        [ IsLinearClosure, IsDenseList ],
  
  function ( kC, relations )
    local C, q, reduced_groebner_basis, leading_monomials, congruence_function, name, quo_kC, FinalizeCategory, homQ, range_cat;
    
    C := UnderlyingCategory( kC );
    
    q := UnderlyingQuiver( C );
    
    if not IsPathCategory( C ) then
        TryNextMethod( );
    fi;
    
    reduced_groebner_basis := ReducedGroebnerBasis( kC, relations );
    
    congruence_function := m -> IsZeroForMorphisms( kC, ReductionOfMorphism( kC, m, reduced_groebner_basis ) );
    
    name := List( relations{[ 1 .. Minimum( 3, Length( relations ) )]},
                  function ( rel )
                    local str;
                    
                    str := ViewString( rel );
                    
                    return str{[ 1 .. PositionSublist( str, ":" ) - Length( q!.colors.other ) - 1 ]};
                    
                  end );
    
    if Length( relations ) > 3 then
      Add( name, "..." );
    fi;
    
    name := Concatenation( Name( kC ), " / [ ", JoinStringsWithSeparator( name, ", " ), " ]" );
    
    quo_kC := QuotientCategory(
                    rec( name := name,
                    nr_arguments_of_congruence_function := 1,
                    congruence_function := congruence_function,
                    underlying_category := kC ) : FinalizeCategory := false );
    
    SetDefiningRelations( quo_kC, relations );
    SetGroebnerBasisOfDefiningRelations( quo_kC, reduced_groebner_basis );
    
    SetSetOfObjects( quo_kC,
        List( SetOfObjects( kC ), o -> ObjectConstructor( quo_kC, o ) ) );
    
    SetSetOfGeneratingMorphisms( quo_kC,
        List( SetOfGeneratingMorphisms( kC ), m ->
                    MorphismConstructor( quo_kC,
                        SetOfObjects( quo_kC )[ObjectIndex( ObjectDatum( kC, Source( m ) ) )],
                        m,
                        SetOfObjects( quo_kC )[ObjectIndex( ObjectDatum( kC, Target( m ) ) )] ) ) );

    # Hom-Structure
    
    leading_monomials := List( reduced_groebner_basis, g -> SupportMorphisms( g )[1] );
    
    if HasFiniteNumberOfMacaulayMorphisms( C, leading_monomials ) then
        
        homQ := MacaulayMorphisms( C, leading_monomials );
        
        SetExternalHoms( quo_kC,
              LazyHList( [ 1 .. NumberOfObjects( q ) ],
                s -> LazyHList( [ 1 .. NumberOfObjects( q ) ],
                  t -> List( homQ[s][t],
                    m -> MorphismConstructor( quo_kC,
                              SetOfObjects( quo_kC )[s],
                              MorphismConstructor( kC,
                                  SetOfObjects( kC )[s],
                                  Pair( [ One( UnderlyingRing( kC ) ) ], [ m ] ),
                                  SetOfObjects( kC )[t] ),
                              SetOfObjects( quo_kC )[t] ) ) ) ) );
        
        range_cat := ValueOption( "range_of_HomStructure" );
        
        if range_cat = fail and (HasIsEquippedWithHomomorphismStructure and IsEquippedWithHomomorphismStructure)( kC ) then
            
            range_cat := RangeCategoryOfHomomorphismStructure( kC );
            
        elif range_cat = fail then
            
            range_cat := CategoryOfRows( UnderlyingRing( kC ) );
            
        fi;
        
        SetIsEquippedWithHomomorphismStructure( quo_kC, true );
        
        SetRangeCategoryOfHomomorphismStructure( quo_kC, range_cat );
        
        ##
        AddBasisOfExternalHom( quo_kC,
          function ( quo_kC, source, target )
            local kC, s, t;
            
            kC := UnderlyingCategory( quo_kC );
            
            s := ObjectIndex( ObjectDatum( kC, ObjectDatum( quo_kC, source ) ) );
            t := ObjectIndex( ObjectDatum( kC, ObjectDatum( quo_kC, target ) ) );
            
            return ExternalHoms( quo_kC )[s][t];
            
        end );
        
        ##
        AddCoefficientsOfMorphism( quo_kC,
          function ( quo_kC, mor )
            local kC, s, t, support_mor;
            
            kC := UnderlyingCategory( quo_kC );
            
            s := ObjectIndex( ObjectDatum( kC, ObjectDatum( quo_kC, Source( mor ) ) ) );
            t := ObjectIndex( ObjectDatum( kC, ObjectDatum( quo_kC, Target( mor ) ) ) );
            
            mor := ReductionOfMorphism( kC, MorphismDatum( quo_kC, mor ), GroebnerBasisOfDefiningRelations( quo_kC ) );
            
            support_mor := SupportMorphisms( mor );
            
            return List( ExternalHoms( quo_kC )[s][t],
                                function ( m )
                                  local p;
                                  
                                  p := Position( support_mor, SupportMorphisms( MorphismDatum( quo_kC, m ) )[1] );
                                  
                                  if p = fail then
                                      return Zero( UnderlyingRing( kC ) );
                                  else
                                      return CoefficientsList( mor )[p];
                                  fi;
                                  
                                end );
            
        end );
    fi;
    
    INSTALL_CANONICAL_REPRESENTATIVE_METHODS_IN_QUOTIENT_CATEGORIES_OF_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( quo_kC );
    INSTALL_VIEW_AND_DISPLAY_METHODS_IN_QUOTIENT_CATEGORIES_OF_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( quo_kC );
    
    Finalize( quo_kC );
    
    return quo_kC;
    
end );

##
InstallMethod( QuotientCategory,
        [ IsLinearClosure, IsDenseList ],
  
  function ( k_quo_C, relations )
    local quo_C, k, C, q, kC, rel_1, rel_2, new_relations, quo_kC, object_constructor, object_datum, morphism_constructor, morphism_datum,
    modeling_tower_object_constructor, modeling_tower_object_datum, modeling_tower_morphism_constructor, modeling_tower_morphism_datum, name, quo_k_quo_C;
    
    quo_C := UnderlyingCategory( k_quo_C );
    
    if not IsQuotientOfPathCategory( quo_C ) then
        TryNextMethod( );
    fi;
    
    k := UnderlyingRing( k_quo_C );
    
    C := UnderlyingCategory( quo_C );
    
    q := UnderlyingQuiver( C );
    
    kC := LinearClosure( k, C : overhead := false );
    
    rel_1 :=
      List( GroebnerBasisOfDefiningRelations( quo_C ), m ->
                MorphismConstructor( kC,
                      SetOfObjects( kC )[ObjectIndex( Source( m[1] ) )],
                      Pair( [ One( k ), MinusOne( k ) ], m ),
                      SetOfObjects( kC )[ObjectIndex( Target( m[1] ) )] ) );

    rel_2 :=
      List( relations, m ->
                MorphismConstructor( kC,
                      SetOfObjects( kC )[ObjectIndex( ObjectDatum( quo_C, ObjectDatum( k_quo_C, Source( m ) ) ) )],
                      Pair( CoefficientsList( m ), List( SupportMorphisms( m ), CanonicalRepresentative ) ),
                      SetOfObjects( kC )[ObjectIndex( ObjectDatum( quo_C, ObjectDatum( k_quo_C, Target( m ) ) ) )] ) );
    
    new_relations := Concatenation( rel_1, rel_2 );
    
    quo_kC := QuotientCategory( kC, new_relations );
    
    object_constructor := { quo_k_quo_C, obj } -> CreateCapCategoryObjectWithAttributes( quo_k_quo_C, UnderlyingCell, obj );
    
    object_datum := { quo_k_quo_C, obj } -> UnderlyingCell( obj );
    
    morphism_constructor := { quo_k_quo_C, S, mor, T } -> CreateCapCategoryMorphismWithAttributes( quo_k_quo_C, S, T, UnderlyingCell, mor );
    
    morphism_datum := { quo_k_quo_C, mor } -> UnderlyingCell( mor );
    
    ## from the raw object data to the object in the highest stage of the tower
    modeling_tower_object_constructor :=
      function ( quo_k_quo_C, datum )
        local k_quo_C, quo_C, C, i, quo_kC;
        
        k_quo_C := UnderlyingCategory( quo_k_quo_C );
        
        quo_C := UnderlyingCategory( k_quo_C );
        
        C := UnderlyingCategory( quo_C );
        
        i := ObjectDatum( C, ObjectDatum( quo_C, UnderlyingOriginalObject( datum ) ) );
        
        quo_kC := ModelingCategory( quo_k_quo_C );
        
        return SetOfObjects( quo_kC )[i];
        
    end;
    
    ## from the object in the highest stage of the tower to the raw object datum
    modeling_tower_object_datum :=
      function ( quo_k_quo_C, obj )
        local quo_kC, kC, C, i;
        
        quo_kC := ModelingCategory( quo_k_quo_C );
        
        kC := UnderlyingCategory( quo_kC );
        
        C := UnderlyingCategory( kC );
        
        i := ObjectDatum( C, ObjectDatum( kC, ObjectDatum( quo_kC, obj ) ) );
        
        return SetOfObjects( UnderlyingCategory( quo_k_quo_C ) )[i];
        
    end;
    
    ## from the raw morphism datum to the morphism in the highest stage of the tower
    modeling_tower_morphism_constructor :=
      function ( quo_k_quo_C, S, datum, T )
        local quo_kC, coeffs, suppor;
        
        quo_kC := ModelingCategory( quo_k_quo_C );
        
        coeffs := CoefficientsList( datum );
        suppor := List( SupportMorphisms( datum ), CanonicalRepresentative );
        
        return MorphismConstructor( quo_kC,
                      S,
                      MorphismConstructor( UnderlyingCategory( quo_kC ), ObjectDatum( quo_kC, S ), Pair( coeffs, suppor ), ObjectDatum( quo_kC, T ) ),
                      T );
        
    end;
    
    ## from the morphism in the highest stage of the tower to the raw morphism datum
    modeling_tower_morphism_datum :=
      function ( quo_k_quo_C, mor )
        local quo_kC, kC, k_quo_C, quo_C, C, q, s, t, coeffs, suppor;
        
        quo_kC := ModelingCategory( quo_k_quo_C );
        
        kC := UnderlyingCategory( quo_kC );
        
        k_quo_C := UnderlyingCategory( quo_k_quo_C );
        
        quo_C := UnderlyingCategory( k_quo_C );
        
        C := UnderlyingCategory( quo_C );
        
        q := UnderlyingQuiver( C );
        
        s := ObjectIndex( ObjectDatum( kC, ObjectDatum( quo_kC, Source( mor ) ) ) );
        t := ObjectIndex( ObjectDatum( kC, ObjectDatum( quo_kC, Target( mor ) ) ) );
        
        coeffs := CoefficientsList( MorphismDatum( mor ) );
        suppor := List( SupportMorphisms( MorphismDatum( mor ) ), m -> MorphismConstructor( quo_C, SetOfObjects( quo_C )[s], m, SetOfObjects( quo_C )[t] ) );
        
        return MorphismConstructor( k_quo_C, SetOfObjects( k_quo_C )[s], Pair( coeffs, suppor ), SetOfObjects( k_quo_C )[t] );
        
    end;
    
    name := List( relations{[ 1 .. Minimum( 3, Length( relations ) )]},
                  function ( rel )
                    local str;
                    
                    str := ViewString( rel );
                    
                    return str{[ 1 .. PositionSublist( str, ":" ) - Length( q!.colors.other ) - 1 ]};
                    
                  end );
    
    if Length( relations ) > 3 then
      Add( name, "..." );
    fi;
    
    name := Concatenation( Name( k_quo_C ), " / [ ", JoinStringsWithSeparator( name, ", " ), " ]" );
    
    ##
    quo_k_quo_C :=
        ReinterpretationOfCategory( quo_kC,
          rec( name := name,
               category_filter := IsQuotientCapCategory,
               category_object_filter := IsQuotientCapCategoryObject,
               category_morphism_filter := IsQuotientCapCategoryMorphism,
               object_constructor := object_constructor,
               object_datum := object_datum,
               morphism_datum := morphism_datum,
               morphism_constructor := morphism_constructor,
               modeling_tower_object_constructor := modeling_tower_object_constructor,
               modeling_tower_object_datum := modeling_tower_object_datum,
               modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
               modeling_tower_morphism_datum := modeling_tower_morphism_datum,
               only_primitive_operations := true ) : FinalizeCategory := false );
    
    quo_k_quo_C!.is_computable := true;
    
    SetUnderlyingCategory( quo_k_quo_C, k_quo_C );
    SetDefiningRelations( quo_k_quo_C, relations );
    
    SetSetOfObjects( quo_k_quo_C, List( SetOfObjects( quo_kC ), obj -> ReinterpretationOfObject( quo_k_quo_C, obj ) ) );
    
    SetSetOfGeneratingMorphisms( quo_k_quo_C,
        ListN( IndicesOfSources( q ), SetOfGeneratingMorphisms( quo_kC ), IndicesOfTargets( q ),
          { s, m, t } -> ReinterpretationOfMorphism( quo_k_quo_C,
                              SetOfObjects( quo_k_quo_C )[s],
                              m,
                              SetOfObjects( quo_k_quo_C )[t] ) ) );
    
    if HasIsEquippedWithHomomorphismStructure( quo_kC ) and IsEquippedWithHomomorphismStructure( quo_kC ) then
        
        SetRangeCategoryOfHomomorphismStructure( quo_k_quo_C, RangeCategoryOfHomomorphismStructure( quo_kC ) );
        
    fi;
    
    INSTALL_CANONICAL_REPRESENTATIVE_METHODS_IN_QUOTIENT_CATEGORIES_OF_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( quo_k_quo_C );
    INSTALL_VIEW_AND_DISPLAY_METHODS_IN_QUOTIENT_CATEGORIES_OF_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( quo_k_quo_C );
    
    Finalize( quo_k_quo_C );
    
    return quo_k_quo_C;
    
end );

##
InstallOtherMethod( \/,
        [ IsLinearClosure, IsDenseList ],
  
  QuotientCategory
);

##
InstallOtherMethod( DataTablesOfCategory,
          [ IsQuotientCapCategory ],
  
  function ( quo_kC )
    local kC, C, all_objs, support_objs, objs, all_gmors, support_gmors, gmors, q;
    
    if not HasRangeCategoryOfHomomorphismStructure( quo_kC ) then
        Error( "the linear closure category passed to 'DataTablesOfCategory' must be hom-finite!" );
    fi;
    
    kC := UnderlyingCategory( quo_kC );
    
    if not IsLinearClosure( kC ) then
        
        TryNextMethod( );
        
    fi;
    
    C := UnderlyingCategory( kC );
    
    if not (IsPathCategory( C ) or IsQuotientOfPathCategory( C ))  then
        
        TryNextMethod( );
        
    fi;
    
    all_objs := SetOfObjects( quo_kC );
    support_objs := PositionsProperty( all_objs, o -> not IsZero( o ) );
    objs := all_objs{support_objs};
    
    all_gmors := SetOfGeneratingMorphisms( quo_kC );
    support_gmors := PositionsProperty( all_gmors, m -> not IsZero( m ) );
    gmors := all_gmors{support_gmors};
    
    q := UnderlyingQuiver( C );
    
    if Length( objs ) <> Length( all_objs ) or Length( gmors ) <> Length( all_gmors ) then
      
      q := FinQuiver(
              NTuple( 3,
                "q",
                NTuple( 3,
                  Length( support_objs ),
                  LabelsOfObjects( q ){support_objs},
                  LaTeXStringsOfObjects( q ){support_objs} ),
                NTuple( 5,
                  Length( support_gmors ),
                  List( IndicesOfSources( q ){support_gmors}, s -> SafePosition( support_objs, s ) ),
                  List( IndicesOfTargets( q ){support_gmors}, t -> SafePosition( support_objs, t ) ),
                  LabelsOfMorphisms( q ){support_gmors},
                  LaTeXStringsOfMorphisms( q ){support_gmors} ) ) );
      
    fi;
    
    return
      NTuple( 5,
      
      #coefficients_ring,
      UnderlyingRing( kC ),
      
      #quiver
      q,
      
      #decomposition_indices_of_bases_elements
      List( objs, s -> List( objs, t -> List( BasisOfExternalHom( quo_kC, s, t ), m ->
        List( MorphismIndices( CanonicalRepresentative( SupportMorphisms( CanonicalRepresentative( m ) )[1] ) ), index -> Position( support_gmors, index ) ) ) ) ),
      
      # hom_structure_objs_gmors
      List( objs, o -> List( gmors, gm ->
        EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( HomomorphismStructureOnMorphisms( quo_kC, IdentityMorphism( quo_kC, o ), gm ) ) ) ) ),
      
      #hom_structure_gmors_objs
      List( objs, o -> List( gmors, gm ->
        EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( HomomorphismStructureOnMorphisms( quo_kC, gm, IdentityMorphism( quo_kC, o ) ) ) ) ) ) );

end );

##
InstallGlobalFunction( INSTALL_CANONICAL_REPRESENTATIVE_METHODS_IN_QUOTIENT_CATEGORIES_OF_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS,
  
  function ( quo_cat )
    
    if IsPathCategory( UnderlyingCategory( UnderlyingCategory( quo_cat ) ) ) then
        
        ##
        InstallOtherMethod( CanonicalRepresentative,
                [ MorphismFilter( quo_cat ) ],
          
          function ( mor )
            local quo_kC, kC;
            
            quo_kC := CapCategory( mor );
            
            kC := UnderlyingCategory( quo_kC );
            
            return ReductionOfMorphism( kC, MorphismDatum( quo_kC, mor ), GroebnerBasisOfDefiningRelations( quo_kC ) );
            
        end );
        
    else
        
        ##
        InstallOtherMethod( CanonicalRepresentative,
                [ MorphismFilter( quo_cat ) ],
          
          function ( mor )
            local quo_k_quo_C, quo_kC, source, target;
            
            quo_k_quo_C := CapCategory( mor );
            
            quo_kC := ModelingCategory( quo_k_quo_C );
            
            source := ModelingObject( quo_k_quo_C, Source( mor ) );
            target := ModelingObject( quo_k_quo_C, Target( mor ) );
            
            return ModelingTowerMorphismDatum( quo_k_quo_C,
                      MorphismConstructor( quo_kC, source, CanonicalRepresentative( ModelingMorphism( quo_k_quo_C, mor ) ), target ) );
            
        end );
        
    fi;
    
end );

##
InstallGlobalFunction( INSTALL_VIEW_AND_DISPLAY_METHODS_IN_QUOTIENT_CATEGORIES_OF_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS,
  
  function ( quo_cat )
    local q, C;
    
    C := UnderlyingCategory( UnderlyingCategory( quo_cat ) );
    
    if IsPathCategory( C ) then
      
      q := UnderlyingQuiver( C );
      
    else
      
      q := UnderlyingQuiver( UnderlyingCategory( C ) );
      
    fi;
    
    ##
    InstallMethod( DisplayString,
              [ ObjectFilter( quo_cat ) ],
    
     o -> Concatenation( ViewString( o ), "\n" ) );
    
    ##
    InstallMethod( ViewString,
              [ ObjectFilter( quo_cat ) ],
      
      function ( obj )
        
        return ViewString( ObjectDatum( obj ) );
        
    end );
    
    ##
    InstallMethod( DisplayString,
              [ MorphismFilter( quo_cat ) ],
    
    m -> Concatenation( ViewString( m ), "\n" ) );
    
    ##
    InstallMethod( ViewString,
              [ MorphismFilter( quo_cat ) ],
      function ( mor )
        local colors, string;
        
        colors := q!.colors;
        
        string := ViewString( CanonicalRepresentative( mor ) );
        string := Concatenation( "[", string );
        return ReplacedString(
                  string,
                  Concatenation( colors!.other, ":" ),
                  Concatenation( colors.reset, "]", colors.other, ":") );
        
    end );
    
end );
