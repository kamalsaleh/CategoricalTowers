




##
InstallOtherMethod( \/,
        [ IsLinearClosure, IsDenseList ],
  
  QuotientCategory
);

##
InstallOtherMethod( QuotientCategory,
        [ IsLinearClosure, IsDenseList ],
        
  function ( k_C, relations )
    local C, Q, reduced_groebner_basis, leading_monomials, congruence_function, name, q_k_C, FinalizeCategory, homQ, range_cat;
    
    C := UnderlyingCategory( k_C );
    
    Q := CapQuiver( C );
    
    if not IsPathCategory( C ) then
        TryNextMethod( );
    fi;
    
    reduced_groebner_basis := REDUCED_GROEBNER_BASIS_IN_LINEAR_CLOSURE_OF_PATH_CATEGORY( k_C, GROEBNER_BASIS_IN_LINEAR_CLOSURE_OF_PATH_CATEGORY( k_C, relations ) );
    
    leading_monomials := List( reduced_groebner_basis, g -> SupportMorphisms( g )[1] );
    
    congruence_function := m -> IsZeroForMorphisms( k_C, ReductionOfMorphism( k_C, m, reduced_groebner_basis ) );
    
    name := List( relations{[ 1 .. Minimum( 3, Length( relations ) )]},
                  function ( rel )
                    local str;
                    
                    str := ViewString( rel );
                    
                    str := str{[ 1 .. PositionSublist( str, ":" ) - 1 ]};
                    
                    if not IsEmpty( Q!.colors.mor ) then
                      str := ReplacedString( str, Q!.colors.mor, "" );
                    fi;
                    
                    if not IsEmpty( Q!.colors.reset ) then
                      str := ReplacedString( str, Q!.colors.reset, "" );
                    fi;
                    
                    if not IsEmpty( Q!.colors.other ) then
                      str := ReplacedString( str, Q!.colors.other, "" );
                    fi;
                    
                    if not IsEmpty( k_C!.colors!.coeff ) then
                      str := ReplacedString( str, k_C!.colors!.coeff, "" );
                    fi;
                    
                    if not IsEmpty( k_C!.colors!.reset ) then
                      str := ReplacedString( str, k_C!.colors!.reset, "" );
                    fi;
                    
                    return str;
                    
                  end );
    
    if Length( relations ) > 3 then
      Add( name, "..." );
    fi;
    
    name := Concatenation( Name( k_C ), " / [ ", JoinStringsWithSeparator( name, ", " ), " ]" );
    
    q_k_C := QuotientCategory(
                           rec( name := name,
                                nr_arguments_of_congruence_function := 1,
                                congruence_function := congruence_function,
                                underlying_category := k_C ) : FinalizeCategory := false );
    
    q_k_C!.underlying_two_sided_ideal := rec( generators := relations, reduced_groebner_basis := reduced_groebner_basis );

    SetSetOfObjects( q_k_C, List( SetOfObjects( k_C ), o -> ObjectConstructor( q_k_C, o ) ) );
    
    SetSetOfGeneratingMorphisms( q_k_C,
            List( SetOfGeneratingMorphisms( k_C ),
              m -> MorphismConstructor( q_k_C,
                        SetOfObjects( q_k_C )[ObjectIndex( UnderlyingOriginalObject( Source( m ) ) )],
                        m,
                        SetOfObjects( q_k_C )[ObjectIndex( UnderlyingOriginalObject( Target( m ) ) )] ) ) );

    # Hom-Structure
    
    if HasFiniteNumberOfNonMultiples( C, leading_monomials ) then
        
        homQ := ExternalHoms( C, leading_monomials );
        
        SetExternalHoms( q_k_C,
              LazyHList( [ 1 .. NumberOfObjects( Q ) ],
                s -> LazyHList( [ 1 .. NumberOfObjects( Q ) ],
                  t -> List( homQ[s][t],
                    m -> MorphismConstructor( q_k_C,
                              SetOfObjects( q_k_C )[s],
                              MorphismConstructor( k_C, SetOfObjects( k_C )[s], Pair( [ One( UnderlyingRing( k_C ) ) ], [ m ] ), SetOfObjects( k_C )[t] ),
                              SetOfObjects( q_k_C )[t] ) ) ) ) );

        if (HasIsEquippedWithHomomorphismStructure and IsEquippedWithHomomorphismStructure)( k_C ) then
            
            range_cat := RangeCategoryOfHomomorphismStructure( k_C );
            
        else
            
            range_cat := CategoryOfRows( UnderlyingRing( k_C ) );
            
        fi;
        
        SetIsEquippedWithHomomorphismStructure( q_k_C, true );
        
        SetRangeCategoryOfHomomorphismStructure( q_k_C, range_cat );
        
        ##
        AddBasisOfExternalHom( q_k_C,
          function ( q_k_C, obj_1, obj_2 )
            local s, t;
            
            s := ObjectIndex( UnderlyingOriginalObject( ObjectDatum( obj_1 ) ) );
            t := ObjectIndex( UnderlyingOriginalObject( ObjectDatum( obj_2 ) ) );
            
            return ExternalHoms( q_k_C )[s][t];
            
        end );
        
        ##
        AddCoefficientsOfMorphism( q_k_C,
          function ( q_k_C, mor )
            local s, t;
            
            s := ObjectIndex( UnderlyingOriginalObject( ObjectDatum( Source( mor ) ) ) );
            t := ObjectIndex( UnderlyingOriginalObject( ObjectDatum( Target( mor ) ) ) );
            
            mor := ReductionOfMorphism( k_C, MorphismDatum( mor ), q_k_C!.underlying_two_sided_ideal!.reduced_groebner_basis );
            
            return List( ExternalHoms( q_k_C )[s][t],
                                function ( m )
                                  local p;
                                  
                                  p := Position( SupportMorphisms( mor ), SupportMorphisms( MorphismDatum( m ) )[1] );
                                  
                                  if p = fail then
                                      return Zero( UnderlyingRing( k_C ) );
                                  else
                                      return CoefficientsList( mor )[p];
                                  fi;
                                  
                                end );
            
        end );
    fi;
    
    INSTALL_DISPLAY_AND_VIEW_METHODS_FOR_QUOTIENT_OF_LINEAR_CATEGORY( q_k_C );
    
    Finalize( q_k_C );
    
    return q_k_C;
    
end );

##
InstallOtherMethod( QuotientCategory,
        [ IsLinearClosure, IsDenseList ],
        
  function ( k_q_C, relations )
    local q_C, k, C, Q, k_C, overhead, rel_1, rel_2, new_relations, modeling_cat, object_constructor, object_datum, morphism_constructor, morphism_datum,
    modeling_tower_object_constructor, modeling_tower_object_datum, modeling_tower_morphism_constructor, modeling_tower_morphism_datum, q_k_q_C,
    category_filter, category_object_filter, category_morphism_filter;
    
    q_C := UnderlyingCategory( k_q_C );
    
    if not IsQuotientOfPathCategory( q_C ) then
        TryNextMethod( );
    fi;
    
    k := UnderlyingRing( k_q_C );
    
    C := UnderlyingCategory( q_C );
    
    Q := CapQuiver( C );
    
    k_C := LinearClosure( k, C : overhead := false );
    
    rel_1 :=
      List( GroebnerBasisOfDefiningRelations( q_C ),
              m -> MorphismConstructor( k_C,
                      SetOfObjects( k_C )[ObjectIndex( Source( m[1] ) )],
                      Pair( [ One( k ), MinusOne( k ) ], m ),
                      SetOfObjects( k_C )[ObjectIndex( Target( m[1] ) )] ) );

    rel_2 :=
      List( relations,
              m -> MorphismConstructor( k_C,
                      SetOfObjects( k_C )[ObjectIndex( ObjectDatum( UnderlyingOriginalObject( Source( m ) ) ) )],
                      Pair( CoefficientsList( m ), List( SupportMorphisms( m ), CanonicalRepresentative ) ),
                      SetOfObjects( k_C )[ObjectIndex( ObjectDatum( UnderlyingOriginalObject( Target( m ) ) ) )] ) );
    
    new_relations := Concatenation( rel_1, rel_2 );
    
    modeling_cat := QuotientCategory( k_C, new_relations );
    
    object_constructor := { q_k_q_C, obj } -> CreateCapCategoryObjectWithAttributes( q_k_q_C, UnderlyingCell, obj );
    
    object_datum := { q_k_q_C, obj } -> UnderlyingCell( obj );
    
    morphism_constructor := { q_k_q_C, S, mor, T } -> CreateCapCategoryMorphismWithAttributes( q_k_q_C, S, T, UnderlyingCell, mor );
    
    morphism_datum := { q_k_q_C, mor } -> UnderlyingCell( mor );
    
    ## from the raw object data to the object in the highest stage of the tower
    modeling_tower_object_constructor :=
      function ( q_k_q_C, datum )
        local modeling_cat, k_q_C, q_C, C, Q, i;
        
        modeling_cat := ModelingCategory( q_k_q_C );
        
        k_q_C := UnderlyingCategory( q_k_q_C );
        
        q_C := UnderlyingCategory( k_q_C );
        
        C := UnderlyingCategory( q_C );
        
        Q := CapQuiver( C );
        
        i := ObjectDatum( Q, ObjectDatum( C, ObjectDatum( q_C, UnderlyingOriginalObject( datum ) ) ) );
        
        return SetOfObjects( modeling_cat )[i];
        
    end;
    
    ## from the object in the highest stage of the tower to the raw object datum
    modeling_tower_object_datum :=
      function ( q_k_q_C, obj )
        local modeling_cat, k_q_C, q_C, C, Q, i;
        
        modeling_cat := ModelingCategory( q_k_q_C );
        
        k_q_C := UnderlyingCategory( q_k_q_C );
        
        q_C := UnderlyingCategory( k_q_C );
        
        C := UnderlyingCategory( q_C );
        
        Q := CapQuiver( C );

        i := ObjectDatum( Q, ObjectDatum( C, UnderlyingOriginalObject( ObjectDatum( modeling_cat, obj ) ) ) );
        
        return ObjectConstructor( q_k_q_C, SetOfObjects( UnderlyingCategory( q_k_q_C ) )[i] );
        
    end;
    
    ## from the raw morphism datum to the morphism in the highest stage of the tower
    modeling_tower_morphism_constructor :=
      function ( q_k_q_C, S, datum, T )
        local modeling_cat, coeffs, suppor;
        
        modeling_cat := ModelingCategory( q_k_q_C );
        
        coeffs := CoefficientsList( datum );
        suppor := List( SupportMorphisms( datum ), CanonicalRepresentative );
        
        return MorphismConstructor( modeling_cat,
                      S,
                      MorphismConstructor( UnderlyingCategory( modeling_cat ), ObjectDatum( modeling_cat, S ), Pair( coeffs, suppor ), ObjectDatum( modeling_cat, T ) ),
                      T );
        
    end;
    
    ## from the morphism in the highest stage of the tower to the raw morphism datum
    modeling_tower_morphism_datum :=
      function ( q_k_q_C, mor )
        local modeling_cat, k_q_C, q_C, C, Q, s, t, coeffs, suppor;
        
        modeling_cat := ModelingCategory( q_k_q_C );
        
        k_q_C := UnderlyingCategory( q_k_q_C );
        
        q_C := UnderlyingCategory( k_q_C );
        
        C := UnderlyingCategory( q_C );
        
        Q := CapQuiver( C );
        
        s := ObjectDatum( Q, ObjectDatum( C, UnderlyingOriginalObject( ObjectDatum( modeling_cat, Source( mor ) ) ) ) );
        t := ObjectDatum( Q, ObjectDatum( C, UnderlyingOriginalObject( ObjectDatum( modeling_cat, Target( mor ) ) ) ) );
        
        coeffs := CoefficientsList( MorphismDatum( mor ) );
        suppor := List( SupportMorphisms( MorphismDatum( mor ) ), m -> MorphismConstructor( q_C, SetOfObjects( q_C )[s], m, SetOfObjects( q_C )[t] ) );
        
        return MorphismConstructor( k_q_C, SetOfObjects( k_q_C )[s], Pair( coeffs, suppor ), SetOfObjects( k_q_C )[t] );
        
    end;
    
    name := List( relations{[ 1 .. Minimum( 3, Length( relations ) )]},
                  function ( rel )
                    local str;
                    
                    str := ViewString( rel );
                    
                    str := str{[ 1 .. PositionSublist( str, ":" ) - 1 ]};
                    
                    if not IsEmpty( Q!.colors.mor ) then
                      str := ReplacedString( str, Q!.colors.mor, "" );
                    fi;
                    
                    if not IsEmpty( Q!.colors.reset ) then
                      str := ReplacedString( str, Q!.colors.reset, "" );
                    fi;
                    
                    if not IsEmpty( Q!.colors.other ) then
                      str := ReplacedString( str, Q!.colors.other, "" );
                    fi;
                    
                    if not IsEmpty( k_q_C!.colors!.coeff ) then
                      str := ReplacedString( str, k_C!.colors!.coeff, "" );
                    fi;
                    
                    if not IsEmpty( k_q_C!.colors!.reset ) then
                      str := ReplacedString( str, k_C!.colors!.reset, "" );
                    fi;
                    
                    return str;
                    
                  end );
    
    if Length( relations ) > 3 then
      Add( name, "..." );
    fi;
    
    name := Concatenation( Name( k_q_C ), " / [ ", JoinStringsWithSeparator( name, ", " ), " ]" );
 
    ##
    q_k_q_C :=
        ReinterpretationOfCategory( modeling_cat,
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
    
    q_k_q_C!.is_computable := true;
    
    SetUnderlyingCategory( q_k_q_C, k_q_C );
    
    if IsEquippedWithHomomorphismStructure( k_q_C ) then
        
        SetRangeCategoryOfHomomorphismStructure( q_k_q_C, RangeCategoryOfHomomorphismStructure( k_q_C ) );
        
    fi;
    
    INSTALL_DISPLAY_AND_VIEW_METHODS_FOR_QUOTIENT_OF_LINEAR_CATEGORY( q_k_q_C );
    
    Finalize( q_k_q_C );
    
    return q_k_q_C;
    
end );

##
InstallGlobalFunction( INSTALL_DISPLAY_AND_VIEW_METHODS_FOR_QUOTIENT_OF_LINEAR_CATEGORY,
  
  function ( qtient_cat )
    local U;
    
    U := UnderlyingCategory( UnderlyingCategory( qtient_cat ) );
    
    if IsPathCategory( U ) then
        
        ##
        InstallOtherMethod( CanonicalRepresentative,
                [ MorphismFilter( qtient_cat ) ],
          
          function ( mor )
            local reduced_groebner_basis;
            
            reduced_groebner_basis := qtient_cat!.underlying_two_sided_ideal!.reduced_groebner_basis;
             
            return ReductionOfMorphism( UnderlyingCategory( qtient_cat ), MorphismDatum( mor ), qtient_cat!.underlying_two_sided_ideal!.reduced_groebner_basis );
            
        end );
        
    elif IsQuotientOfPathCategory( U ) then
        
        U := UnderlyingCategory( U );
        
        ##
        InstallOtherMethod( CanonicalRepresentative,
                [ MorphismFilter( qtient_cat ) ],
          
          function ( mor )
            local q_k_q_C, MC, S, T;
            
            q_k_q_C := CapCategory( mor );
            
            MC := ModelingCategory( q_k_q_C );
            
            S := ModelingObject( q_k_q_C, Source( mor ) );
            T := ModelingObject( q_k_q_C, Target( mor ) );
            
            return ModelingTowerMorphismDatum( q_k_q_C, MorphismConstructor( MC, S, CanonicalRepresentative( ModelingMorphism( q_k_q_C, mor ) ), T ) );
            
        end );
        
    fi;
    
    ##
    InstallMethod( DisplayString,
              [ ObjectFilter( qtient_cat ) ],
    
     o -> Concatenation( ViewString( o ), "\n" ) );
    
    ##
    InstallMethod( ViewString,
              [ ObjectFilter( qtient_cat ) ],
      function ( obj )
        
        return ViewString( ObjectDatum( obj ) );
        
    end );
    
    ##
    InstallMethod( DisplayString,
              [ MorphismFilter( qtient_cat ) ],
    
    m -> Concatenation( ViewString( m ), "\n" ) );
    
    ##
    InstallMethod( ViewString,
              [ MorphismFilter( qtient_cat ) ],
      function ( mor )
        local colors, string;
        
        colors := CapQuiver( U )!.colors;
        
        string := ViewString( CanonicalRepresentative( mor ) );
        string := Concatenation( "[", string );
        string := ReplacedString( string, Concatenation( colors!.other, ":" ), Concatenation( colors.reset, "]", colors.other, ":") );
        
        return string;
        
    end );
    
end );

#######################
#
# Division Algorithm
#
#######################


## If G ist not a Groebner Basis, then the reduction might differ for different shuffles of G
##
## C := PathCategory( "q(o)[x:o->o,y:o->o,z:o->o]" : colors := true );
## ReductionOfMorphism( C, C.xxyyxy, [ [ C.xx, C.xy ], [ C.xyyx, C.xyyy ], [ C.x^5, C.y^5 ] ] );
## #! <x•y^3•x•y:(o) -≻ (o)>
## ReductionOfMorphism( C, C.xxyyxy, [ [ C.xyyx, C.xyyy ], [ C.xx, C.xy ], [ C.x^5, C.y^5 ] ] );
## #! <x•y^5:(o) -≻ (o)>

## the output is a morphism
##
InstallMethod( ReductionOfMorphism,
          [ IsLinearClosure, IsLinearClosureMorphism, IsDenseList ],
          
  function ( k_C, f, G )
    local C, Q, one, S, T, lC_G, lM_G, lM_G_datum, r, lC_f, lM_f, lM_f_datum, i, p, c_i, u_i, v_i, t, lT_f;
    
    C := UnderlyingCategory( k_C );
    Q := CapQuiver( C );
    
    one := One( UnderlyingRing( k_C ) );
    
    S := Source( f );
    T := Target( f );
    
    #c := List( G, g -> [] );
    #u := List( G, g -> [] );
    #v := List( G, g -> [] );
    
    lC_G := List( G, g -> CoefficientsList( g )[1] );
    lM_G := List( G, g -> SupportMorphisms( g )[1] );
    lM_G_datum := List( lM_G, m -> Pair( MorphismLength( m ), List( MorphismSupport( m ), MorphismIndex ) ) );
    
    r := ZeroMorphism( k_C, S, T );
    
    while not IsZeroForMorphisms( k_C, f ) do
        
        lC_f := CoefficientsList( f )[1];
        lM_f := SupportMorphisms( f )[1];
        lM_f_datum := Pair( MorphismLength( lM_f ), List( MorphismSupport( lM_f ), MorphismIndex ) );
        
        i := PositionProperty( lM_G_datum, datum -> PositionSublist( lM_f_datum[2], datum[2] ) <> fail );
        
        if i <> fail then
            
            p := PositionSublist( lM_f_datum[2], lM_G_datum[i][2] );
            
            c_i := lC_f / lC_G[i];
            
            u_i := MorphismConstructor( C,
                            UnderlyingOriginalObject( S ),
                            Pair( p - 1, SetOfMorphisms( Q ){lM_f_datum[2]{[ 1 .. p - 1 ]}} ),
                            UnderlyingOriginalObject( Source( G[i] ) ) );
            
            u_i := MorphismConstructor( k_C, S, Pair( [ one ], [ u_i ] ), Source( G[i] ) );
            
            v_i := MorphismConstructor( C,
                            UnderlyingOriginalObject( Target( G[i] ) ),
                            Pair( lM_f_datum[1] - p - lM_G_datum[i][1] + 1, SetOfMorphisms( Q ){lM_f_datum[2]{[ p + lM_G_datum[i][1] .. lM_f_datum[1] ]}} ),
                            UnderlyingOriginalObject( T ) );

            v_i := MorphismConstructor( k_C, Target( G[i] ), Pair( [ one ], [ v_i ] ), T );

            #Add( c[i], c_i );
            #Add( u[i], u_i );
            #Add( v[i], v_i );
            
            t := MultiplyWithElementOfCommutativeRingForMorphisms( k_C, c_i, PreComposeList( k_C, [ u_i, G[i], v_i ] ) );
            f := SubtractionForMorphisms( k_C, f, t );
            
        else
            
            lT_f := MorphismConstructor( k_C, S, Pair( [ lC_f ], [ lM_f ] ), T );
            
            r := AdditionForMorphisms   ( k_C, r, lT_f );
            f := SubtractionForMorphisms( k_C, f, lT_f );
            
        fi;
        
    od;
    
    return r; # c, u, v
    
end );

##
InstallMethod( NewRelation,
          [ IsLinearClosure, IsLinearClosureMorphism, IsLinearClosureMorphism, IsDenseList ],
  
  function ( k_C, g, h, overlap_coeffs )
    local C, one, lM_g, lM_h, l_lM_g, r_lM_g, l_lM_h, r_lM_h, lC_g, lC_h;
    
    C := UnderlyingCategory( k_C );
    
    one := One( UnderlyingRing( k_C ) );
    
    lM_g := SupportMorphisms( g )[1];
    lM_h := SupportMorphisms( h )[1];
    
    l_lM_g := MorphismConstructor( k_C, SetOfObjects( k_C )[ObjectIndex( Source( overlap_coeffs[1][1] ) )], Pair( [ one ], [ overlap_coeffs[1][1] ] ), Source( g ) );
    r_lM_g := MorphismConstructor( k_C, Target( g ), Pair( [ one ], [ overlap_coeffs[1][2] ] ), SetOfObjects( k_C )[ObjectIndex( Target( overlap_coeffs[1][2] ) )] );
    
    l_lM_h := MorphismConstructor( k_C, SetOfObjects( k_C )[ObjectIndex( Source( overlap_coeffs[2][1] ) )], Pair( [ one ], [ overlap_coeffs[2][1] ] ), Source( h ) );
    r_lM_h := MorphismConstructor( k_C, Target( h ), Pair( [ one ], [ overlap_coeffs[2][2] ] ), SetOfObjects( k_C )[ObjectIndex( Target( overlap_coeffs[2][2] ) )] );
    
    lC_g := CoefficientsList( g )[1];
    lC_h := CoefficientsList( h )[1];
    
    return SubtractionForMorphisms( k_C,
                MultiplyWithElementOfCommutativeRingForMorphisms( k_C, Inverse( lC_g ), PreComposeList( k_C, [ l_lM_g, g, r_lM_g ] ) ),
                MultiplyWithElementOfCommutativeRingForMorphisms( k_C, Inverse( lC_h ), PreComposeList( k_C, [ l_lM_h, h, r_lM_h ] ) ) );
    
end );

##
InstallGlobalFunction( GROEBNER_BASIS_IN_LINEAR_CLOSURE_OF_PATH_CATEGORY,
          #[ IsLinearClosure, IsDenseList ],
          
  function ( k_C, relations )
    local C, groebner_basis, indices, rels, i, g, new_indices, new_rels;
    
    C := UnderlyingCategory( k_C );
    
    # Compute a Gröbner basis
    
    groebner_basis := ShallowCopy( relations );
    
    indices := Concatenation( List( [ 1 .. Length( groebner_basis ) ], i -> [ i, i ] ), Combinations( [ 1 .. Length( groebner_basis ) ], 2 ) );
    
    rels := Concatenation( List( indices,
                                i -> List( OverlappingCoefficients( C,
                                              SupportMorphisms( groebner_basis[i[1]] )[1], SupportMorphisms( groebner_basis[i[2]] )[1] ),
                                                  overlap_coeffs -> NewRelation( k_C, groebner_basis[i[1]], groebner_basis[i[2]], overlap_coeffs ) ) ) );
    
    i := 1;
    
    while i <= Length( rels ) do
        
        if not IsZeroForMorphisms( k_C, rels[i] ) then
            
            g := ReductionOfMorphism( k_C, rels[i], groebner_basis );
            
            if not IsZeroForMorphisms( k_C, g ) then
              
              Add( groebner_basis, Inverse( CoefficientsList( g )[1] ) * g ); # one can also add g without normalization
              
              new_indices := List( [ 1 .. Length( groebner_basis ) ], i -> [ i, Length( groebner_basis ) ] );
              
              new_rels := Concatenation(
                            List( new_indices,
                                i -> List( OverlappingCoefficients( C,
                                              SupportMorphisms( groebner_basis[i[1]] )[1], SupportMorphisms( groebner_basis[i[2]] )[1] ),
                                                  overlap_coeffs -> NewRelation( k_C, groebner_basis[i[1]], groebner_basis[i[2]], overlap_coeffs ) ) ) );
              
              rels := Concatenation( rels, new_rels );
              
            fi;
            
        fi;
        
        i := i + 1;
        
    od;
    
    return groebner_basis;
    
end );

##
InstallGlobalFunction( REDUCED_GROEBNER_BASIS_IN_LINEAR_CLOSURE_OF_PATH_CATEGORY,
  
  function ( k_C, groebner_basis )
    local reduced_groebner_basis, i, r;
    
    reduced_groebner_basis := ShallowCopy( groebner_basis );
    
    i := 1;
    
    while i <= Length( reduced_groebner_basis ) do
      
      r := ReductionOfMorphism( k_C, reduced_groebner_basis[i], reduced_groebner_basis{Difference( [ 1 .. Length( reduced_groebner_basis ) ], [ i ] )} );
      
      if IsZeroForMorphisms( k_C, r ) then
          
          Remove( reduced_groebner_basis, i );
          
      elif not IsEqualForMorphisms( k_C, r, reduced_groebner_basis[i] ) then
          
          reduced_groebner_basis[i] := MultiplyWithElementOfCommutativeRingForMorphisms( k_C, Inverse( CoefficientsList( r )[1] ), r );
          
          i := 1;
          
      else
          
          i := i + 1;
          
      fi;
      
    od;
    
    return reduced_groebner_basis;
    
end );

