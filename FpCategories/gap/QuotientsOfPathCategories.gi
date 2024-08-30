# SPDX-License-Identifier: GPL-2.0-or-later
# FpCategories: Finitely presented categories by generating quivers and relations
#
# Implementations
#

##
InstallGlobalFunction( QUOTIENT_CATEGORY_OF_PATH_CATEGORY,
  
  function ( C, relations )
    local groebner_basis, congruence_function, name, quo_C, q, has_finite_number_of_macaulay_morphisms, leading_monomials, macaulay_morphisms;
    
    groebner_basis := ValueOption( "groebner_basis" );
    
    if groebner_basis = fail then
        groebner_basis := GroebnerBasis( C, relations );
    fi;
    
    congruence_function :=
      { mor_1, mor_2 } -> IsEqualForMorphisms( C,
                              ReductionOfMorphism( C, mor_1, groebner_basis ),
                              ReductionOfMorphism( C, mor_2, groebner_basis ) );
    
    name := List( relations{[ 1 .. Minimum( 3, Length( relations ) ) ]},
              rel -> Concatenation( MorphismLabel( rel[1] ), " = ", MorphismLabel( rel[2] ) ) );
    
    if Length( relations ) > 3 then
          Add( name, "..." );
    fi;
    
    name := Concatenation( Name( C ), " / [ ", JoinStringsWithSeparator( name, ", " ), " ]" );
    
    quo_C := QuotientCategory(
                rec( name := name,
                     category_filter := IsQuotientOfPathCategory,
                     category_object_filter := IsQuotientOfPathCategoryObject,
                     category_morphism_filter := IsQuotientOfPathCategoryMorphism,
                     nr_arguments_of_congruence_function := 2,
                     congruence_function := congruence_function,
                     underlying_category := C ) : FinalizeCategory := false, overhead := false );
    
    ##
    AddSetOfGeneratingMorphismsOfCategory( quo_C,
      function( quo_C )
        local objects;

        objects := SetOfObjects( quo_C );
        
        return List( SetOfGeneratingMorphisms( UnderlyingCategory( quo_C ) ),
                     m -> MorphismConstructor( quo_C,
                             objects[ObjectIndex( Source( m ) )],
                             m,
                             objects[ObjectIndex( Target( m ) )] ) );
        
    end );
    
    q := UnderlyingQuiver( C );
    
    SetUnderlyingQuiver( quo_C, q );
    
    SetDefiningTripleOfUnderlyingQuiver( quo_C, DefiningTripleOfUnderlyingQuiver( C ) );
    
    SetDefiningRelations( quo_C, relations );
    
    SetGroebnerBasisOfDefiningRelations( quo_C, groebner_basis );
    
    has_finite_number_of_macaulay_morphisms := ValueOption( "has_finite_number_of_macaulay_morphisms" );
    
    if has_finite_number_of_macaulay_morphisms = fail then
        
        leading_monomials := List( groebner_basis, g -> g[1] );
        
        has_finite_number_of_macaulay_morphisms := HasFiniteNumberOfMacaulayMorphisms( C, leading_monomials );
        
    fi;
    
    if has_finite_number_of_macaulay_morphisms then
        
        SetIsFiniteCategory( quo_C, true );
        
        macaulay_morphisms := ValueOption( "macaulay_morphisms" );
        
        if macaulay_morphisms = fail then
            
            macaulay_morphisms := MacaulayMorphisms( C, leading_monomials );
            
        fi;
        
        SetExternalHoms( quo_C,
              LazyHList( [ 1 .. NumberOfObjects( q ) ],
                s -> LazyHList( [ 1 .. NumberOfObjects( q ) ],
                  t -> List( macaulay_morphisms[s][t],
                    m -> MorphismConstructor( quo_C,
                              SetOfObjects( quo_C )[s],
                              m,
                              SetOfObjects( quo_C )[t] ) ) ) ) );

        
        SET_RANGE_CATEGORY_Of_HOMOMORPHISM_STRUCTURE( quo_C, SkeletalFinSets );
        
        ##
        AddMorphismsOfExternalHom( quo_C,
          function ( quo_C, obj_1, obj_2 )
            local s, t;
            
            s := ObjectIndex( ObjectDatum( quo_C, obj_1 ) );
            t := ObjectIndex( ObjectDatum( quo_C, obj_2 ) );
            
            return ExternalHoms( quo_C )[s][t];
            
        end );
        
    fi;
    
    quo_C!.compiler_hints.category_attribute_names :=
      [ "UnderlyingQuiver",
        "DefiningTripleOfUnderlyingQuiver",
        ];
    
    Finalize( quo_C );
    
    return quo_C;
    
end );

##
InstallOtherMethod( QuotientCategory,
        [ IsPathCategory, IsDenseList ],
  
  function ( C, relations )
    local reduced_gb;
    
    reduced_gb := ReducedGroebnerBasis( C, relations );
    
    return QUOTIENT_CATEGORY_OF_PATH_CATEGORY( C, relations : groebner_basis := reduced_gb );
    
end );

##
InstallOtherMethod( \/,
        [ IsPathCategory, IsDenseList ],
  
  QuotientCategory
);

##
InstallMethod( TensorProductOfPathCategories,
          [ IsPathCategory, IsPathCategory ],
  
  function ( C1, C2 )
    local q1, q2, quiver_datum_1, quiver_datum_2, q1xq2, admissible_order, C, gmors_C, rels, C1xC2;
    
    q1 := UnderlyingQuiver( C1 );
    q2 := UnderlyingQuiver( C2 );
    
    quiver_datum_1 := QuiverDatum( q1 );
    quiver_datum_2 := QuiverDatum( q2 );
    
    q1xq2 := TensorProductOfFinQuivers( q1, q2 );
    
    admissible_order := C1!.admissible_order;
    
    if not admissible_order = C2!.admissible_order then
        Error( "the passed categories must have the same 'admissible_order'\n" );
    fi;
    
    C := PathCategory( q1xq2 : admissible_order := admissible_order );
    
    gmors_C := SetOfGeneratingMorphisms( C );
    
    # for every pair of generating morphisms f:A -> B and u:X -> Y
    # we need the relation:
    #
    #          A⊗X
    #         /   \
    #    f⊗X /     \ A⊗u
    #       V       V
    #     B⊗X       A⊗Y
    #       \       /
    #    B⊗u \     / f⊗Y
    #         V   V
    #          B⊗Y
    
    if C!.admissible_order = "Dp" then
      
      rels :=
          Concatenation(
            List( [ 1 .. quiver_datum_1[3][1] ], i ->
              List( [ 1 .. quiver_datum_2[3][1] ], j ->
                Pair(
                  PreCompose( C,
                    gmors_C[(quiver_datum_1[3][2][i] - 1) * quiver_datum_2[3][1] + j],
                    gmors_C[quiver_datum_1[2][1] * quiver_datum_2[3][1] + (i-1) * quiver_datum_2[2][1] + quiver_datum_2[3][3][j]] ),
                  PreCompose( C,
                    gmors_C[quiver_datum_1[2][1] * quiver_datum_2[3][1] + (i-1) * quiver_datum_2[2][1] + quiver_datum_2[3][2][j]],
                    gmors_C[(quiver_datum_1[3][3][i] - 1) * quiver_datum_2[3][1] + j] ) ) ) ) );
      
    else
      
      rels :=
          Concatenation(
            List( [ 1 .. quiver_datum_1[3][1] ], i ->
              List( [ 1 .. quiver_datum_2[3][1] ], j ->
                Pair(
                  PreCompose( C,
                    gmors_C[quiver_datum_1[2][1] * quiver_datum_2[3][1] + (i-1) * quiver_datum_2[2][1] + quiver_datum_2[3][2][j]],
                    gmors_C[(quiver_datum_1[3][3][i] - 1) * quiver_datum_2[3][1] + j] ),
                  PreCompose( C,
                    gmors_C[(quiver_datum_1[3][2][i] - 1) * quiver_datum_2[3][1] + j],
                    gmors_C[quiver_datum_1[2][1] * quiver_datum_2[3][1] + (i-1) * quiver_datum_2[2][1] + quiver_datum_2[3][3][j]] ) ) ) ) );
      
    fi;
    
    C1xC2 := QUOTIENT_CATEGORY_OF_PATH_CATEGORY( C, rels : groebner_basis := rels );
    
    if IsAcyclicQuiver( q1xq2 ) then
        
        SetExternalHoms( C1xC2,
            Concatenation(
              List( [ 1 .. quiver_datum_1[2][1] ], i ->
                List( [ 1 .. quiver_datum_2[2][1] ], j ->
                  Concatenation(
                    List( [ 1 .. quiver_datum_1[2][1] ], m ->
                      List( [ 1 .. quiver_datum_2[2][1] ], n ->
                        Concatenation(
                          List( ExternalHoms( C1 )[i][m], l ->
                            List( ExternalHoms( C2 )[j][n], r ->
                              ElementaryTensor( l, r, C1xC2 ) ) ) ) ) ) ) ) ) ) );
        
    fi;
    
    INSTALL_SPECIAL_VIEW_STRING_FOR_MORPHISMS_IN_TENSOR_PRODUCT_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( C1xC2, C1, C2 );
    
    return C1xC2;
    
end );

##
InstallMethod( TensorProductOfQuotientsOfPathCategories,
        [ IsQuotientOfPathCategory, IsQuotientOfPathCategory ],
  
  function ( C1, C2 )
    local P1, nr_objs_1, P2, nr_objs_2, P1xP2, rels_0, rels_1, rels_2, rels, has_finite_number_of_macaulay_morphisms, macaulay_morphisms, C1xC2;
    
    P1 := UnderlyingCategory( C1 );
    nr_objs_1 := Length( SetOfObjects( P1 ) );
    
    P2 := UnderlyingCategory( C2 );
    nr_objs_2 := Length( SetOfObjects( P2 ) );
    
    P1xP2 := TensorProductOfPathCategories( P1, P2 );
    
    rels_0 := GroebnerBasisOfDefiningRelations( P1xP2 );
    
    rels_1 :=
      Concatenation(
        List( SetOfObjects( P1 ), o ->
          List( GroebnerBasisOfDefiningRelations( C2 ), r ->
            Pair( CanonicalRepresentative( ElementaryTensor( o, r[1], P1xP2 ) ), CanonicalRepresentative( ElementaryTensor( o, r[2], P1xP2 ) ) ) ) ) );
    
    rels_2 :=
      Concatenation(
        List( GroebnerBasisOfDefiningRelations( C1 ), r ->
          List( SetOfObjects( P2 ), o ->
            Pair( CanonicalRepresentative( ElementaryTensor( r[1], o, P1xP2 ) ), CanonicalRepresentative( ElementaryTensor( r[2], o, P1xP2 ) ) ) ) ) );
    
    rels := Concatenation( rels_0, rels_1, rels_2 );
    
    if IsFiniteCategory( C1 ) and IsFiniteCategory( C2 ) then
      
      has_finite_number_of_macaulay_morphisms := true;
      
      macaulay_morphisms :=
        Concatenation(
          List( [ 1 .. nr_objs_1 ], i ->
            List( [ 1 .. nr_objs_2 ], j ->
              Concatenation(
                List( [ 1 .. nr_objs_1 ], m ->
                  List( [ 1 .. nr_objs_2 ], n ->
                    Concatenation(
                      List( ExternalHoms( C1 )[i][m], l ->
                        List( ExternalHoms( C2 )[j][n], r ->
                          UnderlyingCell( ElementaryTensor( UnderlyingCell( l ), UnderlyingCell( r ), P1xP2 ) ) ) ) ) ) ) ) ) ) );
    else
      
      has_finite_number_of_macaulay_morphisms := false;
      
      macaulay_morphisms := fail;
      
    fi;
    
    C1xC2 := QUOTIENT_CATEGORY_OF_PATH_CATEGORY( UnderlyingCategory( P1xP2 ), rels
                : groebner_basis := rels,
                  has_finite_number_of_macaulay_morphisms := has_finite_number_of_macaulay_morphisms,
                  macaulay_morphisms := macaulay_morphisms );
    
    INSTALL_SPECIAL_VIEW_STRING_FOR_MORPHISMS_IN_TENSOR_PRODUCT_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( C1xC2, C1, C2 );
    
    return C1xC2;
    
end );

##
InstallOtherMethod( \*,
        [ IsPathCategory, IsPathCategory ],
  
  TensorProductOfPathCategories
);

##
InstallMethod( ElementaryTensor,
        [ IsPathCategoryObject, IsPathCategoryObject, IsQuotientOfPathCategory ],
  
  function ( obj_1, obj_2, C1_x_C2 )
    local q2;
    
    q2 := UnderlyingQuiver( CapCategory( obj_2 ) );
    
    return SetOfObjects( C1_x_C2 )[( ObjectIndex( obj_1 ) - 1 ) * NumberOfObjects( q2 ) + ObjectIndex( obj_2 )];
    
end );

##
InstallMethod( ElementaryTensor,
        [ IsPathCategoryObject, IsPathCategoryMorphism, IsQuotientOfPathCategory ],
  
  function ( obj, mor, C1_x_C2 )
    local q2, obj_index, mor_indices, indices, source, target;
    
    q2 := UnderlyingQuiver( CapCategory( mor ) );
    
    obj_index := ObjectIndex( obj );
    mor_indices := MorphismIndices( mor );
    
    indices := List( mor_indices, index -> (obj_index - 1) * NumberOfMorphisms( q2 ) + index );
    
    source := ElementaryTensor( obj, Source( mor ), C1_x_C2 );
    target := ElementaryTensor( obj, Target( mor ), C1_x_C2 );
    
    return MorphismConstructor( C1_x_C2,
              source,
              MorphismConstructor( UnderlyingCategory( C1_x_C2 ),
                  UnderlyingCell( source ),
                  Pair( Length( indices ), indices ),
                  UnderlyingCell( target )  ),
              target );
end );

##
InstallMethod( ElementaryTensor,
        [ IsPathCategoryMorphism, IsPathCategoryObject, IsQuotientOfPathCategory ],
  
  function ( mor, obj, C1_x_C2 )
    local q1, q2, obj_index, mor_indices, indices, source, target;
    
    q1 := UnderlyingQuiver( CapCategory( mor ) );
    q2 := UnderlyingQuiver( CapCategory( obj ) );
    
    obj_index := ObjectIndex( obj );
    mor_indices := MorphismIndices( mor );
    
    indices := List( mor_indices, index ->
                  NumberOfObjects( q1 ) * NumberOfMorphisms( q2 ) + (index - 1) * NumberOfObjects( q2 ) + obj_index );
    
    source := ElementaryTensor( Source( mor ), obj, C1_x_C2 );
    target := ElementaryTensor( Target( mor ), obj, C1_x_C2 );
    
    return MorphismConstructor( C1_x_C2,
              source,
              MorphismConstructor( UnderlyingCategory( C1_x_C2 ),
                  UnderlyingCell( source ),
                  Pair( Length( indices ), indices ),
                  UnderlyingCell( target )  ),
              target );
end );

##
InstallMethod( ElementaryTensor,
          [ IsPathCategoryMorphism, IsPathCategoryMorphism, IsQuotientOfPathCategory ],
  
  function ( mor_1, mor_2, C1_x_C2 )
    
    return PreCompose( C1_x_C2,
              ElementaryTensor( mor_1, Source( mor_2 ), C1_x_C2 ),
              ElementaryTensor( Target( mor_1 ), mor_2, C1_x_C2 ) );
    
end );

##
InstallMethod( ElementaryTensor,
        [ IsQuotientOfPathCategoryObject, IsQuotientOfPathCategoryObject, IsQuotientOfPathCategory ],
  
  function ( obj_1, obj_2, C1_x_C2 )
    
    return ElementaryTensor( UnderlyingCell( obj_1 ), UnderlyingCell( obj_2 ), C1_x_C2 );
    
end );

##
InstallMethod( ElementaryTensor,
        [ IsQuotientOfPathCategoryObject, IsQuotientOfPathCategoryMorphism, IsQuotientOfPathCategory ],
  
  function ( obj, mor, C1_x_C2 )
    
    return ElementaryTensor( UnderlyingCell( obj ), UnderlyingCell( mor ), C1_x_C2 );
    
end );

##
InstallMethod( ElementaryTensor,
        [ IsQuotientOfPathCategoryMorphism, IsQuotientOfPathCategoryObject, IsQuotientOfPathCategory ],
  
  function ( mor, obj, C1_x_C2 )
    
    return ElementaryTensor( UnderlyingCell( mor ), UnderlyingCell( obj ), C1_x_C2 );
    
end );

##
InstallMethod( ElementaryTensor,
          [ IsQuotientOfPathCategoryMorphism, IsQuotientOfPathCategoryMorphism, IsQuotientOfPathCategory ],
  
  function ( mor_1, mor_2, C1_x_C2 )
    
    return PreCompose( C1_x_C2,
              ElementaryTensor( mor_1, Source( mor_2 ), C1_x_C2 ),
              ElementaryTensor( Target( mor_1 ), mor_2, C1_x_C2 ) );
    
end );

##
InstallOtherMethod( ElementaryTensor,
          [ IsCapCategory, IsCapCategoryCell, IsCapCategoryCell ],
  
  function ( C, c_1, c_2 )
    
    return ElementaryTensor( c_1, c_2, C );
    
end );

##
InstallMethod( CanonicalRepresentative,
        [ IsQuotientOfPathCategoryMorphism ],
  
  function ( mor )
    local qC;
    
    qC := CapCategory( mor );
    
    return ReductionOfMorphism( UnderlyingCategory( qC ), MorphismDatum( qC, mor ), GroebnerBasisOfDefiningRelations( qC ) );
    
end );

##
InstallMethod( ObjectIndex,
          [ IsQuotientOfPathCategoryObject ],
  
  function ( obj )
    
    return ObjectIndex( ObjectDatum( obj ) );
    
end );

InstallMethod( ExternalHomsWithGivenLengthOp,
        [ IsQuotientOfPathCategory, IsInt ],
        
  function ( quo_C, len )
    local C, mors;
    
    C := UnderlyingCategory( quo_C );
    
    mors := ExternalHomsWithGivenLength( C, len );
    
    return List( mors, row ->
                 List( row, morphisms ->
                       DuplicateFreeList(
                               List( morphisms, m ->
                                     MorphismConstructor( quo_C,
                                             SetOfObjects( quo_C )[ObjectIndex( Source( m ) )],
                                             m,
                                             SetOfObjects( quo_C )[ObjectIndex( Target( m ) )] ) ) ) ) );
    
end );

##
InstallGlobalFunction( INSTALL_SPECIAL_VIEW_STRING_FOR_MORPHISMS_IN_TENSOR_PRODUCT_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS,
  
  function ( C1xC2, C1, C2 )
    local q1, q2, quiver_datum_1, quiver_datum_2;
    
    q1 := UnderlyingQuiver( C1 );
    q2 := UnderlyingQuiver( C2 );
    
    quiver_datum_1 := QuiverDatum( q1 );
    quiver_datum_2 := QuiverDatum( q2 );
    
    ##
    InstallMethod( ViewString,
              [ MorphismFilter( C1xC2 ) ],
      
      function ( mor )
        local indices, l_side, r_side, index, string, as_power;
        
        mor := CanonicalRepresentative( mor );
        
        indices := MorphismIndices( mor );
        
        l_side := [ ];
        r_side := [ ];
         
        for index in indices do
            
            if index <= quiver_datum_1[2][1] * quiver_datum_2[3][1] then
                
                Add( r_side, quiver_datum_2[3][4][1 + REM_INT(index - 1, quiver_datum_2[3][1])] );
                
            else
                
                index := index - quiver_datum_1[2][1] * quiver_datum_2[3][1];
                
                Add( l_side, quiver_datum_1[3][4][1 + QUO_INT(index - 1, quiver_datum_2[2][1])] );
                
            fi;
        od;
        
        as_power :=
          function( pair )
            if pair[2] = 1 then
                return pair[1];
            else
                return Concatenation( pair[1], "^", String( pair[2] ) );
            fi;
        end;
        
        l_side := List( CollectEntries( l_side ), as_power );
        r_side := List( CollectEntries( r_side ), as_power );
        
        if IsEmpty( l_side ) then
            l_side := quiver_datum_1[2][2][1 + QUO_INT( ObjectIndex( Source( mor ) ) - 1, quiver_datum_2[2][1] )];
        else
            l_side := JoinStringsWithSeparator( l_side, "⋅" );
        fi;
        
        if IsEmpty( r_side ) then
            r_side := quiver_datum_2[2][2][1 + REM_INT( ObjectIndex( Source( mor ) ) - 1, quiver_datum_2[2][1] )];
        else
            r_side := JoinStringsWithSeparator( r_side, "⋅" );
        fi;
        
        string := JoinStringsWithSeparator( [ l_side, r_side ], "⊗" );
        
        if IsEmpty( indices ) then
            string := Concatenation( "id(", string, ")" );
        fi;
        
        return Concatenation( "[", string, "]:", ViewString( Source( mor ) ), " -≻ ", ViewString( Target( mor ) ) );
        
      end );
      
end );

##
InstallMethod( DisplayString,
          [ IsQuotientOfPathCategoryObject ],
  
  function ( obj )
    
    return Concatenation( ViewString( obj ), "\n" );
    
end );

##
InstallMethod( ViewString,
          [ IsQuotientOfPathCategoryObject ],
  
  function ( obj )
    
    return ViewString( UnderlyingCell( obj ) );
    
end );

##
InstallMethod( String,
          [ IsQuotientOfPathCategoryObject ],
  
  ViewString );

##
InstallMethod( DisplayString,
          [ IsQuotientOfPathCategoryMorphism ],
  
  function ( mor )
    
    return Concatenation( ViewString( mor ), "\n" );
    
end );

##
InstallMethod( ViewString,
          [ IsQuotientOfPathCategoryMorphism ],
  function ( mor )
    local colors, str;
    
    colors := UnderlyingQuiver( UnderlyingCategory( CapCategory( mor ) ) )!.colors;
    
    str := ViewString( CanonicalRepresentative( mor ) );
    
    str := Concatenation( "[", str );
    
    str := ReplacedString(
                  str,
                  Concatenation( colors!.other, ":" ),
                  Concatenation( colors.reset, "]", colors.other, ":") );
    
    return str;
    
end );

##
InstallMethod( String,
          [ IsQuotientOfPathCategoryMorphism ],
  
  ViewString );
