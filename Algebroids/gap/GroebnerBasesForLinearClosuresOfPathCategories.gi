






InstallOtherMethod( ReductionOfMorphism,
          [ IsLinearClosure, IsLinearClosureMorphism, IsDenseList ],
  
  function ( kC, f, G )
    local C, one, S, T, lC_G, lM_G, lM_G_datum, r, lC_f, lM_f, lM_f_datum, i, p, c_i, u_i, v_i, t, lT_f;
    
    C := UnderlyingCategory( kC );
    
    one := One( UnderlyingRing( kC ) );
    
    S := Source( f );
    T := Target( f );
    
    lC_G := List( G, g -> CoefficientsList( g )[1] );
    lM_G := List( G, g -> SupportMorphisms( g )[1] );
    lM_G_datum := List( lM_G, m -> MorphismDatum( C, m ) );
    
    r := ZeroMorphism( kC, S, T );
    
    while not IsZeroForMorphisms( kC, f ) do
        
        lC_f := CoefficientsList( f )[1];
        lM_f := SupportMorphisms( f )[1];
        
        lM_f_datum := MorphismDatum( C, lM_f );
        
        i := PositionProperty( lM_G_datum, datum -> PositionSublist( lM_f_datum[2], datum[2] ) <> fail );
        
        if i <> fail then
            
            p := PositionSublist( lM_f_datum[2], lM_G_datum[i][2] );
            
            c_i := lC_f / lC_G[i];
            
            u_i := MorphismConstructor( C,
                            UnderlyingOriginalObject( S ),
                            Pair( p - 1, lM_f_datum[2]{[ 1 .. p - 1 ]} ),
                            UnderlyingOriginalObject( Source( G[i] ) ) );
            
            u_i := MorphismConstructor( kC, S, Pair( [ one ], [ u_i ] ), Source( G[i] ) );
            
            v_i := MorphismConstructor( C,
                            UnderlyingOriginalObject( Target( G[i] ) ),
                            Pair( lM_f_datum[1] - p - lM_G_datum[i][1] + 1, lM_f_datum[2]{[ p + lM_G_datum[i][1] .. lM_f_datum[1] ]} ),
                            UnderlyingOriginalObject( T ) );
            
            v_i := MorphismConstructor( kC, Target( G[i] ), Pair( [ one ], [ v_i ] ), T );
            
            t := MultiplyWithElementOfCommutativeRingForMorphisms( kC, c_i, PreComposeList( kC, [ u_i, G[i], v_i ] ) );
            f := SubtractionForMorphisms( kC, f, t );
            
        else
            
            lT_f := MorphismConstructor( kC, S, Pair( [ lC_f ], [ lM_f ] ), T );
            
            r := AdditionForMorphisms   ( kC, r, lT_f );
            f := SubtractionForMorphisms( kC, f, lT_f );
            
        fi;
        
    od;
    
    return r; # c, u, v
    
end );

##
InstallOtherMethod( NewRelation,
          [ IsLinearClosure, IsLinearClosureMorphism, IsLinearClosureMorphism, IsDenseList ],
  
  function ( kC, g, h, overlap_coeffs )
    local C, one, lM_g, lM_h, l_lM_g, r_lM_g, l_lM_h, r_lM_h, lC_g, lC_h;
    
    C := UnderlyingCategory( kC );
    
    one := One( UnderlyingRing( kC ) );
    
    lM_g := SupportMorphisms( g )[1];
    lM_h := SupportMorphisms( h )[1];
    
    l_lM_g := MorphismConstructor( kC, SetOfObjects( kC )[ObjectIndex( Source( overlap_coeffs[1][1] ) )], Pair( [ one ], [ overlap_coeffs[1][1] ] ), Source( g ) );
    r_lM_g := MorphismConstructor( kC, Target( g ), Pair( [ one ], [ overlap_coeffs[1][2] ] ), SetOfObjects( kC )[ObjectIndex( Target( overlap_coeffs[1][2] ) )] );
    
    l_lM_h := MorphismConstructor( kC, SetOfObjects( kC )[ObjectIndex( Source( overlap_coeffs[2][1] ) )], Pair( [ one ], [ overlap_coeffs[2][1] ] ), Source( h ) );
    r_lM_h := MorphismConstructor( kC, Target( h ), Pair( [ one ], [ overlap_coeffs[2][2] ] ), SetOfObjects( kC )[ObjectIndex( Target( overlap_coeffs[2][2] ) )] );
    
    lC_g := CoefficientsList( g )[1];
    lC_h := CoefficientsList( h )[1];
    
    return SubtractionForMorphisms( kC,
                MultiplyWithElementOfCommutativeRingForMorphisms( kC, Inverse( lC_g ), PreComposeList( kC, [ l_lM_g, g, r_lM_g ] ) ),
                MultiplyWithElementOfCommutativeRingForMorphisms( kC, Inverse( lC_h ), PreComposeList( kC, [ l_lM_h, h, r_lM_h ] ) ) );
    
end );

##
InstallOtherMethod( GroebnerBasis,
          [ IsLinearClosure, IsDenseList ],
  
  function ( kC, relations )
    local C, groebner_basis, indices, rels, i, g, new_indices, new_rels;
    
    C := UnderlyingCategory( kC );
    
    # Compute a Gröbner basis
    
    groebner_basis := ShallowCopy( relations );
    
    indices := Concatenation( List( [ 1 .. Length( groebner_basis ) ], i -> [ i, i ] ), Combinations( [ 1 .. Length( groebner_basis ) ], 2 ) );
    
    rels := Concatenation( List( indices,
                                i -> List( OverlappingCoefficients( C,
                                              SupportMorphisms( groebner_basis[i[1]] )[1], SupportMorphisms( groebner_basis[i[2]] )[1] ),
                                                  overlap_coeffs -> NewRelation( kC, groebner_basis[i[1]], groebner_basis[i[2]], overlap_coeffs ) ) ) );
    
    i := 1;
    
    while i <= Length( rels ) do
        
        if not IsZeroForMorphisms( kC, rels[i] ) then
            
            g := ReductionOfMorphism( kC, rels[i], groebner_basis );
            
            if not IsZeroForMorphisms( kC, g ) then
              
              Add( groebner_basis, Inverse( CoefficientsList( g )[1] ) * g ); # one can also add g without normalization
              
              new_indices := List( [ 1 .. Length( groebner_basis ) ], i -> [ i, Length( groebner_basis ) ] );
              
              new_rels := Concatenation(
                            List( new_indices,
                                i -> List( OverlappingCoefficients( C,
                                              SupportMorphisms( groebner_basis[i[1]] )[1], SupportMorphisms( groebner_basis[i[2]] )[1] ),
                                                  overlap_coeffs -> NewRelation( kC, groebner_basis[i[1]], groebner_basis[i[2]], overlap_coeffs ) ) ) );
              
              rels := Concatenation( rels, new_rels );
              
            fi;
            
        fi;
        
        i := i + 1;
        
    od;
    
    return groebner_basis;
    
end );

##
InstallOtherMethod( ReducedGroebnerBasisWithGivenGroebnerBasis,
            [ IsLinearClosure, IsDenseList ],
  
  function ( kC, groebner_basis )
    local reduced_groebner_basis, i, r;
    
    reduced_groebner_basis := ShallowCopy( groebner_basis );
    
    i := 1;
    
    while i <= Length( reduced_groebner_basis ) do
      
      r := ReductionOfMorphism( kC, reduced_groebner_basis[i], reduced_groebner_basis{Difference( [ 1 .. Length( reduced_groebner_basis ) ], [ i ] )} );
      
      if IsZeroForMorphisms( kC, r ) then
          
          Remove( reduced_groebner_basis, i );
          
      elif not IsEqualForMorphisms( kC, r, reduced_groebner_basis[i] ) then
          
          reduced_groebner_basis[i] := MultiplyWithElementOfCommutativeRingForMorphisms( kC, Inverse( CoefficientsList( r )[1] ), r );
          
          i := 1;
          
      else
          
          i := i + 1;
          
      fi;
      
    od;
    
    return reduced_groebner_basis;
    
end );

##
InstallOtherMethod( ReducedGroebnerBasis,
          [ IsLinearClosure, IsDenseList ],
  
  function ( kC, relations )
    
    return ReducedGroebnerBasisWithGivenGroebnerBasis( kC, GroebnerBasis( kC, relations ) );
    
end );

