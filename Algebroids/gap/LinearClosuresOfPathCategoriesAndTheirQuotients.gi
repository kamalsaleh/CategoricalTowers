





BindGlobal( "LINEAR_CLOSURE_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS",
  
  function ( k, C )
    local admissible_order, colors, sorting_func, k_C;
    
    admissible_order := ValueOption( "admissible_order" );
    
    if admissible_order = fail then
        
        if IsPathCategory( C ) then
          admissible_order := C!.admissible_order;
        else
          admissible_order := UnderlyingCategory( C )!.admissible_order;
        fi;
        
    elif not admissible_order in [ "Dp", "dp" ] then
        
        Error( "only \"Dp\" and \"dp\" admissible orders are supported!\n" );
        
    fi;
    
    colors := ValueOption( "colors" );
    
    if colors = fail then
        
        colors := rec( coeff := "", other := "", reset := "" );
        
    elif colors = true then
        
        colors := rec( coeff := TextAttr.5, other := TextAttr.1, reset := TextAttr.reset );
        
    fi;
    
    if IsPathCategory( C ) then
        
        sorting_func := { mor_1, mor_2 } -> IsDescendingForMorphisms( C, mor_1, mor_2, admissible_order );
        
    else
        
        sorting_func := { mor_1, mor_2 } -> IsDescendingForMorphisms( UnderlyingCategory( C ), CanonicalRepresentative( mor_1 ), CanonicalRepresentative( mor_2 ), admissible_order );
        
    fi;
    
    k_C := LinearClosure( k, C, sorting_func : overhead := false ); # every morphism start by its maximum monomial
    
    k_C!.Name := Concatenation( RingName( k ), "-", k_C!.Name );
    
    k_C!.admissible_order := admissible_order;
    
    k_C!.colors := colors;
    
    SetSetOfObjects( k_C,
          List( SetOfObjects( C ),
                    o -> ObjectConstructor( k_C, o ) ) );
    
    SetSetOfGeneratingMorphisms( k_C,
          List( SetOfGeneratingMorphisms( C ),
                    m -> MorphismConstructor( k_C,
                              SetOfObjects( k_C )[ObjectIndex( Source( m ) )],
                              Pair( [ One( UnderlyingRing( k_C ) ) ], [ m ] ),
                              SetOfObjects( k_C )[ObjectIndex( Target( m ) )] ) ) );
    
    INSTALL_VIEW_AND_DISPLAY_METHODS_IN_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS( k_C );
    
    return k_C;
    
end );

##
InstallOtherMethod( LinearClosure,
          [ IsHomalgRing, IsPathCategory ],
    
    LINEAR_CLOSURE_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS
);

##
InstallOtherMethod( \[\],
          [ IsHomalgRing, IsPathCategory ],
  
  { k, C } -> LinearClosure( k, C : overhead := false )
);

##
InstallOtherMethod( LinearClosure,
          [ IsHomalgRing, IsQuotientOfPathCategory ],
  
  LINEAR_CLOSURE_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS
);

##
InstallOtherMethod( \[\],
          [ IsHomalgRing, IsQuotientOfPathCategory ],
  
  { k, C } -> LinearClosure( k, C : overhead := false )
);

##
InstallGlobalFunction( "INSTALL_VIEW_AND_DISPLAY_METHODS_IN_LINEAR_CLOSURES_OF_PATH_CATEGORIES_OR_THEIR_QUOTIENTS",
  
  function ( k_C )
    local C;
     
    C := UnderlyingCategory( k_C );
    
    if IsQuotientOfPathCategory( C ) then
        
        C := UnderlyingCategory( C );
        
    fi;
    
    ##
    InstallMethod( ViewString,
              [ ObjectFilter( k_C ) ],
      
      function ( obj )
        
        return ViewString( ObjectDatum( obj ) );
        
    end );
    
    ##
    InstallMethod( DisplayString,
              [ ObjectFilter( k_C ) ],
      
      obj -> Concatenation( ViewString( obj ), "\n" )
    );
    
    ##
    InstallMethod( ViewString,
              [ MorphismFilter( k_C ) ],
      
      function ( alpha )
        local k_C, Q, coeffs, labels, datum_string;
        
        k_C := CapCategory( alpha );
        
        Q := CapQuiver( C );
        
        coeffs := List( CoefficientsList( alpha ), c -> Concatenation( k_C!.colors.coeff, String( c ), k_C!.colors.reset ) );
        
        labels := List( SupportMorphisms( alpha ), m -> ( str -> str{[1 .. PositionSublist( str, Concatenation( Q!.colors.other, ":" ) ) - 1]} )( ViewString( m ) ) );
        
        if IsEmpty( labels ) then
            
            datum_string := Concatenation( k_C!.colors.coeff, "0", k_C!.colors.reset );
            
        else
            
            datum_string := JoinStringsWithSeparator( ListN( coeffs, labels, { c, l } -> Concatenation( c, "*", l ) ), Concatenation( k_C!.colors.reset, " + " ) );
            datum_string := ReplacedString( datum_string, Concatenation( "+ ", k_C!.colors.coeff, "-" ), Concatenation( "- ", k_C!.colors.coeff ) );
        fi;
        
        return
          Concatenation(
              datum_string,
              Q!.colors.other,
              ":",
              ViewString( ObjectDatum( UnderlyingOriginalObject( Source( alpha ) ) ) ),
              Q!.colors.other,
              " -≻ ",
              ViewString( ObjectDatum( UnderlyingOriginalObject( Target( alpha ) ) ) ) );
          
    end );
    
    ##
    InstallMethod( DisplayString,
              [ MorphismFilter( k_C ) ],
      
      mor -> Concatenation( ViewString( mor ), "\n" )
    );
    
end );

##
InstallMethod( \.,
          [ IsLinearClosure, IsPosInt ],
  
  function ( k_C, string_as_int )
    local name, cell;
    
    name := NameRNam( string_as_int );
    
    cell := UnderlyingCategory( k_C ).( name );
    
    if IsCapCategoryObject( cell ) then
        
        return ObjectConstructor( k_C, cell );
        
    else
        
        return MorphismConstructor( k_C,
                    ObjectConstructor( k_C, Source( cell ) ),
                    Pair( [ One( UnderlyingRing( k_C ) ) ], [ cell ] ),
                    ObjectConstructor( k_C, Target( cell ) ) );
        
    fi;
    
end );

