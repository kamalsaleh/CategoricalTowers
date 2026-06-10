# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations depending on the Algebroids package
#

##
InstallMethod( AddAdditionalMonoidalStructureToFunctorCategory,
        "for a functor category with algebroid source",
        [ IsFunctorCategory, IsAlgebroid, IsCapCategory ],
        
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
