# SPDX-License-Identifier: GPL-2.0-or-later
# Locales: Locales, frames, coframes, meet semi-lattices of locally closed subsets, and Boolean algebras of constructible sets
#
# Implementations
#

InstallTrueMethod( IsBiHeytingAlgebra, IsHeytingAlgebra and IsCoHeytingAlgebra );
InstallTrueMethod( IsHeytingAlgebra, IsBiHeytingAlgebra );
InstallTrueMethod( IsCoHeytingAlgebra, IsBiHeytingAlgebra );

InstallTrueMethod( IsBiHeytingAlgebra, IsBooleanAlgebra );

##
InstallGlobalFunction( ADD_COMMON_METHODS_FOR_BOOLEAN_ALGEBRAS,
  function( boolean_algebra )
    
    SetIsBooleanAlgebra( boolean_algebra, true );
    
    ADD_COMMON_METHODS_FOR_HEYTING_ALGEBRAS( boolean_algebra );
    
    ADD_COMMON_METHODS_FOR_COHEYTING_ALGEBRAS( boolean_algebra );
    
    ##
    AddMorphismFromDoubleNegationWithGivenDoubleNegation( boolean_algebra,
      function( cat, A, B )
        
        return UniqueMorphism( cat, B, A );
        
    end );
    
    ##
    AddMorphismToDoubleConegationWithGivenDoubleConegation( boolean_algebra,
      function( cat, A, B )
        
        return UniqueMorphism( cat, A, B );
        
    end );
    
end );
