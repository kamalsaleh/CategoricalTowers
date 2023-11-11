# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Tools

#! @Section Tools for quivers

#! @Description
#!  Return a triple consisting of the number of vertices of the quiver <A>q</A>,
#!  the number of arrows of the quiver <A>q</A>, and a list of pairs of integers
#!  encoding the arrows of <A>q</A>.
#! @Arguments q
#! @Returns a triple
DeclareAttribute( "DefiningTripleOfAQuiver",
        IsQuiver );
#! @InsertChunk DefiningTripleOfAQuiver

#! @Section Tools for categories

#! @Description
#!  The nerve data of the category <A>C</A>.
#! @Arguments C
#! @Returns a pair consisting of a triple and an 8-tuple
DeclareAttribute( "NerveTruncatedInDegree2Data",
        IsCapCategory );

#! @Description
#!  The normalized indices of the generating morphisms of the finite category <A>C</A>.
#! @Arguments C
#! @Returns a list of integers
DeclareAttribute( "IndicesOfGeneratingMorphismsFromHomStructure",
        IsCapCategory );

#! @Description
#!  The opposite category of a finite category <A>C</A>.
#! @Arguments C
#! @Returns a &CAP; category
DeclareAttribute( "OppositeFiniteCategory",
        IsCapCategory );

DeclareGlobalFunction( "DefiningTripleOfUnderlyingQuiverAsString" );

DeclareGlobalFunction( "DefiningTripleOfUnderlyingQuiverAsENHANCED_SYNTAX_TREE" );

DeclareGlobalFunction( "IndicesOfGeneratingMorphismsAsENHANCED_SYNTAX_TREE" );

DeclareGlobalFunction( "DecompositionIndicesOfAllMorphismsAsENHANCED_SYNTAX_TREE" );

DeclareGlobalFunction( "DataTablesAsString" );

DeclareGlobalFunction( "DataTablesAsENHANCED_SYNTAX_TREE" );
