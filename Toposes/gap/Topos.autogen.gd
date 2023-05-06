# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Declarations
#
# THIS FILE IS AUTOMATICALLY GENERATED, SEE CAP_project/CAP/gap/MethodRecord.gi

#! @Chapter Toposes

#! @Section Add-methods

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `CartesianSquareOfSubobjectClassifier`.
#! $F: (  ) \mapsto \mathtt{CartesianSquareOfSubobjectClassifier}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddCartesianSquareOfSubobjectClassifier",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddCartesianSquareOfSubobjectClassifier",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddCartesianSquareOfSubobjectClassifier",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddCartesianSquareOfSubobjectClassifier",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `ClassifyingMorphismOfSubobject`.
#! $F: ( alpha ) \mapsto \mathtt{ClassifyingMorphismOfSubobject}(alpha)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddClassifyingMorphismOfSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddClassifyingMorphismOfSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddClassifyingMorphismOfSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddClassifyingMorphismOfSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `ClassifyingMorphismOfSubobjectWithGivenSubobjectClassifier`.
#! $F: ( alpha, Omega ) \mapsto \mathtt{ClassifyingMorphismOfSubobjectWithGivenSubobjectClassifier}(alpha, Omega)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddClassifyingMorphismOfSubobjectWithGivenSubobjectClassifier",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddClassifyingMorphismOfSubobjectWithGivenSubobjectClassifier",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddClassifyingMorphismOfSubobjectWithGivenSubobjectClassifier",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddClassifyingMorphismOfSubobjectWithGivenSubobjectClassifier",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfIntersectionSubobject`.
#! $F: ( iota1, iota2 ) \mapsto \mathtt{EmbeddingOfIntersectionSubobject}(iota1, iota2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfIntersectionSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfIntersectionSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfIntersectionSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfIntersectionSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfIntersectionSubobjectWithGivenIntersection`.
#! $F: ( iota1, iota2, intersection ) \mapsto \mathtt{EmbeddingOfIntersectionSubobjectWithGivenIntersection}(iota1, iota2, intersection)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfIntersectionSubobjectWithGivenIntersection",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfIntersectionSubobjectWithGivenIntersection",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfIntersectionSubobjectWithGivenIntersection",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfIntersectionSubobjectWithGivenIntersection",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfPseudoComplementSubobject`.
#! $F: ( iota ) \mapsto \mathtt{EmbeddingOfPseudoComplementSubobject}(iota)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfPseudoComplementSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfPseudoComplementSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfPseudoComplementSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfPseudoComplementSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfPseudoComplementSubobjectWithGivenPseudoComplement`.
#! $F: ( iota, complement ) \mapsto \mathtt{EmbeddingOfPseudoComplementSubobjectWithGivenPseudoComplement}(iota, complement)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfPseudoComplementSubobjectWithGivenPseudoComplement",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfPseudoComplementSubobjectWithGivenPseudoComplement",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfPseudoComplementSubobjectWithGivenPseudoComplement",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfPseudoComplementSubobjectWithGivenPseudoComplement",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfRelativePseudoComplementSubobject`.
#! $F: ( iota1, iota2 ) \mapsto \mathtt{EmbeddingOfRelativePseudoComplementSubobject}(iota1, iota2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfRelativePseudoComplementSubobjectWithGivenImplication`.
#! $F: ( iota1, iota2, implication ) \mapsto \mathtt{EmbeddingOfRelativePseudoComplementSubobjectWithGivenImplication}(iota1, iota2, implication)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobjectWithGivenImplication",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobjectWithGivenImplication",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobjectWithGivenImplication",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfRelativePseudoComplementSubobjectWithGivenImplication",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfUnionSubobject`.
#! $F: ( iota1, iota2 ) \mapsto \mathtt{EmbeddingOfUnionSubobject}(iota1, iota2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfUnionSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfUnionSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfUnionSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfUnionSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `EmbeddingOfUnionSubobjectWithGivenUnion`.
#! $F: ( iota1, iota2, union ) \mapsto \mathtt{EmbeddingOfUnionSubobjectWithGivenUnion}(iota1, iota2, union)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddEmbeddingOfUnionSubobjectWithGivenUnion",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddEmbeddingOfUnionSubobjectWithGivenUnion",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddEmbeddingOfUnionSubobjectWithGivenUnion",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddEmbeddingOfUnionSubobjectWithGivenUnion",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `ExactCoverWithGlobalElements`.
#! $F: ( arg2 ) \mapsto \mathtt{ExactCoverWithGlobalElements}(arg2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddExactCoverWithGlobalElements",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddExactCoverWithGlobalElements",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddExactCoverWithGlobalElements",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddExactCoverWithGlobalElements",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `HasPushoutComplement`.
#! $F: ( arg2, arg3 ) \mapsto \mathtt{HasPushoutComplement}(arg2, arg3)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddHasPushoutComplement",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddHasPushoutComplement",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddHasPushoutComplement",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddHasPushoutComplement",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `IntersectionSubobject`.
#! $F: ( arg2, arg3 ) \mapsto \mathtt{IntersectionSubobject}(arg2, arg3)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddIntersectionSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIntersectionSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIntersectionSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIntersectionSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `IsomorphismOntoCartesianSquareOfPowerObject`.
#! $F: ( a ) \mapsto \mathtt{IsomorphismOntoCartesianSquareOfPowerObject}(a)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `IsomorphismOntoCartesianSquareOfPowerObjectWithGivenObjects`.
#! $F: ( ExpaOmega2, a, PaxPa ) \mapsto \mathtt{IsomorphismOntoCartesianSquareOfPowerObjectWithGivenObjects}(ExpaOmega2, a, PaxPa)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObjectWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObjectWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObjectWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsomorphismOntoCartesianSquareOfPowerObjectWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `LawvereTierneyEmbeddingsOfSubobjectClassifiers`.
#! $F: (  ) \mapsto \mathtt{LawvereTierneyEmbeddingsOfSubobjectClassifiers}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddLawvereTierneyEmbeddingsOfSubobjectClassifiers",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddLawvereTierneyEmbeddingsOfSubobjectClassifiers",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddLawvereTierneyEmbeddingsOfSubobjectClassifiers",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddLawvereTierneyEmbeddingsOfSubobjectClassifiers",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `LawvereTierneyLocalModalityOperators`.
#! $F: (  ) \mapsto \mathtt{LawvereTierneyLocalModalityOperators}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddLawvereTierneyLocalModalityOperators",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddLawvereTierneyLocalModalityOperators",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddLawvereTierneyLocalModalityOperators",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddLawvereTierneyLocalModalityOperators",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `LawvereTierneySubobjects`.
#! $F: (  ) \mapsto \mathtt{LawvereTierneySubobjects}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddLawvereTierneySubobjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddLawvereTierneySubobjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddLawvereTierneySubobjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddLawvereTierneySubobjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `ListOfSubobjects`.
#! $F: ( arg2 ) \mapsto \mathtt{ListOfSubobjects}(arg2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddListOfSubobjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddListOfSubobjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddListOfSubobjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddListOfSubobjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `MorphismsOfExternalHom`.
#! $F: ( arg2, arg3 ) \mapsto \mathtt{MorphismsOfExternalHom}(arg2, arg3)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddMorphismsOfExternalHom",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddMorphismsOfExternalHom",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddMorphismsOfExternalHom",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddMorphismsOfExternalHom",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `PowerObject`.
#! $F: ( arg2 ) \mapsto \mathtt{PowerObject}(arg2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddPowerObject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddPowerObject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddPowerObject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddPowerObject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `PowerObjectFunctorial`.
#! $F: ( f ) \mapsto \mathtt{PowerObjectFunctorial}(f)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddPowerObjectFunctorial",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddPowerObjectFunctorial",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddPowerObjectFunctorial",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddPowerObjectFunctorial",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `PowerObjectFunctorialWithGivenPowerObjects`.
#! $F: ( Pb, f, Pa ) \mapsto \mathtt{PowerObjectFunctorialWithGivenPowerObjects}(Pb, f, Pa)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddPowerObjectFunctorialWithGivenPowerObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddPowerObjectFunctorialWithGivenPowerObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddPowerObjectFunctorialWithGivenPowerObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddPowerObjectFunctorialWithGivenPowerObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `PseudoComplementSubobject`.
#! $F: ( arg2 ) \mapsto \mathtt{PseudoComplementSubobject}(arg2)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddPseudoComplementSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddPseudoComplementSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddPseudoComplementSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddPseudoComplementSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `PushoutComplement`.
#! $F: ( l, m ) \mapsto \mathtt{PushoutComplement}(l, m)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddPushoutComplement",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddPushoutComplement",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddPushoutComplement",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddPushoutComplement",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `RelativePseudoComplementSubobject`.
#! $F: ( arg2, arg3 ) \mapsto \mathtt{RelativePseudoComplementSubobject}(arg2, arg3)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddRelativePseudoComplementSubobject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `SingletonMorphism`.
#! $F: ( a ) \mapsto \mathtt{SingletonMorphism}(a)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddSingletonMorphism",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddSingletonMorphism",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddSingletonMorphism",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddSingletonMorphism",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `SingletonMorphismWithGivenPowerObject`.
#! $F: ( a, Pa ) \mapsto \mathtt{SingletonMorphismWithGivenPowerObject}(a, Pa)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddSingletonMorphismWithGivenPowerObject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddSingletonMorphismWithGivenPowerObject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddSingletonMorphismWithGivenPowerObject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddSingletonMorphismWithGivenPowerObject",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `SubobjectClassifier`.
#! $F: (  ) \mapsto \mathtt{SubobjectClassifier}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddSubobjectClassifier",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddSubobjectClassifier",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddSubobjectClassifier",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddSubobjectClassifier",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `SubobjectOfClassifyingMorphism`.
#! $F: ( alpha ) \mapsto \mathtt{SubobjectOfClassifyingMorphism}(alpha)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddSubobjectOfClassifyingMorphism",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddSubobjectOfClassifyingMorphism",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddSubobjectOfClassifyingMorphism",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddSubobjectOfClassifyingMorphism",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfAnd`.
#! $F: (  ) \mapsto \mathtt{TruthMorphismOfAnd}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfAnd",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfAnd",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfAnd",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfAnd",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfAndWithGivenObjects`.
#! $F: ( Omega2, Omega ) \mapsto \mathtt{TruthMorphismOfAndWithGivenObjects}(Omega2, Omega)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfAndWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfAndWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfAndWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfAndWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfFalse`.
#! $F: (  ) \mapsto \mathtt{TruthMorphismOfFalse}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfFalse",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfFalse",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfFalse",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfFalse",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfFalseWithGivenObjects`.
#! $F: ( T, Omega ) \mapsto \mathtt{TruthMorphismOfFalseWithGivenObjects}(T, Omega)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfFalseWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfFalseWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfFalseWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfFalseWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfImplies`.
#! $F: (  ) \mapsto \mathtt{TruthMorphismOfImplies}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfImplies",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfImplies",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfImplies",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfImplies",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfImpliesWithGivenObjects`.
#! $F: ( Omega2, Omega ) \mapsto \mathtt{TruthMorphismOfImpliesWithGivenObjects}(Omega2, Omega)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfImpliesWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfImpliesWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfImpliesWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfImpliesWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfNot`.
#! $F: (  ) \mapsto \mathtt{TruthMorphismOfNot}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfNot",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfNot",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfNot",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfNot",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfNotWithGivenObjects`.
#! $F: ( Omega, Omega1 ) \mapsto \mathtt{TruthMorphismOfNotWithGivenObjects}(Omega, Omega1)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfNotWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfNotWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfNotWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfNotWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfOr`.
#! $F: (  ) \mapsto \mathtt{TruthMorphismOfOr}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfOr",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfOr",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfOr",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfOr",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfOrWithGivenObjects`.
#! $F: ( Omega2, Omega ) \mapsto \mathtt{TruthMorphismOfOrWithGivenObjects}(Omega2, Omega)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfOrWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfOrWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfOrWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfOrWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfTrue`.
#! $F: (  ) \mapsto \mathtt{TruthMorphismOfTrue}()$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfTrue",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfTrue",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfTrue",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfTrue",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `TruthMorphismOfTrueWithGivenObjects`.
#! $F: ( T, Omega ) \mapsto \mathtt{TruthMorphismOfTrueWithGivenObjects}(T, Omega)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddTruthMorphismOfTrueWithGivenObjects",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddTruthMorphismOfTrueWithGivenObjects",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddTruthMorphismOfTrueWithGivenObjects",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddTruthMorphismOfTrueWithGivenObjects",
                  [ IsCapCategory, IsList ] );

#! @Description
#! The arguments are a category $C$ and a function $F$.
#! This operation adds the given function $F$
#! to the category for the basic operation `UnionSubobject`.
#! $F: ( arg2, arg3 ) \mapsto \mathtt{UnionSubobject}(arg2, arg3)$.
#! @Returns nothing
#! @Arguments C, F
DeclareOperation( "AddUnionSubobject",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddUnionSubobject",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddUnionSubobject",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddUnionSubobject",
                  [ IsCapCategory, IsList ] );
