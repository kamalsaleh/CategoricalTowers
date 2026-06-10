# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Reading the declaration part of the package.
#

ReadPackage( "FunctorCategories", "gap/PreSheaves.gd");
ReadPackage( "FunctorCategories", "gap/HomStructure.gd");
ReadPackage( "FunctorCategories", "gap/FunctorCategories.gd");
ReadPackage( "FunctorCategories", "gap/CoPreSheaves.gd");
ReadPackage( "FunctorCategories", "gap/FiniteCocompletion.gd");
ReadPackage( "FunctorCategories", "gap/CategoryOfBouquets.gd");
ReadPackage( "FunctorCategories", "gap/CategoryOfQuivers.gd");
ReadPackage( "FunctorCategories", "gap/CategoryOfDecoratedQuivers.gd");
ReadPackage( "FunctorCategories", "gap/CategoryOfReflexiveQuivers.gd");
ReadPackage( "FunctorCategories", "gap/FiniteCompletion.gd");
ReadPackage( "FunctorCategories", "gap/FreeDistributiveCompletion.gd");

ReadPackage( "FunctorCategories", "gap/AbelianClosure.gd");
if IsPackageMarkedForLoading( "Algebroids", ">= 2026.04-01" ) then
    ReadPackage( "FunctorCategories", "gap/with_algebroids/AbelianClosure.gd");
fi;

ReadPackage( "FunctorCategories", "gap/Functors.gd");
if IsPackageMarkedForLoading( "Algebroids", ">= 2026.04-01" ) then
    ReadPackage( "FunctorCategories", "gap/with_algebroids/Functors.gd");
fi;

ReadPackage( "FunctorCategories", "gap/DirectSumDecomposition.gd");
ReadPackage( "FunctorCategories", "gap/HomologicalMethods.gd");
ReadPackage( "FunctorCategories", "gap/QuotientsOfAlgebroidsFromDataTablesUsingPreSheaves.gd");
ReadPackage( "FunctorCategories", "gap/Tools.gd");
ReadPackage( "FunctorCategories", "gap/ToolsMethodRecordDeclarations.autogen.gd");
