# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Reading the declaration part of the package.
#

ReadPackage( "Algebroids", "gap/QuiverRows.gd" );

ReadPackage( "Algebroids", "gap/FpCategories.gd");
ReadPackage( "Algebroids", "gap/Algebroids.gd");
ReadPackage( "Algebroids", "gap/Functors.gd");
ReadPackage( "Algebroids", "gap/CategoryFromNerveData.gd");
ReadPackage( "Algebroids", "gap/CategoryFromDataTables.gd");
ReadPackage( "Algebroids", "gap/AlgebroidFromDataTables.gd");
ReadPackage( "Algebroids", "gap/CategoryOfAlgebroids.gd");
ReadPackage( "Algebroids", "gap/Bialgebroids.gd");
ReadPackage( "Algebroids", "gap/SimplicialCategory.gd");
ReadPackage( "Algebroids", "gap/Tools.gd");
ReadPackage( "Algebroids", "gap/Quivers.gd");
ReadPackage( "Algebroids", "gap/PathCategories.gd");
ReadPackage( "Algebroids", "gap/QuotientsOfPathCategories.gd");
ReadPackage( "Algebroids", "gap/GroebnerBasesForPathCategories.gd");
ReadPackage( "Algebroids", "gap/LinearClosuresOfPathCategoriesAndTheirQuotients.gd" );

if IsPackageMarkedForLoading( "JuliaInterface", ">= 0.2" ) then
    ReadPackage( "Algebroids", "gap/Julia.gd" );
fi;
