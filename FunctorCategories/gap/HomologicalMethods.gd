# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Declarations
#

DeclareAttribute( "RadicalInclusionOfPreSheaf", IsObjectInPreSheafCategory );

DeclareOperation( "CoverElementByValueOfYonedaEmbedding", [ IsObjectInPreSheafCategory, IsCapCategoryMorphism, IsInt ] );

DeclareAttribute( "ProjectiveCoverObjectDataOfPreSheaf", IsObjectInPreSheafCategory );

DeclareAttribute( "WeakProjectiveCoverObjectDataOfPreSheaf", IsObjectInPreSheafCategory );

DeclareAttribute( "InjectiveEnvelope", IsObjectInPreSheafCategory );
