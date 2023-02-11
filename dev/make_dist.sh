#!/bin/bash

set -e

packages="Algebroids CategoriesWithAmbientObjects CategoryConstructor CatReps ExteriorPowersCategories FiniteCocompletion FunctorCategories GradedCategories InternalModules IntrinsicCategories IntrinsicGradedModules IntrinsicModules LazyCategories Locales PreSheaves SubcategoriesForCAP Toposes ZariskiFrames "

base_dir="$PWD"

for pkg in ${packages}; do
  ./dev/release-gap-package --skip-existing-release --srcdir ${base_dir}/${pkg} --webdir ${base_dir}/gh-pages/${pkg} --update-script ${base_dir}/gh-pages/update.g --release-script ${base_dir}/dev/.release $@
done