# Chapter 2 Area and Coarea Acceptance Matrix

This matrix records the current checked source state against the Chapter 2 contract in
`pasted-text-1.txt` and Simon's *Introduction to Geometric Measure Theory* (2014 revision).
In the status column, `implemented` means that the declaring module and root aggregate build
without diagnostics, the available declaration-linter set passes, and the transitive axiom closure
is exactly `[propext, Classical.choice, Quot.sound]`; any exception is stated in its row.

| Headline | Simon reference | Exact declaration | Role | Status |
| --- | --- | --- | --- | --- |
| Lipschitz extension | Chapter 2, Section 1, Theorem 1.2, p. 40 | `Area.lipschitz_extension_real` in `GMT/Area/Jacobian.lean` | scalar extension interface | implemented |
| Rademacher interface | Chapter 2, Section 1, Theorem 1.4, pp. 40-42 | `LipschitzWith.ae_differentiableAt` from Mathlib, consumed by `GMT/Area/Jacobian.lean` | canonical finite-dimensional theorem | reused; root build and available declaration linters pass; axiom closure `[propext, Classical.choice, Quot.sound]` |
| Rademacher public wrapper | Chapter 2, Section 1, Theorem 1.4, pp. 40-42 | `Area.rademacher` in `GMT/Area/Jacobian.lean` | finite-dimensional real normed-space interface | implemented |
| Lusin closed-set continuity | Chapter 2, Section 1, proof of Theorem 1.5, pp. 43-44 | `StronglyMeasurable.exists_isClosed_continuousOn` in `GMT/Measure/Lusin.lean` | generic weakly regular finite-measure Lusin theorem; dependency for derivative-field continuity in the C1 approximation proof | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Global Lusin closed-set continuity | Chapter 2, Section 1, proof of Theorem 1.5, p. 44 | `StronglyMeasurable.exists_isClosed_continuousOn_of_isLocallyFiniteMeasure` in `GMT/Measure/Lusin.lean` | sigma-compact locally finite corollary over arbitrary measurable sets; consumes the finite-measure Lusin theorem on a canonical open spanning sequence | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Closed differentiability set with continuous derivative | Chapter 2, Section 1, proof of Theorem 1.5, p. 44 | `LipschitzWith.exists_isClosed_differentiableAt_continuousOn_fderiv` in `GMT/Analysis/Lipschitz.lean` | finite-dimensional Rademacher-Lusin interface; produces a closed set with arbitrarily small complement on which the map is differentiable and its derivative is continuous | implemented; consumes Rademacher and global Lusin, module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Closed Whitney one-jet extraction | Chapter 2, Section 1, proof of Theorem 1.5 and Theorem 1.6, pp. 42-44 | `exists_closed_measure_sdiff_lt_isWhitneyOneJetOn` in `GMT/Analysis/Whitney.lean` | generic locally finite extraction from a continuous derivative field; produces the local-on-compacts strict two-point compatibility required by Whitney extension | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Lipschitz Whitney one-jet extraction | Chapter 2, Section 1, proof of Theorem 1.5, p. 44 | `LipschitzWith.exists_isClosed_isWhitneyOneJetOn` in `GMT/Analysis/Whitney.lean` | finite-dimensional Rademacher-Lusin-Egoroff interface; produces a closed co-small set carrying the canonical derivative Whitney one-jet | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Whitney C1 extension | Chapter 2, Section 1, Theorem 1.6, pp. 42-43 | `IsWhitneyOneJetOn.exists_contDiff` in `GMT/Analysis/Whitney.lean` | canonical finite-dimensional closed-set extension preserving the one-jet values and derivatives | implemented; all cover, partition, and estimate machinery is private; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Closed-set C1 Lipschitz approximation | Chapter 2, Section 1, Theorem 1.5, pp. 42-44 | `LipschitzWith.exists_contDiff_eqOn_fderiv` in `GMT/Analysis/Whitney.lean` | finite-dimensional vector-valued primary producing a closed co-small set on which both values and Fréchet derivatives agree | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| C1 Lipschitz approximation | Chapter 2, Section 1, Theorem 1.5, pp. 42-44 | `LipschitzWith.exists_contDiff_measure_ne_lt` in `GMT/Analysis/Whitney.lean` | Simon-shaped mismatch-set corollary, generalized intrinsically to finite-dimensional vector-valued maps | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Hausdorff image estimate | Chapter 2, Section 1, Theorem 1.8(i), pp. 44-45 | `Area.lipschitz_image_hmeasure_le` in `GMT/Area/Jacobian.lean` | measure estimate | implemented |
| Dimension-lowering Lipschitz image-null estimate | Chapter 2, Section 1, Theorem 1.8(i), pp. 44-45 | `Area.lipschitz_dimension_lowering_image_null` in `GMT/Area/Jacobian.lean` | target-dimensional image nullity for Lipschitz maps from lower-dimensional finite-dimensional spaces | implemented |
| Euclidean Hausdorff normalization bridge | Chapter 2, Section 3, formula 3.1, p. 53 | `Measure.euclideanHausdorffMeasure_apply_eq_smul` in `GMT/Measure/Hausdorff.lean` | explicit pointwise bridge from normalized `μHE` to raw `μH` | implemented |
| Hausdorff image measurability | Chapter 2, Section 1, Theorem 1.8(i), pp. 44-45 | `LipschitzOnWith.nullMeasurableSet_image_hausdorffMeasure` in `GMT/Measure/Hausdorff.lean` | completion-aware measurable-image interface for finite-measure source sets | implemented |
| Hausdorff fiber multiplicity measurability | Chapter 2, Section 1, Theorem 1.8(ii), pp. 44-45 | `LipschitzOnWith.aemeasurable_encard_fiber` in `GMT/Measure/Hausdorff.lean` | measurable extended-cardinality fibers for finite Hausdorff source sets | implemented |
| Hausdorff fiber multiplicity estimate | Chapter 2, Section 1, Theorem 1.8(ii), pp. 44-45 | `LipschitzOnWith.lintegral_encard_fiber_le` in `GMT/Measure/Hausdorff.lean` | integrated fiber-cardinality bound with sharp `K^d` constant | implemented |
| Area multiplicity Hausdorff measurability | Chapter 2, Section 1, Theorem 1.8(ii), pp. 44-45 | `Area.aemeasurable_multiplicity` in `GMT/Area/Formula.lean` | Area-layer corollary exposing the consumer multiplicity definition | implemented |
| Area multiplicity Hausdorff estimate | Chapter 2, Section 1, Theorem 1.8(ii), pp. 44-45 | `Area.lintegral_multiplicity_le` in `GMT/Area/Formula.lean` | Area-layer integrated multiplicity bound | implemented |
| Intrinsic Jacobian | Chapter 2, Section 3, formulas 3.2-3.3, pp. 53-54 | `Area.jacobian`, `Area.jacobianWithin` in `GMT/Area/Jacobian.lean` | rectangular `LinearMap.normDet` interface | implemented |
| Intrinsic coarea Jacobian | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.coareaJacobian` in `GMT/Area/Jacobian.lean` | adjoint `LinearMap.normDet` interface, with nonsurjective vanishing and Gram-determinant identity | implemented |
| Rectangular norm-determinant continuity | Chapter 2, Section 3, formula 3.3, p. 53; Section 6, formula 6.2, p. 66 | `ContinuousLinearMap.continuous_normDet` in `GMT/Linear/NormDet.lean` | lower-layer continuity engine for area and coarea Jacobian measurability | implemented |
| Area Jacobian measurability | Chapter 2, Section 3, formulas 3.3-3.5, pp. 53-54 | `Area.measurable_jacobian` in `GMT/Area/Jacobian.lean` | measurable integrand interface obtained from measurable `fderiv` and norm-determinant continuity | implemented |
| Coarea Jacobian measurability | Chapter 2, Section 6, formulas 6.3 and 6.6, pp. 66-67 | `Area.measurable_coareaJacobian` in `GMT/Area/Jacobian.lean` | measurable integrand interface obtained from measurable `fderiv`, continuous adjoint, and norm-determinant continuity | implemented |
| Linear area formula | Chapter 2, Section 3, formula 3.1, p. 53 | `Area.linear_area_formula` in `GMT/Area/Jacobian.lean` | canonical linear primary | implemented |
| Linear area formula with volume bridge | Chapter 2, Section 3, formula 3.1, p. 53 | `Area.linear_area_formula_eq_volume` in `GMT/Area/Jacobian.lean` | normalized-measure corollary | implemented |
| Lower local area comparison | Chapter 2, Section 3, proof of formula 3.2, pp. 53-54 | `Area.mul_le_euclideanHausdorffMeasure_image_of_lt_normDet` in `GMT/Area/Formula.lean` | reusable rectangular comparison for maps approximated by an injective linear map; lower half of the higher-codimension area formula | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Upper local area comparison | Chapter 2, Section 3, proof of formulas 3.2-3.3, pp. 53-54 | `Area.euclideanHausdorffMeasure_image_le_mul_of_normDet_lt` in `GMT/Area/Formula.lean` | reusable rectangular comparison for maps approximated by any linear map; handles rank deficiency by injective augmentation | implemented; module builds silently, declaration linters pass, axiom closure `[propext, Classical.choice, Quot.sound]` |
| Injective area formula | Chapter 2, Section 3, formula 3.2, pp. 53-54 | `Area.injective_area_formula` in `GMT/Area/Formula.lean` | canonical rectangular differentiable interface over independent `E` and `F` | implemented |
| Lipschitz injective weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.injective_area_formula_weighted_lipschitz` in `GMT/Area/Formula.lean` | rectangular source-weighted fiber-sum identity for globally Lipschitz injective maps, with Rademacher null-set transfer | implemented |
| Lipschitz injective area formula, unweighted | Chapter 2, Section 3, formula 3.2, pp. 53-54 | `Area.injective_area_formula_lipschitz` in `GMT/Area/Formula.lean` | unweighted rectangular globally Lipschitz injective corollary | implemented |
| Equal-rank general area formula | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.area_formula_of_finrank_eq` in `GMT/Area/Formula.lean` | non-injective source-weighted fiber-sum identity across different equal-rank Euclidean spaces | implemented |
| Equal-rank general area formula, unweighted | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.area_formula_of_finrank_eq_unweighted` in `GMT/Area/Formula.lean` | unweighted equal-rank corollary | implemented |
| Equal-rank injective weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.injective_area_formula_weighted_of_finrank_eq` in `GMT/Area/Formula.lean` | source-weighted fiber-sum identity across equal-rank Euclidean spaces | implemented |
| Weighted injective area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.injective_area_formula_weighted` in `GMT/Area/Formula.lean` | rectangular source-weighted fiber-sum interface | implemented |
| General non-injective area formula | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.area_formula` in `GMT/Area/Formula.lean` | canonical rectangular measurable source-weighted fiber-sum identity | implemented for independent finite-dimensional `E` and `F` |
| General non-injective area formula, unweighted | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.area_formula_unweighted` in `GMT/Area/Formula.lean` | unweighted corollary of the canonical rectangular weighted identity | implemented |
| General weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.area_formula` in `GMT/Area/Formula.lean` | nonnegative measurable source weight summed over each fiber, with target measure in the source dimension | implemented for independent finite-dimensional `E` and `F` |
| Fiber multiplicity | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.multiplicity` in `GMT/Area/Formula.lean` | consumer-visible fiber object | implemented |
| Weighted fiber multiplicity | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.weightedMultiplicity` in `GMT/Area/Formula.lean` | consumer-visible source-weighted fiber sum | implemented |
| General image-weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.area_formula_image_weighted` in `GMT/Area/Formula.lean` | rectangular target-weight specialization with multiplicity | implemented |
| Scalar monotone area formula | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.monotone_area_formula_real` in `GMT/Area/Formula.lean` | non-injective real-map weighted formula via monotone decomposition | implemented as a scalar corollary |
| Scalar monotone area formula, unweighted | Chapter 2, Section 3, formula 3.2, pp. 53-54 | `Area.monotone_area_formula_real_unweighted` in `GMT/Area/Formula.lean` | scalar image measure identity | implemented as a scalar corollary |
| Scalar monotone area formula with multiplicity | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.monotone_area_formula_real_with_multiplicity` in `GMT/Area/Formula.lean` | explicit fiber-counting identity for monotone real maps | implemented as a scalar non-injective corollary |
| Linear coarea formula | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_formula` in `GMT/Area/Coarea.lean` | canonical arbitrary linear identity over the original codomain, including the rank-deficient and impossible-dimension cases | implemented |
| Weighted linear coarea formula | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_formula_weighted` in `GMT/Area/Coarea.lean` | canonical measurable nonnegative identity over the original codomain | implemented |
| Product linear coarea/Fubini formula | Chapter 2, Section 6, formula 6.1, p. 65 | `Area.linear_coarea_formula_prod` in `GMT/Area/Coarea.lean` | product-measure projection identity | implemented |
| Product linear coarea formula with intrinsic fiber measure | Chapter 2, Section 6, formula 6.1, p. 65 | `Area.linear_coarea_formula_prod_hmeasure` in `GMT/Area/Coarea.lean` | projection identity with normalized fiber Hausdorff measure | implemented |
| Weighted product linear coarea/Fubini formula | Chapter 2, Section 6, formulas 6.1-6.2, pp. 65-66 | `Area.linear_coarea_formula_prod_weighted` in `GMT/Area/Coarea.lean` | product-measure identity for a measurable nonnegative weight | implemented |
| Weighted product linear coarea with intrinsic fiber measure | Chapter 2, Section 6, formulas 6.1-6.2, pp. 65-66 | `Area.linear_coarea_formula_prod_hmeasure_weighted` in `GMT/Area/Coarea.lean` | product identity with normalized fiber Hausdorff measure | implemented |
| Orthogonal-slice linear coarea formula | Chapter 2, Section 6, formulas 6.1-6.2, pp. 65-66 | `Area.linear_coarea_formula_orthogonal` in `GMT/Area/Coarea.lean` | intrinsic higher-codimension slice disintegration | implemented via Mathlib's affine-subspace disintegration |
| Surjective linear coarea formula | Chapter 2, Section 6, formulas 6.1-6.2, pp. 65-66 | `Area.linear_coarea_formula_surjective` in `GMT/Area/Coarea.lean` | canonical arbitrary-surjective linear identity with intrinsic restricted-map factor | implemented |
| Weighted surjective linear coarea formula | Chapter 2, Section 6, formulas 6.1-6.2, pp. 65-66 | `Area.linear_coarea_formula_surjective_weighted` in `GMT/Area/Coarea.lean` | measurable nonnegative weight on the domain with intrinsic restricted-map factor | implemented |
| Range-valued linear coarea formula | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_formula_range` in `GMT/Area/Coarea.lean` | coarea identity over the actual range of an arbitrary linear map | implemented |
| Weighted range-valued linear coarea formula | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_formula_range_weighted` in `GMT/Area/Coarea.lean` | measurable nonnegative weight over the actual range of an arbitrary linear map | implemented |
| Coarea factor adjoint bridge | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_factor_eq_normDet_adjoint` in `GMT/Area/Coarea.lean` | identifies the restricted factor with the intrinsic adjoint norm determinant for surjective maps | implemented |
| Coarea factor square | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_factor_sq` in `GMT/Area/Coarea.lean` | identifies the square of the intrinsic coarea factor with the determinant of `L ∘ₗ L.adjoint` | implemented |
| Restricted coarea factor square | Chapter 2, Section 6, formula 6.2, p. 66 | `Area.linear_coarea_restricted_factor_sq` in `GMT/Area/Coarea.lean` | supporting Gram-operator identity on the kernel orthogonal complement | implemented |
| Canonical linear coarea coordinates | Chapter 2, Section 6, proof of formula 6.2, p. 66 | `Area.linearCoareaCoordinates`, `Area.linearCoareaCoordinates_apply`, and `Area.linear_coarea_coordinates_normDet` in `GMT/Area/Coarea.lean` | canonical map to the codomain and kernel coordinates, with evaluation and norm-determinant laws | implemented |
| Dimension-lowering C¹ image-null corollary | Chapter 2, Section 6, formula 6.4, pp. 66-67 | `Area.dimension_lowering_image_null` in `GMT/Area/Coarea.lean` | full image nullity when domain dimension is smaller than codomain | implemented via Hausdorff-dimension bound; not the coarea-derived Sard proof |
| Finite-partition image-weighted area engine | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.area_formula_of_finite_injective_partition_image_weighted` in `GMT/Area/Formula.lean` | reusable rectangular finite injective-partition engine for target weights | implemented |
| Countable-partition area engine | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.area_formula_of_countable_injective_partition` in `GMT/Area/Formula.lean` | reusable rectangular countable injective-partition engine for source-weighted fiber sums | implemented |
| Coarea fiber-integral measurability | Chapter 2, Section 6, formulas 6.3 and 6.6, pp. 66-67 | `Area.aemeasurable_coarea_fiber_integral` in `GMT/Area/Coarea.lean` | measurable nonlinear weighted fiber integral | implemented |
| General weighted coarea formula | Chapter 2, Section 6, formula 6.6, p. 67 | `Area.coarea_formula_weighted` in `GMT/Area/Coarea.lean` | canonical nonlinear weighted fiber identity, including the rank-deficient locus | implemented |
| General coarea formula | Chapter 2, Section 6, formula 6.3, p. 66 | `Area.coarea_formula` in `GMT/Area/Coarea.lean` | unweighted corollary of the canonical weighted identity | implemented |
| Lipschitz coarea fiber measurability | Chapter 2, Section 1, Theorem 1.9, pp. 45-46 | `Area.aemeasurable_lipschitz_coarea_fiber_measure` in `GMT/Area/Coarea.lean` | completion-measurable fiber-measure function for globally Lipschitz finite-dimensional Euclidean maps | implemented |
| Sharp normalized Lipschitz coarea inequality | Chapter 2, Section 1, Theorem 1.9, pp. 45-46 | `Area.lipschitz_coarea_inequality` in `GMT/Area/Coarea.lean` | canonical normalized `μHE` inequality with sharp coefficient `1` | implemented |
| Simon volume-ratio Lipschitz coarea inequality | Chapter 2, Section 1, Theorem 1.9, pp. 45-46 | `Area.lipschitz_coarea_inequality_volume_ratio` in `GMT/Area/Coarea.lean` | Simon's printed `ω_m ω_k / ω_(m+k)` coefficient in normalized Euclidean notation | implemented as an ambient-global finite-dimensional specialization |
| Norm determinant bound | Chapter 2, Section 1, Theorem 1.9, pp. 45-46 | `ContinuousLinearMap.normDet_le_norm_pow` in `GMT/Linear/NormDet.lean` | intrinsic lower-layer bound used to estimate the coarea Jacobian by the Lipschitz constant | implemented |
| Euclidean unit-ball volume ratio bound | Chapter 2, Section 1, Theorem 1.9, pp. 45-46 | `MeasureTheory.euclideanUnitBallVolume_add_le_mul` in `GMT/Measure/Density.lean` | lower-layer product-ball comparison yielding the Simon coefficient from the sharp normalized estimate | implemented |
| Compact Hausdorff-fiber measurability | Chapter 2, Section 1, proof of Theorem 1.9, pp. 45-46 | `ContinuousOn.measurable_hausdorffMeasure_fiber` in `GMT/Measure/Hausdorff.lean` | lower-layer measurable fiber-measure interface for continuous maps on compact sets | implemented |
| Measurable Hausdorff-fiber majorant | Chapter 2, Section 1, proof of Theorem 1.9, pp. 45-46 | `LipschitzOnWith.exists_measurable_hausdorffMeasure_fiber_majorant` in `GMT/Measure/Hausdorff.lean` | lower-layer integrated measurable majorant used for critical and discarded null-set fibers | implemented |
| Euclidean C1 submanifold predicate | Chapter 2, Section 4, local submanifold interface used in Section 6, pp. 57-60 | `IsContDiffSubmanifold` in `GMT/Area/Submanifold.lean` | intrinsic local-parametrization predicate used by the regular-fiber conclusion | implemented |
| Closed critical locus | Chapter 2, Section 6, Theorem 6.4, p. 67 | `Area.isClosed_critical_set` in `GMT/Area/Coarea.lean` | reusable critical-set topology interface | implemented |
| Regular fiber submanifold | Chapter 2, Section 6, Theorem 6.4, p. 67 | `Area.isContDiffSubmanifold_regular_fiber` in `GMT/Area/Coarea.lean` | implicit-function-theorem description of the regular fiber | implemented |
| Critical fiber nullity | Chapter 2, Section 6, Theorem 6.4, p. 67 | `Area.ae_critical_fiber_measure_eq_zero` in `GMT/Area/Coarea.lean` | coarea-derived almost-everywhere critical-fiber nullity | implemented |
| C1 Sard-type consequence | Chapter 2, Section 6, Theorem 6.4, p. 67 | `Area.sard_fiber_decomposition` in `GMT/Area/Coarea.lean` | regular submanifold plus closed critical remainder of zero fiber measure | implemented |

The following load-bearing public dependencies are also part of the delivered surface. They are
supporting API rather than additional Simon headlines:
`StronglyMeasurable.exists_isClosed_continuousOn`,
`StronglyMeasurable.exists_isClosed_continuousOn_of_isLocallyFiniteMeasure`,
`LipschitzWith.exists_isClosed_differentiableAt_continuousOn_fderiv`,
`HasStrictFDerivWithinAt`, `IsWhitneyOneJetOn`,
`exists_closed_measure_sdiff_lt_isWhitneyOneJetOn`,
`LipschitzWith.exists_isClosed_isWhitneyOneJetOn`,
`IsWhitneyOneJetOn.exists_contDiff`,
`LipschitzWith.exists_contDiff_eqOn_fderiv`,
`LipschitzWith.exists_contDiff_measure_ne_lt`,
`ApproximatesLinearOn.ae_norm_fderiv_sub_le`,
`Area.jacobian_nonneg`,
`Area.jacobian_of_hasFDerivAt`, `Area.jacobian_of_hasFDerivWithinAt`,
`Area.jacobian_continuousLinearMap`, `Area.jacobian_linearMap`, `Area.jacobian_zero`,
`Area.jacobian_id`, `Area.measurable_jacobian`,
`LinearMap.normDet_adjoint_of_finrank_eq`, `ContinuousLinearMap.continuous_normDet`,
`Area.coareaJacobian_nonneg`, `Area.coareaJacobian_of_hasFDerivAt`,
`Area.coareaJacobian_continuousLinearMap`, `Area.coareaJacobian_linearMap`,
`Area.coareaJacobian_eq_jacobian_of_finrank_eq`,
`Area.coareaJacobian_eq_zero_of_not_surjective`,
`Area.coareaJacobian_eq_zero_of_finrank_lt`, `Area.coareaJacobian_sq`,
`Area.coareaJacobian_zero`, `Area.coareaJacobian_id`,
`Area.measurable_coareaJacobian`,
`Area.multiplicity_eq_zero_of_not_mem_image`,
`Area.multiplicity_eq_one_of_injOn`, `Area.weightedMultiplicity`,
`Area.weightedMultiplicity_one`, `Area.weightedMultiplicity_comp`,
`Area.antitone_area_formula_real`, `Area.antitone_area_formula_real_unweighted`,
`Area.area_formula_of_finite_injective_partition_image_weighted`,
`Area.area_formula_of_countable_injective_partition`,
`Area.area_formula_of_countable_injective_partition_image_weighted`, `Area.area_formula`,
`Area.area_formula_image_weighted`, `Area.area_formula_unweighted`,
`Area.injective_area_formula_weighted_lipschitz`,
`Area.injective_area_formula_image_weighted_lipschitz`,
`Area.injective_area_formula_lipschitz`, `Area.area_formula_of_finrank_eq`,
`Area.area_formula_image_weighted_of_finrank_eq`, `Area.area_formula_of_finrank_eq_unweighted`,
`Area.injective_area_formula_weighted_of_finrank_eq`,
`Area.injective_area_formula_image_weighted_of_finrank_eq`, `Area.linear_coarea_formula_surjective`,
`Area.linear_coarea_formula_surjective_weighted`, `Area.linear_coarea_formula_range`,
`Area.linear_coarea_formula_range_weighted`, `Area.linear_coarea_factor_eq_normDet_adjoint`,
`Area.linear_coarea_factor_sq`, `Area.linear_coarea_restricted_factor_sq`,
`Area.linearCoareaCoordinates`, `Area.linearCoareaCoordinates_apply`,
`Area.linear_coarea_coordinates_normDet`,
`ContinuousLinearMap.normDet_le_norm_pow`,
`MeasureTheory.euclideanUnitBallVolume_add_le_mul`,
`ContinuousOn.measurable_hausdorffMeasure_fiber`,
`LipschitzOnWith.exists_measurable_hausdorffMeasure_fiber_majorant`,
`Area.aemeasurable_coarea_fiber_integral`, `Area.coarea_formula_weighted`,
`Area.aemeasurable_lipschitz_coarea_fiber_measure`, `Area.lipschitz_coarea_inequality`,
`IsContDiffSubmanifold`, `Area.isClosed_critical_set`,
`Area.isContDiffSubmanifold_regular_fiber`, and `Area.ae_critical_fiber_measure_eq_zero`.
Their exact checked types are recorded below with the headline signatures; each remains in its stated
topic home and is consumed by the area/coarea proof forest.

The finite Chapter 2 suite is implemented. The general rectangular area formula is primary, with
injective, image-weighted, unweighted, Lipschitz, and equal-rank corollaries. The nonlinear weighted
coarea formula is primary over `C¹` maps when the codomain dimension is strictly smaller, and the
unweighted formula is its corollary. The Sard result decomposes almost every fiber into its regular
submanifold part and a closed critical remainder of zero fiber Hausdorff measure.

The Simon 1.9 correspondence has one explicit source-fidelity boundary. Simon assumes a map defined
and Lipschitz only on the measured set `A`; the Lean declarations take a globally Lipschitz ambient
map and a completion-measurable set. No unrestricted-domain Kirszbraun extension theorem is available
in the pinned Mathlib revision, so the Lean volume-ratio theorem is an ambient-global specialization,
not the literal full-domain statement of Simon 1.9. For Simon 6.4, the regular fiber is explicitly
returned as empty or a `C¹` submanifold, matching the source wording.

## Exact checked signatures

The following are the elaborated signatures checked from the current source with `#check`.
They are included here so the matrix records the actual public contracts rather than only source
names. `NNReal`, `ENNReal`, `μHE`, and `volume` abbreviate the corresponding Mathlib types and
measures in the displayed output.

```text
Area.lipschitz_extension_real {X} [PseudoMetricSpace X] {s : Set X} {f : X → ℝ} {K : NNReal}
  (hf : LipschitzOnWith K f s) : ∃ g, LipschitzWith K g ∧ Set.EqOn f g s
Area.lipschitz_image_hmeasure_le {X Y} [EMetricSpace X] [EMetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {f : X → Y} {K : NNReal} (hf : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) (s : Set X) :
  μH[d] (f '' s) ≤ ↑K ^ d * μH[d] s
Area.lipschitz_dimension_lowering_image_null {E F} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F]
  [BorelSpace F] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) (hEF : finrank ℝ E < finrank ℝ F) :
  μHE[finrank ℝ F] (Set.range f) = 0
Area.rademacher {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] {f : E → F} {K : NNReal} (hf : LipschitzWith K f) :
  ∀ᵐ x ∂(Measure.addHaar : Measure E), DifferentiableAt ℝ f x
StronglyMeasurable.exists_isClosed_continuousOn {X Y} [MeasurableSpace X]
  [TopologicalSpace X] [OpensMeasurableSpace X] {mu : Measure X} [mu.WeaklyRegular]
  [PseudoMetricSpace Y] {f : X → Y} (hf : StronglyMeasurable f) {s : Set X}
  (hs : MeasurableSet s) (hmu : mu s ≠ ∞) {ε : ENNReal} (hε : ε ≠ 0) :
  ∃ t ⊆ s, IsClosed t ∧ mu (s \ t) < ε ∧ ContinuousOn f t
StronglyMeasurable.exists_isClosed_continuousOn_of_isLocallyFiniteMeasure {X Y}
  [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {mu : Measure X} [mu.WeaklyRegular] [SigmaCompactSpace X]
  [IsLocallyFiniteMeasure mu] [PseudoMetricSpace Y] {f : X → Y}
  (hf : StronglyMeasurable f) {s : Set X} (hs : MeasurableSet s)
  {ε : ENNReal} (hε : ε ≠ 0) :
  ∃ t ⊆ s, IsClosed t ∧ mu (s \ t) < ε ∧ ContinuousOn f t
LipschitzWith.exists_isClosed_differentiableAt_continuousOn_fderiv {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) {ε : ENNReal} (hε : ε ≠ 0) :
  ∃ s, IsClosed s ∧ Measure.addHaar sᶜ < ε ∧
    (∀ x ∈ s, DifferentiableAt ℝ f x) ∧ ContinuousOn (fderiv ℝ f) s
HasStrictFDerivWithinAt {𝕜 E F} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) : Prop
IsWhitneyOneJetOn {𝕜 E F} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] (f : E → F) (f' : E → E →L[𝕜] F) (s : Set E) : Prop
exists_closed_measure_sdiff_lt_isWhitneyOneJetOn {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [IsLocallyFiniteMeasure mu] [ProperSpace E]
  (f : E → F) (s : Set E) (hs : IsClosed s) (f' : E → E →L[ℝ] F)
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
  (hf'cont : ContinuousOn f' s) {ε : ENNReal} (εpos : 0 < ε) :
  ∃ K ⊆ s, IsClosed K ∧ mu (s \ K) < ε ∧ IsWhitneyOneJetOn f f' K
LipschitzWith.exists_isClosed_isWhitneyOneJetOn {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {f : E → F} {K : NNReal} (hf : LipschitzWith K f)
  {ε : ENNReal} (hε : ε ≠ 0) :
  ∃ s, IsClosed s ∧ Measure.addHaar sᶜ < ε ∧ IsWhitneyOneJetOn f (fderiv ℝ f) s
IsWhitneyOneJetOn.exists_contDiff {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E → E →L[ℝ] F}
  {s : Set E} (h : IsWhitneyOneJetOn f f' s) (hs : IsClosed s) :
  ∃ g, ContDiff ℝ 1 g ∧ EqOn g f s ∧ EqOn (fderiv ℝ g) f' s
LipschitzWith.exists_contDiff_eqOn_fderiv {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) {ε : ENNReal} (hε : ε ≠ 0) :
  ∃ g s, IsClosed s ∧ Measure.addHaar sᶜ < ε ∧ ContDiff ℝ 1 g ∧
    EqOn g f s ∧ EqOn (fderiv ℝ g) (fderiv ℝ f) s
LipschitzWith.exists_contDiff_measure_ne_lt {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) {ε : ENNReal} (hε : ε ≠ 0) :
  ∃ g, ContDiff ℝ 1 g ∧
    Measure.addHaar ({x | f x ≠ g x} ∪ {x | fderiv ℝ f x ≠ fderiv ℝ g x}) < ε
ApproximatesLinearOn.ae_norm_fderiv_sub_le {E F}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure] {s : Set E} {f : E → F}
  {A : E →L[ℝ] F} {δ : NNReal} (hf : ApproximatesLinearOn f A s δ)
  (hs : MeasurableSet s) (f' : E → E →L[ℝ] F)
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
  ∀ᵐ x ∂mu.restrict s, ‖f' x - A‖₊ ≤ δ
Area.jacobian {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E → F) (x : E) : ℝ
Area.jacobianWithin {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E → F) (s : Set E) (x : E) : ℝ
Area.jacobian_nonneg {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E → F) (x : E) :
  0 ≤ Area.jacobian f x
ContinuousLinearMap.continuous_normDet {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
  Continuous (fun L : E →L[ℝ] F => L.toLinearMap.normDet)
Area.measurable_jacobian {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] (f : E → F) :
  Measurable (Area.jacobian f)
Area.measurable_coareaJacobian {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] (f : E → F) :
  Measurable (Area.coareaJacobian f)
Measure.euclideanHausdorffMeasure_apply_eq_smul {X} [EMetricSpace X] [MeasurableSpace X]
  [BorelSpace X] (d : ℕ) (s : Set X) :
  μHE[d] s = Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] * μH[d] s
LipschitzOnWith.aemeasurable_encard_fiber {X Y} [MetricSpace X] [SigmaCompactSpace X]
  [MetricSpace Y] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {f : X → Y} {s : Set X} {K : NNReal} {d : ℝ} (hf : LipschitzOnWith K f s)
  (hd : 0 ≤ d) (hs : NullMeasurableSet s μH[d]) (hfin : μH[d] s ≠ ∞) :
  AEMeasurable (fun y => ((s ∩ f ⁻¹' {y}).encard : ℕ∞) : Y → ℝ≥0∞) μH[d]
LipschitzOnWith.lintegral_encard_fiber_le {X Y} [MetricSpace X] [SigmaCompactSpace X]
  [MetricSpace Y] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {f : X → Y} {s : Set X} {K : NNReal} {d : ℝ} (hf : LipschitzOnWith K f s)
  (hd : 0 ≤ d) (hs : NullMeasurableSet s μH[d]) (hfin : μH[d] s ≠ ∞) :
  ∫⁻ y : Y, ((s ∩ f ⁻¹' {y}).encard : ℕ∞) ∂μH[d] ≤ (K : ℝ≥0∞)^d * μH[d] s
Area.aemeasurable_multiplicity {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → E} {s : Set E}
  {K : NNReal} (hf : LipschitzOnWith K f s)
  (hs : NullMeasurableSet s μH[(Module.finrank ℝ E : ℝ)])
  (hfin : μH[(Module.finrank ℝ E : ℝ)] s ≠ ∞) :
  AEMeasurable (Area.multiplicity f s) μH[(Module.finrank ℝ E : ℝ)]
Area.lintegral_multiplicity_le {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → E} {s : Set E}
  {K : NNReal} (hf : LipschitzOnWith K f s)
  (hs : NullMeasurableSet s μH[(Module.finrank ℝ E : ℝ)])
  (hfin : μH[(Module.finrank ℝ E : ℝ)] s ≠ ∞) :
  ∫⁻ y : E, Area.multiplicity f s y ∂μH[(Module.finrank ℝ E : ℝ)] ≤
    (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * μH[(Module.finrank ℝ E : ℝ)] s
Area.jacobian_of_hasFDerivAt {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : E → F} {L : E →L[ℝ] F} {x : E}
  (h : HasFDerivAt f L x) : Area.jacobian f x = L.toLinearMap.normDet
Area.jacobian_of_hasFDerivWithinAt {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : E → F} {L : E →L[ℝ] F}
  {s : Set E} {x : E} (h : HasFDerivWithinAt f L s x) (hs : UniqueDiffWithinAt ℝ s x) :
  Area.jacobianWithin f s x = L.toLinearMap.normDet
Area.jacobian_continuousLinearMap {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (L : E →L[ℝ] F) (x : E) :
  Area.jacobian L x = L.toLinearMap.normDet
Area.jacobian_linearMap {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (L : E →ₗ[ℝ] F) (x : E) :
  Area.jacobian L x = L.normDet
Area.jacobian_zero {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (x : E) :
  Area.jacobian (0 : E → F) x = 0 ^ finrank ℝ E
Area.jacobian_id {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (x : E) : Area.jacobian (id : E → E) x = 1
LinearMap.normDet_adjoint_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F)
  (h : finrank ℝ E = finrank ℝ F) : L.adjoint.normDet = L.normDet
Area.coareaJacobian {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (f : E → F) (x : E) : ℝ
Area.coareaJacobian_nonneg {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (f : E → F) (x : E) : 0 ≤ Area.coareaJacobian f x
Area.coareaJacobian_of_hasFDerivAt {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {f : E → F} {L : E →L[ℝ] F} {x : E}
  (h : HasFDerivAt f L x) : Area.coareaJacobian f x = L.toLinearMap.adjoint.normDet
Area.coareaJacobian_continuousLinearMap {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →L[ℝ] F) (x : E) :
  Area.coareaJacobian L x = L.toLinearMap.adjoint.normDet
Area.coareaJacobian_linearMap {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) (x : E) :
  Area.coareaJacobian L x = L.adjoint.normDet
Area.coareaJacobian_eq_jacobian_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (h : finrank ℝ E = finrank ℝ F)
  (f : E → F) (x : E) : Area.coareaJacobian f x = Area.jacobian f x
Area.coareaJacobian_eq_zero_of_not_surjective {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {L : E →L[ℝ] F}
  {x : E} (hf : HasFDerivAt f L x) (hL : ¬ Function.Surjective L) :
  Area.coareaJacobian f x = 0
Area.coareaJacobian_eq_zero_of_finrank_lt {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (h : finrank ℝ E < finrank ℝ F)
  (f : E → F) (x : E) : Area.coareaJacobian f x = 0
Area.coareaJacobian_sq {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (f : E → F) (x : E) :
  Area.coareaJacobian f x ^ 2 =
    ((fderiv ℝ f x).toLinearMap ∘ₗ (fderiv ℝ f x).toLinearMap.adjoint).det
Area.coareaJacobian_zero {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (x : E) :
  Area.coareaJacobian (0 : E → F) x = 0 ^ finrank ℝ F
Area.coareaJacobian_id {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (x : E) : Area.coareaJacobian (id : E → E) x = 1
Area.linear_area_formula {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (L : E →ₗ[ℝ] F) (s : Set E) :
  μHE[finrank ℝ E] (L '' s) = ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s
Area.linear_area_formula_eq_volume {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (L : E →ₗ[ℝ] F) (s : Set E) :
  μHE[finrank ℝ E] (L '' s) = ENNReal.ofReal L.normDet * volume s
Area.mul_le_euclideanHausdorffMeasure_image_of_lt_normDet {E F}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (A : E →L[ℝ] F) {c : NNReal}
  (hc : ↑c < ENNReal.ofReal A.toLinearMap.normDet) :
  ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (s : Set E) (f : E → F),
    ApproximatesLinearOn f A s δ →
      ↑c * μHE[finrank ℝ E] s ≤ μHE[finrank ℝ E] (f '' s)
Area.euclideanHausdorffMeasure_image_le_mul_of_normDet_lt {E F}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (A : E →L[ℝ] F) {c : NNReal}
  (hc : ENNReal.ofReal A.toLinearMap.normDet < ↑c) :
  ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (s : Set E) (f : E → F),
    ApproximatesLinearOn f A s δ →
      μHE[finrank ℝ E] (f '' s) ≤ ↑c * μHE[finrank ℝ E] s
Area.injective_area_formula {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {f' : E → E →L[ℝ] F}
  {s : Set E} (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hfinj : Set.InjOn f s) :
  μHE[finrank ℝ E] (f '' s) =
    ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet) ∂μHE[finrank ℝ E]
Area.injective_area_formula_weighted_lipschitz {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  {s : Set E} {K : NNReal} (g : E → ENNReal) (hs : MeasurableSet s)
  (hf : LipschitzWith K f) (hfinj : Set.InjOn f s) (hg : Measurable g) :
  ∫⁻ y : F, Area.weightedMultiplicity f s g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x) ∂μHE[finrank ℝ E]
Area.injective_area_formula_image_weighted_lipschitz {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  {s : Set E} {K : NNReal} (g : F → ENNReal) (hs : MeasurableSet s)
  (hf : LipschitzWith K f) (hfinj : Set.InjOn f s) :
  ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x) ∂μHE[finrank ℝ E]
Area.injective_area_formula_lipschitz {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  {s : Set E} {K : NNReal} (hs : MeasurableSet s)
  (hf : LipschitzWith K f) (hfinj : Set.InjOn f s) :
  μHE[finrank ℝ E] (f '' s) =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) ∂μHE[finrank ℝ E]
Area.injective_area_formula_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  {f' : E → E →L[ℝ] F} {s : Set E} (g : E → ENNReal)
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
  (hfinj : Set.InjOn f s) (hg : Measurable g) :
  ∫⁻ y : F, Area.weightedMultiplicity f s g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x) ∂μHE[finrank ℝ E]
Area.injective_area_formula_image_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  {f' : E → E →L[ℝ] F} {s : Set E} (g : F → ENNReal)
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
  (hfinj : Set.InjOn f s) :
  ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x) ∂μHE[finrank ℝ E]
Area.multiplicity {E F} (f : E → F) (s : Set E) (y : F) : ENNReal
Area.weightedMultiplicity {E F} (f : E → F) (s : Set E) (g : E → ENNReal) (y : F) : ENNReal
Area.weightedMultiplicity_one {E F} (f : E → F) (s : Set E) (y : F) :
  Area.weightedMultiplicity f s (fun _ => 1) y = Area.multiplicity f s y
Area.weightedMultiplicity_comp {E F} (f : E → F) (s : Set E) (g : F → ENNReal) (y : F) :
  Area.weightedMultiplicity f s (g ∘ f) y = Area.multiplicity f s y * g y
Area.multiplicity_eq_zero_of_not_mem_image {E F} {f : E → F} {s : Set E} {y : F}
  (hy : y ∉ f '' s) : Area.multiplicity f s y = 0
Area.multiplicity_eq_one_of_injOn {E F} {f : E → F} {s : Set E} (hf : Set.InjOn f s)
  {y : F} (hy : y ∈ f '' s) : Area.multiplicity f s y = 1
Area.monotone_area_formula_real {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ENNReal)
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
  (hf : MonotoneOn f s) : ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x)
Area.monotone_area_formula_real_unweighted {f f' : ℝ → ℝ} {s : Set ℝ}
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
  (hf : MonotoneOn f s) : volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal (f' x)
Area.antitone_area_formula_real {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ENNReal)
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
  (hf : AntitoneOn f s) : ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (-f' x) * g (f x)
Area.antitone_area_formula_real_unweighted {f f' : ℝ → ℝ} {s : Set ℝ}
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
  (hf : AntitoneOn f s) : volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal (-f' x)
Area.monotone_area_formula_real_with_multiplicity {f f' : ℝ → ℝ} {s : Set ℝ}
  (g : ℝ → ENNReal) (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) :
  ∫⁻ y, Area.multiplicity f s y * g y = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x)
Area.area_formula_of_finite_injective_partition_image_weighted {E F}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} (n : ℕ) (t : Fin n → Set E)
  (g : F → ENNReal) (hpart : ⋃ i, t i = s) (ht : ∀ i, MeasurableSet (t i))
  (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (t i) (t j))
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i, InjOn f (t i))
  (hg : Measurable g) :
  ∫⁻ y : F, Area.multiplicity f s y * g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x) ∂μHE[finrank ℝ E]
Area.area_formula {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (g : E → ENNReal) (hs : MeasurableSet s)
  (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
  ∫⁻ y : F, Area.weightedMultiplicity f s g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x) ∂μHE[finrank ℝ E]
Area.area_formula_image_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  {s : Set E} (g : F → ENNReal) (hs : MeasurableSet s)
  (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
  ∫⁻ y : F, Area.multiplicity f s y * g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x) ∂μHE[finrank ℝ E]
Area.area_formula_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (g : E → ENNReal) (hfinrank : finrank ℝ E = finrank ℝ F)
  (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
  ∫⁻ y, Area.weightedMultiplicity f s g y ∂μHE[finrank ℝ F] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x)
Area.area_formula_image_weighted_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (g : F → ENNReal) (hfinrank : finrank ℝ E = finrank ℝ F)
  (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
  ∫⁻ y, Area.multiplicity f s y * g y ∂μHE[finrank ℝ F] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
Area.area_formula_of_finrank_eq_unweighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (hfinrank : finrank ℝ E = finrank ℝ F) (hs : MeasurableSet s)
  (hf : ContDiff ℝ 1 f) :
  ∫⁻ y, Area.multiplicity f s y ∂μHE[finrank ℝ F] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x)
Area.injective_area_formula_weighted_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} (g : E → ENNReal)
  (hfinrank : finrank ℝ E = finrank ℝ F) (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : Set.InjOn f s)
  (hg : Measurable g) :
  ∫⁻ y, Area.weightedMultiplicity f s g y ∂μHE[finrank ℝ F] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x)
Area.injective_area_formula_image_weighted_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (g : F → ENNReal) (hfinrank : finrank ℝ E = finrank ℝ F)
  (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) (hg : Measurable g)
  (hfinj : Set.InjOn f s) :
  ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ F] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
Area.area_formula_of_countable_injective_partition {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
  (t : ℕ → Set E) (g : E → ENNReal)
  (hpart : ⋃ i, t i = s) (ht : ∀ i, MeasurableSet (t i))
  (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (t i) (t j))
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i, InjOn f (t i))
  (hg : Measurable g) :
  ∫⁻ y : F, Area.weightedMultiplicity f s g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x) ∂μHE[finrank ℝ E]
Area.area_formula_of_countable_injective_partition_image_weighted {E F}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
  (t : ℕ → Set E) (g : F → ENNReal) (hpart : ⋃ i, t i = s)
  (ht : ∀ i, MeasurableSet (t i))
  (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (t i) (t j))
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i, InjOn f (t i))
  (hg : Measurable g) :
  ∫⁻ y : F, Area.multiplicity f s y * g y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x) ∂μHE[finrank ℝ E]
Area.area_formula_unweighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {s : Set E} (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) :
  ∫⁻ y : F, Area.multiplicity f s y ∂μHE[finrank ℝ E] =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) ∂μHE[finrank ℝ E]
Area.linear_coarea_formula {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (L : E →ₗ[ℝ] F) (s : Set E) (hs : MeasurableSet s) :
  ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ L ⁻¹' {y}) =
    ENNReal.ofReal L.adjoint.normDet * μHE[finrank ℝ E] s
Area.linear_coarea_formula_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (L : E →ₗ[ℝ] F)
  (s : Set E) (hs : MeasurableSet s) (g : E → ENNReal) (hg : Measurable g) :
  ∫⁻ y : F, ∫⁻ x in s ∩ L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] =
    ENNReal.ofReal L.adjoint.normDet * ∫⁻ x in s, g x ∂μHE[finrank ℝ E]
Area.linear_coarea_formula_prod {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (s : Set (E × F)) (hs : MeasurableSet s) :
  ∫⁻ y : E, volume (Prod.mk y ⁻¹' s) = (volume.prod volume) s
Area.linear_coarea_formula_prod_hmeasure {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (s : Set (E × F))
  (hs : MeasurableSet s) :
  ∫⁻ y : E, μHE[finrank ℝ F] (Prod.mk y ⁻¹' s) = (volume.prod volume) s
Area.linear_coarea_formula_prod_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (s : Set (E × F)) (hs : MeasurableSet s) {g : E × F → ENNReal} (hg : Measurable g) :
  ∫⁻ y : E, ∫⁻ z in Prod.mk y ⁻¹' s, g (y, z) = ∫⁻ p in s, g p
Area.linear_coarea_formula_prod_hmeasure_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] (s : Set (E × F)) (hs : MeasurableSet s)
  {g : E × F → ENNReal} (hg : Measurable g) :
  ∫⁻ y : E, ∫⁻ z in Prod.mk y ⁻¹' s, g (y, z) ∂μHE[finrank ℝ F] = ∫⁻ p in s, g p
Area.linear_coarea_formula_orthogonal {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (V : Submodule ℝ E) (s : Set E) (hs : MeasurableSet s) :
  μHE[finrank ℝ E] s = ∫⁻ x : AffineSubspace.mk' (0 : E) V,
    μHE[finrank ℝ Vᗮ] (s ∩ AffineSubspace.mk' x.val Vᗮ)
      ∂μHE[finrank ℝ V]
Area.linear_coarea_formula_surjective {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) (s : Set E)
  (hs : MeasurableSet s) :
  ∫⁻ y : F, μHE[finrank ℝ (LinearMap.ker L)] (s ∩ L ⁻¹' {y}) =
        ENNReal.ofReal (L.domRestrict (LinearMap.ker L)ᗮ).normDet * μHE[finrank ℝ E] s
Area.linear_coarea_formula_surjective_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (L : E →ₗ[ℝ] F)
  (hL : Function.Surjective L) (s : Set E) (hs : MeasurableSet s)
  (g : E → ℝ≥0∞) (hg : Measurable g) :
  ∫⁻ y : F, ∫⁻ x in s ∩ L ⁻¹' {y}, g x ∂μHE[finrank ℝ (LinearMap.ker L)] =
    ENNReal.ofReal (L.domRestrict (LinearMap.ker L)ᗮ).normDet *
      ∫⁻ x in s, g x ∂μHE[finrank ℝ E]
Area.linear_coarea_formula_range {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (L : E →ₗ[ℝ] F) (s : Set E) (hs : MeasurableSet s) :
  ∫⁻ y : LinearMap.range L, μHE[finrank ℝ (LinearMap.ker L)]
      (s ∩ L.rangeRestrict ⁻¹' {y}) =
    ENNReal.ofReal (L.rangeRestrict.domRestrict (LinearMap.ker L)ᗮ).normDet *
      μHE[finrank ℝ E] s
Area.linear_coarea_formula_range_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] (L : E →ₗ[ℝ] F) (s : Set E)
  (hs : MeasurableSet s) (g : E → ℝ≥0∞) (hg : Measurable g) :
  ∫⁻ y : LinearMap.range L, ∫⁻ x in s ∩ L.rangeRestrict ⁻¹' {y}, g x
      ∂μHE[finrank ℝ (LinearMap.ker L)] =
    ENNReal.ofReal (L.rangeRestrict.domRestrict (LinearMap.ker L)ᗮ).normDet *
      ∫⁻ x in s, g x ∂μHE[finrank ℝ E]
Area.linear_coarea_factor_eq_normDet_adjoint {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F)
  (hL : Function.Surjective L) :
  (L.domRestrict (LinearMap.ker L)ᗮ).normDet = L.adjoint.normDet
Area.linear_coarea_factor_sq {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) :
  L.adjoint.normDet ^ 2 = (L ∘ₗ L.adjoint).det
Area.linear_coarea_restricted_factor_sq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) :
  (L.domRestrict (LinearMap.ker L)ᗮ).normDet ^ 2 =
    ((L.domRestrict (LinearMap.ker L)ᗮ).adjoint ∘ₗ
      L.domRestrict (LinearMap.ker L)ᗮ).det
Area.linearCoareaCoordinates {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F) :
  E →ₗ[ℝ] WithLp 2 (F × LinearMap.ker L)
Area.linearCoareaCoordinates_apply {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F) (x : E) :
  Area.linearCoareaCoordinates L x =
    WithLp.toLp 2 (L x, (LinearMap.ker L).orthogonalProjectionOnto x)
Area.linear_coarea_coordinates_normDet {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F)
  (hL : Function.Surjective L) :
  (Area.linearCoareaCoordinates L).normDet = L.adjoint.normDet
Area.dimension_lowering_image_null {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} (hf : ContDiff ℝ 1 f)
  (hEF : finrank ℝ E < finrank ℝ F) : μHE[finrank ℝ F] (Set.range f) = 0
Area.critical_image_null {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} {f' : E → E →L[ℝ] E}
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
  (hcrit : ∀ x ∈ s, (f' x).det = 0) : volume (f '' s) = 0
Area.aemeasurable_coarea_fiber_integral {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ F < finrank ℝ E)
  {s : Set E} (hs : MeasurableSet s) (g : E → ENNReal) (hg : Measurable g) :
  AEMeasurable (fun y =>
    ∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume
Area.coarea_formula_weighted {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ F < finrank ℝ E)
  {s : Set E} (hs : MeasurableSet s) (g : E → ENNReal) (hg : Measurable g) :
  ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.coareaJacobian f x) ∂μHE[finrank ℝ E]
Area.coarea_formula {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] {f : E → F}
  (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ F < finrank ℝ E)
  {s : Set E} (hs : MeasurableSet s) :
  ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
    ∫⁻ x in s, ENNReal.ofReal (Area.coareaJacobian f x) ∂μHE[finrank ℝ E]
ContinuousLinearMap.normDet_le_norm_pow {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →L[ℝ] F) :
  L.toLinearMap.normDet ≤ ‖L‖ ^ finrank ℝ E
MeasureTheory.euclideanUnitBallVolume_add_le_mul (m k : ℕ) :
  MeasureTheory.euclideanUnitBallVolume (m + k) ≤
    MeasureTheory.euclideanUnitBallVolume m * MeasureTheory.euclideanUnitBallVolume k
ContinuousOn.measurable_hausdorffMeasure_fiber {X Y} [MetricSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] {f : X → Y} {s : Set X}
  (hf : ContinuousOn f s) (hs : IsCompact s) {d : ℝ} (hd : 0 < d) :
  Measurable (fun y => μH[d] (s ∩ f ⁻¹' {y}))
LipschitzOnWith.exists_measurable_hausdorffMeasure_fiber_majorant {E F}
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E} {K : NNReal}
  (hf : LipschitzOnWith K f s) {k : ℝ} (hk : 0 < k)
  (hfin : μH[k + finrank ℝ F] s ≠ ∞) :
  ∃ q, Measurable q ∧ (∀ y, μH[k] (s ∩ f ⁻¹' {y}) ≤ q y) ∧
    ∫⁻ y : F, q y ∂μHE[finrank ℝ F] ≤
      (K : ENNReal) ^ finrank ℝ F * volume (Metric.closedBall 0 1) *
        μH[k + finrank ℝ F] s
Area.aemeasurable_lipschitz_coarea_fiber_measure {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) (hEF : finrank ℝ F < finrank ℝ E) {s : Set E}
  (hs : NullMeasurableSet s μHE[finrank ℝ E]) :
  AEMeasurable (fun y => μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y})) volume
Area.lipschitz_coarea_inequality {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) (hEF : finrank ℝ F < finrank ℝ E) {s : Set E}
  (hs : NullMeasurableSet s μHE[finrank ℝ E]) :
  ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) ≤
    (K : ENNReal) ^ finrank ℝ F * μHE[finrank ℝ E] s
Area.lipschitz_coarea_inequality_volume_ratio {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) (hEF : finrank ℝ F < finrank ℝ E) {s : Set E}
  (hs : NullMeasurableSet s μHE[finrank ℝ E]) :
  ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) ≤
    (MeasureTheory.euclideanUnitBallVolume (finrank ℝ F) *
        MeasureTheory.euclideanUnitBallVolume (finrank ℝ E - finrank ℝ F) /
        MeasureTheory.euclideanUnitBallVolume (finrank ℝ E)) *
      (K : ENNReal) ^ finrank ℝ F * μHE[finrank ℝ E] s
IsContDiffSubmanifold {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (n : ℕ) (s : Set E) : Prop
Area.isClosed_critical_set {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {f : E → F} (hf : ContDiff ℝ 1 f) :
  IsClosed {x | ¬ Function.Surjective (fderiv ℝ f x)}
Area.isContDiffSubmanifold_regular_fiber {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F}
  (hf : ContDiff ℝ 1 f) (y : F) :
  IsContDiffSubmanifold (finrank ℝ E - finrank ℝ F)
    ({x | Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})
Area.ae_critical_fiber_measure_eq_zero {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ F < finrank ℝ E) :
  ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F]
    ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y}) = 0
Area.sard_fiber_decomposition {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F}
  (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ F < finrank ℝ E) :
  ∀ᵐ y : F,
    μHE[finrank ℝ E - finrank ℝ F]
        ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y}) = 0 ∧
      IsClosed ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y}) ∧
      (({x | Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y}) = ∅ ∨
        IsContDiffSubmanifold (finrank ℝ E - finrank ℝ F)
          ({x | Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})) ∧
      f ⁻¹' {y} =
        ({x | Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y}) ∪
          ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})
```

## Final gate evidence

The exact reviewed Lean source snapshot is commit `8a22dca`. The final documentation checkpoint does
not change Lean source. A fresh combined build of `GMT.Linear.NormDet`, `GMT.Measure.Density`,
`GMT.Measure.Hausdorff`, `GMT.Measure.Lusin`, `GMT.Analysis.Lipschitz`, `GMT.Analysis.Whitney`,
`GMT.Area.Jacobian`, `GMT.Area.Formula`, `GMT.Area.Submanifold`, `GMT.Area.Coarea`, and `GMT`
completed all 3153 jobs with no errors, warnings, information messages, traces, or tactic suggestions.

Fresh external drivers checked the exact elaborated types recorded above and the transitive axiom
closures of every headline and load-bearing public engine. Every closure is exactly
`[propext, Classical.choice, Quot.sound]`; none contains `sorryAx`. The package-wide declaration gate
`#lint- only unusedArguments simpNF synTaut checkType in GMT` succeeds silently. This pinned Mathlib
revision does not register a linter named `defLemma`: the literal probe reports
`error: not a linter: defLemma`. Accordingly, no `defLemma` success is claimed. Explicit declaration-
kind review confirms that the new proposition-valued declarations are definitions and every theorem
has a proposition-valued result; no declaration-kind mismatch remains.

The public-import consumer probes elaborate the rectangular injective and non-injective area formulas,
weighted and unweighted nonlinear coarea, the Lipschitz fiber-measure estimate, and the Sard
decomposition. Degenerate probes cover the empty set, identity maps, zero and constant maps,
non-injective and rank-deficient maps, null-measurable sets, zero-dimensional spaces, equal dimensions,
and impossible source/target dimensions. The arbitrary linear coarea theorem handles equal,
rank-deficient, zero-codomain, and impossible-dimension cases; the nonlinear coarea and Sard statements
carry the mathematically required strict codimension hypothesis.

Proof-body review finds no packaged conclusion or unconstrained semantic witness. Multiplicity and
fiber measures are defined directly from `f`, `s`, and the fiber value; the coarea Jacobian is the
adjoint rectangular `normDet`; the critical remainder and regular submanifold are explicitly tied to
the derivative of the input map. The weighted formulas are canonical primaries and their unweighted,
injective, image-weighted, Lipschitz, and equal-rank forms follow in the natural direction. Generic
norm-determinant, Hausdorff-fiber, Lusin, Lipschitz, and Whitney dependencies remain in their lower
topic homes; chart and assembly mechanics remain private.

`git diff --check`, the aggregate-wiring check, the complete diff review, and the forbidden-token,
diagnostic, resource-override, comment, and accidental-import scans all pass. No `sorry`, `admit`,
`axiom`, `trustMe`, linter suppression, heartbeat override, diagnostic command, or
`DifferentialGeometry` import occurs in the delivered Lean diff.

## Official workflow verdicts

`prove-theorem-suite`: **Accepted**. The finite Chapter 2 theorem forest is dependency-closed from
the normalized Hausdorff, Lusin/Whitney, and rectangular norm-determinant foundations through the
linear, injective, non-injective, weighted, Lipschitz, and nonlinear area/coarea headlines and the
coarea-derived Sard fiber decomposition.

`audit-lean-theorem-suite`: **Accepted**. Mathematical soundness, API and architecture, proof
integrity, exact signatures, available declaration linters, axiom closures, public consumer probes,
silent builds, aggregate wiring, and source/diff discipline pass on the unchanged reviewed Lean
snapshot. The ambient-global Simon 1.9 boundary and unavailable `defLemma` registration are recorded
explicitly above and are not misreported as stronger evidence.
