# Chapter 2 Area and Coarea Acceptance Matrix

This matrix records the current checked source state against the Chapter 2 contract in
`pasted-text-1.txt` and Simon's *Introduction to Geometric Measure Theory* (2014 revision).

| Headline | Simon reference | Exact declaration | Role | Status |
| --- | --- | --- | --- | --- |
| Lipschitz extension | Chapter 2, Section 1, Theorem 1.2, p. 40 | `Area.lipschitz_extension_real` in `GMT/Area/Jacobian.lean` | scalar extension interface | implemented |
| Rademacher interface | Chapter 2, Section 1, Theorem 1.4, pp. 40-42 | `LipschitzWith.ae_differentiableAt` from Mathlib, consumed by `GMT/Area/Jacobian.lean` | canonical finite-dimensional theorem | reused |
| Rademacher public wrapper | Chapter 2, Section 1, Theorem 1.4, pp. 40-42 | `Area.rademacher` in `GMT/Area/Jacobian.lean` | finite-dimensional real normed-space interface | implemented |
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
| Injective area formula | Chapter 2, Section 3, formula 3.2, pp. 53-54 | `Area.injective_area_formula` in `GMT/Area/Formula.lean` | square-dimensional differentiable interface | implemented with equal domain/codomain |
| Lipschitz injective weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.injective_area_formula_weighted_lipschitz` in `GMT/Area/Formula.lean` | square-dimensional source-weighted fiber-sum identity for globally Lipschitz injective maps, with Rademacher null-set transfer | implemented |
| Lipschitz injective area formula, unweighted | Chapter 2, Section 3, formula 3.2, pp. 53-54 | `Area.injective_area_formula_lipschitz` in `GMT/Area/Formula.lean` | unweighted square-dimensional globally Lipschitz injective corollary | implemented |
| Equal-rank injective area formula | Chapter 2, Section 3, formula 3.2, pp. 53-54 | `Area.injective_area_formula_of_finrank_eq` in `GMT/Area/Formula.lean` | intrinsic transport of the injective formula across different equal-rank Euclidean spaces | implemented |
| Equal-rank general area formula | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.area_formula_of_finrank_eq` in `GMT/Area/Formula.lean` | non-injective source-weighted fiber-sum identity across different equal-rank Euclidean spaces | implemented |
| Equal-rank general area formula, unweighted | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.area_formula_of_finrank_eq_unweighted` in `GMT/Area/Formula.lean` | unweighted equal-rank corollary | implemented |
| Equal-rank injective weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.injective_area_formula_weighted_of_finrank_eq` in `GMT/Area/Formula.lean` | source-weighted fiber-sum identity across equal-rank Euclidean spaces | implemented |
| Weighted injective area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.injective_area_formula_weighted` in `GMT/Area/Formula.lean` | square-dimensional source-weighted fiber-sum interface | implemented with equal domain/codomain |
| General non-injective area formula | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.area_formula` in `GMT/Area/Formula.lean` | canonical measurable source-weighted fiber-sum identity | implemented for square-dimensional C¹ maps |
| General non-injective area formula, unweighted | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.area_formula_unweighted` in `GMT/Area/Formula.lean` | unweighted corollary of the canonical weighted identity | implemented for square-dimensional C¹ maps |
| General weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.area_formula` in `GMT/Area/Formula.lean` | nonnegative measurable weight on the source, summed over each fiber | implemented for square-dimensional C¹ maps |
| Fiber multiplicity | Chapter 2, Section 3, formula 3.4, p. 54 | `Area.multiplicity` in `GMT/Area/Formula.lean` | consumer-visible fiber object | implemented |
| Weighted fiber multiplicity | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.weightedMultiplicity` in `GMT/Area/Formula.lean` | consumer-visible source-weighted fiber sum | implemented |
| General image-weighted area formula | Chapter 2, Section 3, formula 3.5, p. 54 | `Area.area_formula_image_weighted` in `GMT/Area/Formula.lean` | target-weight specialization with multiplicity | implemented for square-dimensional C¹ maps |
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
| Dimension-lowering C¹ image-null corollary | Chapter 2, Section 6, formula 6.4, pp. 66-67 | `Area.dimension_lowering_image_null` in `GMT/Area/Coarea.lean` | full image nullity when domain dimension is smaller than codomain | implemented via Hausdorff-dimension bound; not the coarea-derived Sard proof |
| Finite-partition image-weighted area engine | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.area_formula_of_finite_injective_partition_image_weighted` in `GMT/Area/Formula.lean` | reusable finite injective-partition engine for target weights | implemented |
| Countable-partition area engine | Chapter 2, Section 3, formulas 3.4-3.5, p. 54 | `Area.area_formula_of_countable_injective_partition` in `GMT/Area/Formula.lean` | reusable countable injective-partition engine for source-weighted fiber sums | implemented |
| General coarea formula | Chapter 2, Section 6, formula 6.3, p. 66 | no declaration | nonlinear fiber integral | not implemented |
| C1 Sard-type consequence | Chapter 2, Section 6, formula 6.4, pp. 66-67 | `Area.critical_image_null` in `GMT/Area/Coarea.lean` | square-dimensional critical-image null result | partial only; not Simon's m < n fiber conclusion |

The following load-bearing public dependencies are also part of the delivered surface. They are
supporting API rather than additional Simon headlines: `Area.jacobian_nonneg`,
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
`Area.linear_coarea_factor_sq`, and `Area.linear_coarea_restricted_factor_sq`.
Their exact checked types are recorded below with the
headline signatures; all are in the same three Area modules and are consumed by the area/coarea
proof forest.

The current source therefore does not satisfy the full suite contract. The Lipschitz
dimension-lowering image-null estimate is now available as a reusable Hausdorff-measure leaf. In particular, the
general coarea formula, the C¹ approximation theorem
(Simon 1.5), the Hausdorff-fiber estimate (Simon 1.9), and the m < n Sard-type fiber decomposition
remain open.

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
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {f : E → F} {K : NNReal}
  (hf : LipschitzWith K f) (hEF : finrank ℝ E < finrank ℝ F) :
  μHE[finrank ℝ F] (Set.range f) = 0
Area.rademacher {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] {f : E → F} {K : NNReal} (hf : LipschitzWith K f) :
  ∀ᵐ x ∂(Measure.addHaar : Measure E), DifferentiableAt ℝ f x
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
Area.injective_area_formula {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hf : Set.InjOn f s) :
  μHE[finrank ℝ E] (f '' s) = ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x)
Area.injective_area_formula_weighted_lipschitz {E} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} {K : NNReal} (g : E → ENNReal) (hs : MeasurableSet s)
  (hf : LipschitzWith K f) (hfinj : Set.InjOn f s) (hg : Measurable g) :
  ∫⁻ y, Area.weightedMultiplicity f s g y =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x)
Area.injective_area_formula_image_weighted_lipschitz {E} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} {K : NNReal} (g : E → ENNReal) (hs : MeasurableSet s)
  (hf : LipschitzWith K f) (hfinj : Set.InjOn f s) :
  ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
Area.injective_area_formula_lipschitz {E} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} {K : NNReal} (hs : MeasurableSet s)
  (hf : LipschitzWith K f) (hfinj : Set.InjOn f s) :
  μHE[finrank ℝ E] (f '' s) = ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x)
Area.injective_area_formula_of_finrank_eq {E F} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
  (hfinrank : finrank ℝ E = finrank ℝ F) (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hf : Set.InjOn f s) :
  μHE[finrank ℝ E] (f '' s) =
    ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
Area.injective_area_formula_weighted {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (g : E → ENNReal)
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
  (hfinj : Set.InjOn f s) (hg : Measurable g) :
  ∫⁻ y, Area.weightedMultiplicity f s g y =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x)
Area.injective_area_formula_image_weighted {E} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (g : E → ENNReal)
  (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
  (hfinj : Set.InjOn f s) :
  ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
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
Area.area_formula_of_finite_injective_partition_image_weighted {E} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (n : ℕ) (t : Fin n → Set E)
  (g : E → ENNReal) (hpart : ⋃ i, t i = s) (ht : ∀ i, MeasurableSet (t i))
  (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (t i) (t j))
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i, InjOn f (t i))
  (hg : Measurable g) :
  ∫⁻ y, Area.multiplicity f s y * g y =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
Area.area_formula {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} (g : E → ENNReal) (hs : MeasurableSet s)
  (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
  ∫⁻ y, Area.weightedMultiplicity f s g y =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x)
Area.area_formula_image_weighted {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} (g : E → ENNReal) (hs : MeasurableSet s)
  (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
  ∫⁻ y, Area.multiplicity f s y * g y =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
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
Area.area_formula_of_countable_injective_partition {E} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (t : ℕ → Set E) (g : E → ENNReal)
  (hpart : ⋃ i, t i = s) (ht : ∀ i, MeasurableSet (t i))
  (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (t i) (t j))
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i, InjOn f (t i))
  (hg : Measurable g) :
  ∫⁻ y, Area.weightedMultiplicity f s g y =
    ∫⁻ x in s, g x * ENNReal.ofReal (Area.jacobian f x)
Area.area_formula_of_countable_injective_partition_image_weighted {E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {f : E → E} {f' : E → E →L[ℝ] E}
  {s : Set E} (t : ℕ → Set E) (g : E → ENNReal) (hpart : ⋃ i, t i = s)
  (ht : ∀ i, MeasurableSet (t i))
  (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (t i) (t j))
  (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i, InjOn f (t i))
  (hg : Measurable g) :
  ∫⁻ y, Area.multiplicity f s y * g y =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x) * g (f x)
Area.area_formula_unweighted {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) :
  ∫⁻ y, Area.multiplicity f s y =
    ∫⁻ x in s, ENNReal.ofReal (Area.jacobian f x)
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
Area.dimension_lowering_image_null {E F} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} (hf : ContDiff ℝ 1 f)
  (hEF : finrank ℝ E < finrank ℝ F) : μHE[finrank ℝ F] (Set.range f) = 0
Area.critical_image_null {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : E → E} {s : Set E} {f' : E → E →L[ℝ] E}
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
  (hcrit : ∀ x ∈ s, (f' x).det = 0) : volume (f '' s) = 0
```

Fresh evidence for this snapshot: `lake build GMT.Area.Formula GMT.Area.Coarea GMT` succeeds; an
external declaration driver checks the source-weighted multiplicity, injective, Lipschitz,
countable-partition, square, equal-rank, unweighted, and explicitly image-weighted declarations. The available
`unusedArguments`, `simpNF`, and `synTaut` linters pass for every repaired declaration, and every
checked axiom closure is exactly `[propext, Classical.choice, Quot.sound]`.
The intrinsic coarea-Jacobian API and the shared adjoint `normDet` theorem pass the same declaration
linters and have the same axiom closure.
External identity and subsingleton-codomain edge probes for the surjective theorem also elaborate
successfully. The requested
`defLemma` linter is not registered by this Mathlib revision, so it cannot be run or reported as a
passing check without changing the environment. The finite-partition image-weighted engine was separately
checked with `#check`, the available declaration linters, its axiom closure, the aggregate build,
and an external consumer probe in `/tmp/consumer.lean`; the final general and unweighted headlines
were checked in the same probe and axiom driver.

## Official workflow verdicts

`prove-theorem-suite`: **Not accepted**. The finite headline suite is incomplete: the
square- and equal-rank general non-injective source-weighted area formulas, the equal-rank injective
source-weighted theorem, and the unweighted, weighted, and
rank-deficient linear coarea formulas are present, and Simon's 1.8 fiber-cardinality estimate is now
implemented, but the genuine higher-codimension area formula, general coarea branch, Simon's 1.5
approximation theorem, 1.9 Hausdorff-fiber estimate, and the m < n Sard decomposition remain open.

`audit-lean-theorem-suite`: **Not accepted**. The checked source snapshot has clean available
compiler, linter, and axiom checks for the repaired source-weighted area layer, but it fails the
mathematical completeness gate for the same unresolved headlines despite the new Hausdorff-fiber,
equal-rank, and dimension-lowering image-null layers.
The `defLemma` linter named by the contract is unavailable in this Mathlib revision; the available
declaration linters pass.
