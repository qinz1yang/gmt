import GMT.Analysis.IntegrationByParts
import GMT.Varifold.Monotonicity

open Filter Function Metric Set Topology TopologicalSpace
open scoped Distributions ENNReal MeasureTheory NNReal Topology

noncomputable section

namespace Grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem radialTilt_eq_zero_of_mem (S : Grassmannian E n)
    {center x : E} (hcenter : center ∈ S.subspace) (hx : x ∈ S.subspace) :
    S.radialTilt center x = 0 := by
  have hmem : x - center ∈ S.subspace := sub_mem hx hcenter
  have hprojection : S.projection (x - center) = x - center := by
    rw [S.projection_eq_starProjection]
    exact S.subspace.starProjection_eq_self_iff.mpr hmem
  rw [radialTilt, perpendicularProjection]
  simp [hprojection]

end Grassmannian

namespace Varifold

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

private theorem isometry_planeMap (S : Grassmannian E n) :
    Isometry fun y : S.subspace => ((y : E), S) := by
  apply Isometry.of_dist_eq
  intro x y
  simp [Prod.dist_eq, Subtype.dist_eq]

private theorem isometry_subspace_val (S : Grassmannian E n) :
    Isometry fun y : S.subspace => (y : E) := by
  apply Isometry.of_dist_eq
  intro x y
  exact (Subtype.dist_eq x y).symm

variable [MeasurableSpace E] [BorelSpace E]

-- Simon, Chapter 8, Section 1, p. 206: the multiplicity-one flat-plane specialization.
def ofPlane (S : Grassmannian E n) : Varifold E n where
  toMeasure := μHE[n].map fun y : S.subspace => ((y : E), S)
  isFiniteMeasureOnCompacts := by
    let _ : (μHE[n] : Measure S.subspace).IsAddHaarMeasure := by
      simpa only [S.finrank_subspace] using
        (inferInstance :
          (μHE[Module.finrank ℝ S.subspace] : Measure S.subspace).IsAddHaarMeasure)
    constructor
    intro K hK
    rw [Measure.map_apply (isometry_planeMap S).continuous.measurable hK.measurableSet]
    exact (isometry_planeMap S).isClosedEmbedding.isCompact_preimage hK |>.measure_lt_top

@[simp]
theorem toMeasure_ofPlane (S : Grassmannian E n) :
    (ofPlane S).toMeasure = μHE[n].map fun y : S.subspace => ((y : E), S) := rfl

theorem radialTilt_ae_eq_zero_ofPlane (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace) :
    (fun z : E × Grassmannian E n => z.2.radialTilt center z.1) =ᵐ[(ofPlane S).toMeasure]
      0 := by
  rw [toMeasure_ofPlane]
  have hp : MeasurableSet {z : E × Grassmannian E n |
      z.2.radialTilt center z.1 = 0} :=
    Grassmannian.measurable_radialTilt center (measurableSet_singleton 0)
  apply (ae_map_iff (by fun_prop) hp).2
  filter_upwards [] with y
  exact S.radialTilt_eq_zero_of_mem hcenter y.property

theorem setLIntegral_radialTilt_ofPlane (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace)
    (s : Set (E × Grassmannian E n)) :
    ∫⁻ z in s, z.2.radialTilt center z.1 ∂(ofPlane S).toMeasure = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  exact ae_restrict_of_ae (radialTilt_ae_eq_zero_ofPlane S hcenter)

@[simp]
theorem weightMeasure_ofPlane (S : Grassmannian E n) :
    (ofPlane S).weightMeasure = μHE[n].restrict S.subspace := by
  change (μHE[n].map (fun y : S.subspace => ((y : E), S))).fst = _
  rw [Measure.fst_map_prodMk measurable_const]
  calc
    μHE[n].map Subtype.val =
        μHE[n].restrict (Set.range fun y : S.subspace => (y : E)) :=
      (isometry_subspace_val S).map_euclideanHausdorffMeasure
    _ = μHE[n].restrict S.subspace := by
      congr 1
      ext x
      simp

theorem weightMeasure_ofPlane_closedBall (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace) {r : ℝ} (hr : 0 < r) :
    (ofPlane S).weightMeasure (closedBall center r) =
      (ENNReal.ofReal r) ^ n * euclideanUnitBallVolume n := by
  rw [weightMeasure_ofPlane, Measure.restrict_apply measurableSet_closedBall]
  let c : S.subspace := ⟨center, hcenter⟩
  have himage : (Subtype.val : S.subspace → E) '' closedBall c r =
      closedBall center r ∩ (S.subspace : Set E) := by
    ext y
    simp [c, mem_closedBall]
  rw [← himage]
  calc
    (μHE[n] : Measure E) ((Subtype.val : S.subspace → E) '' closedBall c r) =
        (μHE[n] : Measure S.subspace) (closedBall c r) :=
      (isometry_subspace_val S).euclideanHausdorffMeasure_image _
    _ = (ENNReal.ofReal r) ^ n * euclideanUnitBallVolume n :=
      by simpa only [S.finrank_subspace] using euclideanHausdorffMeasure_closedBall c hr

theorem massRatio_ofPlane (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace) {r : ℝ} (hr : 0 < r) :
    (ofPlane S).weightMeasure.massRatio n center r = euclideanUnitBallVolume n := by
  rw [Measure.massRatio, weightMeasure_ofPlane_closedBall S hcenter hr]
  have hne : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top,
    one_pow, one_mul]

theorem densityRatio_ofPlane (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace) {r : ℝ} (hr : 0 < r) :
    (ofPlane S).weightMeasure.densityRatio n center r = 1 := by
  rw [Measure.densityRatio, massRatio_ofPlane S hcenter hr,
    ENNReal.div_self (euclideanUnitBallVolume_ne_zero n)
      (euclideanUnitBallVolume_ne_top n)]

@[simp]
theorem isStationaryOn_ofPlane (S : Grassmannian E n) (U : Opens E) :
    (ofPlane S).IsStationaryOn U := by
  let _ : (μHE[n] : Measure S.subspace).IsAddHaarMeasure := by
    simpa only [S.finrank_subspace] using
      (inferInstance :
        (μHE[Module.finrank ℝ S.subspace] : Measure S.subspace).IsAddHaarMeasure)
  rw [IsStationaryOn]
  ext X
  rw [zero_apply, firstVariation_apply]
  change (∫ z : E × Grassmannian E n,
    z.2.tangentialDivergence X z.1 ∂μHE[n].map
      (fun y : S.subspace => ((y : E), S))) = 0
  rw [(isometry_planeMap S).isClosedEmbedding.integral_map]
  let b := stdOrthonormalBasis ℝ S.subspace
  let F : S.subspace → E := (X : E → E) ∘ Subtype.val
  have hFcontDiff : ContDiff ℝ 1 F := by
    exact X.contDiff.comp S.subspace.subtypeL.contDiff
  have hFcompact : HasCompactSupport F := by
    exact X.hasCompactSupport.comp_isClosedEmbedding
      (isometry_subspace_val S).isClosedEmbedding
  have hcomponent (i : Fin (Module.finrank ℝ S.subspace)) :
      Integrable (fun y : S.subspace => inner ℝ ((b i : S.subspace) : E)
        (fderiv ℝ (X : E → E) (y : E) (b i : E))) μHE[n] ∧
      (∫ y : S.subspace, inner ℝ ((b i : S.subspace) : E)
        (fderiv ℝ (X : E → E) (y : E) (b i : E)) ∂μHE[n]) = 0 := by
    let g : S.subspace → ℝ := (innerSL ℝ ((b i : S.subspace) : E)) ∘ F
    have hgcontDiff : ContDiff ℝ 1 g := by
      exact (innerSL ℝ ((b i : S.subspace) : E)).contDiff.comp hFcontDiff
    have hgcompact : HasCompactSupport g := by
      exact hFcompact.comp_left (map_zero (innerSL ℝ ((b i : S.subspace) : E)))
    have hgderiv (y : S.subspace) :
        fderiv ℝ g y (b i) = inner ℝ ((b i : S.subspace) : E)
          (fderiv ℝ (X : E → E) (y : E) (b i : E)) := by
      have hX := (X.contDiff.differentiable one_ne_zero (y : E)).hasFDerivAt
      have hF := hX.comp y S.subspace.subtypeL.hasFDerivAt
      have hg := (innerSL ℝ ((b i : S.subspace) : E)).hasFDerivAt.comp y hF
      have h := congrArg (fun A : S.subspace →L[ℝ] ℝ => A (b i)) hg.fderiv
      simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL,
        innerSL_apply_apply] at h
      exact h.trans (by rfl)
    have hint : Integrable (fun y => fderiv ℝ g y (b i)) μHE[n] :=
      ((hgcontDiff.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
          (hgcompact.fderiv_apply ℝ (b i))
    refine ⟨hint.congr (Eventually.of_forall hgderiv), ?_⟩
    calc
      (∫ y : S.subspace, inner ℝ ((b i : S.subspace) : E)
          (fderiv ℝ (X : E → E) (y : E) (b i : E)) ∂μHE[n]) =
          ∫ y : S.subspace, fderiv ℝ g y (b i) ∂μHE[n] := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => (hgderiv y).symm
      _ = 0 := integral_fderiv_eq_zero hgcontDiff hgcompact (b i)
  change (∫ y : S.subspace,
    S.tangentialTrace (fderiv ℝ (X : E → E) (y : E)) ∂μHE[n]) = 0
  simp_rw [S.tangentialTrace_eq_sum_inner b]
  calc
    (∫ y : S.subspace,
        ∑ i, inner ℝ ((b i : S.subspace) : E)
          (fderiv ℝ (X : E → E) (y : E) (b i : E)) ∂μHE[n]) =
        ∑ i, ∫ y : S.subspace, inner ℝ ((b i : S.subspace) : E)
          (fderiv ℝ (X : E → E) (y : E) (b i : E)) ∂μHE[n] := by
      exact integral_finsetSum Finset.univ fun i _ => (hcomponent i).1
    _ = 0 := Finset.sum_eq_zero fun i _ => (hcomponent i).2

theorem lowerDensity_ofPlane (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace) :
    (ofPlane S).weightMeasure.lowerDensity n center = 1 := by
  have hstationary := isStationaryOn_ofPlane S (⊤ : Opens E)
  have htend := hstationary.tendsto_densityRatio (center := center) (R := 1)
    zero_lt_one (by simp)
  have hone : Tendsto ((ofPlane S).weightMeasure.densityRatio n center)
      (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (densityRatio_ofPlane S hcenter hr).symm
  exact tendsto_nhds_unique htend hone

theorem upperDensity_ofPlane (S : Grassmannian E n)
    {center : E} (hcenter : center ∈ S.subspace) :
    (ofPlane S).weightMeasure.upperDensity n center = 1 := by
  rw [← lowerDensity_ofPlane S hcenter]
  exact ((isStationaryOn_ofPlane S (⊤ : Opens E)).lowerDensity_eq_upperDensity
    (center := center) (R := 1) zero_lt_one (by simp)).symm

theorem ofPlane_ne_zero (S : Grassmannian E n) : ofPlane S ≠ 0 := by
  intro hzero
  have hmass := weightMeasure_ofPlane_closedBall S
    (show (0 : E) ∈ S.subspace by simp) (r := 1) zero_lt_one
  rw [hzero, weightMeasure_zero] at hmass
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at hmass
  exact euclideanUnitBallVolume_ne_zero n hmass.symm

end Varifold
