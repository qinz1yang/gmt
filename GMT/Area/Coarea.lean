import GMT.Area.Formula
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal MeasureTheory NNReal

namespace Area

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

theorem linear_coarea_formula_prod (s : Set (E × F)) (hs : MeasurableSet s) :
    ∫⁻ y : E, volume (Prod.mk y ⁻¹' s) = (volume.prod volume) s := by
  exact (Measure.prod_apply hs).symm

theorem linear_coarea_formula_prod_hmeasure (s : Set (E × F)) (hs : MeasurableSet s) :
    ∫⁻ y : E, μHE[Module.finrank ℝ F] (Prod.mk y ⁻¹' s) = (volume.prod volume) s := by
  rw [show (μHE[Module.finrank ℝ F] : Measure F) = volume from
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact linear_coarea_formula_prod s hs

theorem linear_coarea_formula_prod_weighted (s : Set (E × F)) (hs : MeasurableSet s)
    {g : E × F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y : E, ∫⁻ z in (Prod.mk y ⁻¹' s), g (y, z) =
      ∫⁻ p in s, g p := by
  classical
  have hgm : AEMeasurable (s.indicator g) (volume.prod volume) :=
    (hg.indicator hs).aemeasurable
  have hp := MeasureTheory.lintegral_prod (μ := (volume : Measure E))
    (ν := (volume : Measure F)) (s.indicator g) hgm
  calc
    ∫⁻ y : E, ∫⁻ z in (Prod.mk y ⁻¹' s), g (y, z) =
        ∫⁻ y : E, ∫⁻ z, s.indicator g (y, z) := by
      apply lintegral_congr
      intro y
      rw [← MeasureTheory.lintegral_indicator (hs.preimage measurable_prodMk_left)
        (fun z : F => g (y, z))]
      apply lintegral_congr
      intro z
      change (if (y, z) ∈ s then g (y, z) else 0) = _
      rfl
    _ = ∫⁻ p : E × F, s.indicator g p := hp.symm
    _ = ∫⁻ p in s, g p := MeasureTheory.lintegral_indicator hs g

theorem linear_coarea_formula_prod_hmeasure_weighted (s : Set (E × F)) (hs : MeasurableSet s)
    {g : E × F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y : E, ∫⁻ z in (Prod.mk y ⁻¹' s), g (y, z)
        ∂μHE[Module.finrank ℝ F] = ∫⁻ p in s, g p := by
  rw [show (μHE[Module.finrank ℝ F] : Measure F) = volume from
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact linear_coarea_formula_prod_weighted s hs hg

theorem linear_coarea_formula_orthogonal
    (V : Submodule ℝ E) (s : Set E) (hs : MeasurableSet s) :
    μHE[Module.finrank ℝ E] s =
      ∫⁻ x : AffineSubspace.mk' (0 : E) V,
        μHE[Module.finrank ℝ Vᗮ] (s ∩ AffineSubspace.mk' x.val Vᗮ)
          ∂μHE[Module.finrank ℝ V] := by
  let A := AffineSubspace.mk' (0 : E) V
  have hdir : A.direction = V := AffineSubspace.direction_mk' (0 : E) V
  have H := AffineSubspace.euclideanHausdorffMeasure_eq_lintegral A hs
  rw [hdir] at H
  exact H

private lemma map_volume_linear_equiv
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    (R : U →ₗ[ℝ] V) (hR : Function.Bijective R) :
    Measure.map R (volume : Measure U) =
      (ENNReal.ofReal R.normDet)⁻¹ • (volume : Measure V) := by
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply R.continuous_of_finiteDimensional.measurable ht]
  have himage : R '' (R ⁻¹' t) = t := by
    exact Set.image_preimage_eq t hR.2
  have hscale := R.euclideanHausdorffMeasure_image (R ⁻¹' t)
  rw [himage] at hscale
  have hdim : Module.finrank ℝ U = Module.finrank ℝ V := by
    let e : U ≃ₗ[ℝ] V := LinearEquiv.ofBijective R hR
    exact e.finrank_eq
  have htarget : μHE[Module.finrank ℝ U] (t : Set V) = volume t := by
    rw [show Module.finrank ℝ U = Module.finrank ℝ V from hdim]
    exact congrArg (fun m : Measure V => m t)
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := V))
  rw [htarget, InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at hscale
  have hdetpos : 0 < R.normDet := by
    have hker : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr hR.1
    have hdet : R.normDet ≠ 0 := by
      intro hzero
      exact (R.normDet_eq_zero_iff_ker_ne_bot.mp hzero) hker
    exact lt_of_le_of_ne R.normDet_nonneg (Ne.symm hdet)
  have hc0 : ENNReal.ofReal R.normDet ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hdetpos).ne'
  have hc_top : ENNReal.ofReal R.normDet ≠ ∞ := ENNReal.ofReal_ne_top
  change volume (R ⁻¹' t) = (ENNReal.ofReal R.normDet)⁻¹ * volume t
  rw [← ENNReal.div_eq_inv_mul]
  rw [ENNReal.eq_div_iff hc0 hc_top]
  simpa [div_eq_mul_inv, mul_comm] using hscale.symm

private lemma orthogonal_restrict_bijective
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : U →ₗ[ℝ] V) (hL : Function.Surjective L) :
    Function.Bijective (L.domRestrict (LinearMap.ker L)ᗮ) := by
  let K : Submodule ℝ U := LinearMap.ker L
  have hinj : Function.Injective (L.domRestrict Kᗮ) := by
    apply LinearMap.injective_domRestrict_iff.2
    simpa [K] using K.orthogonal_disjoint.symm
  have hsurj : Function.Surjective (L.domRestrict Kᗮ) := by
    apply LinearMap.surjective_domRestrict_iff hL |>.2
    exact K.isCompl_orthogonal.symm.codisjoint
  exact ⟨hinj, hsurj⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
theorem linear_coarea_factor_eq_normDet_adjoint
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) :
    (L.domRestrict (LinearMap.ker L)ᗮ).normDet = L.adjoint.normDet := by
  let K : Submodule ℝ E := LinearMap.ker L
  let R : Kᗮ →ₗ[ℝ] F := L.domRestrict Kᗮ
  have hR : Function.Bijective R := orthogonal_restrict_bijective L hL
  have hfactor : L.adjoint = Kᗮ.subtype ∘ₗ R.adjoint := by
    ext y
    have hmem : L.adjoint y ∈ Kᗮ := by
      change L.adjoint y ∈ L.kerᗮ
      rw [LinearMap.orthogonal_ker]
      exact ⟨y, rfl⟩
    have hsub : R.adjoint y = (⟨L.adjoint y, hmem⟩ : Kᗮ) := by
      apply ext_inner_right ℝ
      intro x
      rw [LinearMap.adjoint_inner_left]
      change @inner ℝ F _ y (L (x : E)) =
        @inner ℝ E _ (L.adjoint y) (x : E)
      exact (LinearMap.adjoint_inner_left L (x : E) y).symm
    change L.adjoint y = (R.adjoint y : E)
    exact (congrArg Subtype.val hsub).symm
  have hi : (Kᗮ.subtype.domRestrict R.adjoint.range).normDet = 1 := by
    let i : R.adjoint.range →ₗᵢ[ℝ] E :=
      Kᗮ.subtypeₗᵢ.comp R.adjoint.range.subtypeₗᵢ
    exact i.normDet_eq_one
  have hdim : Module.finrank ℝ Kᗮ = Module.finrank ℝ F := by
    let e : Kᗮ ≃ₗ[ℝ] F := LinearEquiv.ofBijective R hR
    exact e.finrank_eq
  rw [hfactor, LinearMap.normDet_comp, hi, one_mul,
    LinearMap.normDet_adjoint_of_finrank_eq R hdim]

private theorem normDet_withLp_prodMap
    {U U' V V' : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup U'] [InnerProductSpace ℝ U'] [FiniteDimensional ℝ U']
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
    (A : U →ₗ[ℝ] U') (B : V →ₗ[ℝ] V')
    (hU : Module.finrank ℝ U = Module.finrank ℝ U')
    (hV : Module.finrank ℝ V = Module.finrank ℝ V') :
    ((A.prodMap B).withLpMap 2).normDet = A.normDet * B.normDet := by
  let bU := stdOrthonormalBasis ℝ U
  let bU' := (stdOrthonormalBasis ℝ U').reindex (Fin.castOrderIso hU.symm).toEquiv
  let bV := stdOrthonormalBasis ℝ V
  let bV' := (stdOrthonormalBasis ℝ V').reindex (Fin.castOrderIso hV.symm).toEquiv
  rw [LinearMap.normDet_eq_norm_det_toMatrix ((A.prodMap B).withLpMap 2)
    (bU.prod bV) (bU'.prod bV')]
  rw [LinearMap.normDet_eq_norm_det_toMatrix A bU bU',
    LinearMap.normDet_eq_norm_det_toMatrix B bV bV']
  simp only [← norm_mul]
  congr 1
  have hmatrix :
      LinearMap.toMatrix (bU.prod bV).toBasis (bU'.prod bV').toBasis
          ((A.prodMap B).withLpMap 2) =
        LinearMap.toMatrix (bU.toBasis.prod bV.toBasis)
          (bU'.toBasis.prod bV'.toBasis) (A.prodMap B) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply', OrthonormalBasis.prod, Module.Basis.prod_repr_inl,
        Module.Basis.prod_repr_inr]
  rw [hmatrix]
  have hblocks :
      LinearMap.toMatrix (bU.toBasis.prod bV.toBasis)
          (bU'.toBasis.prod bV'.toBasis) (A.prodMap B) =
        Matrix.fromBlocks (LinearMap.toMatrix bU.toBasis bU'.toBasis A) 0 0
          (LinearMap.toMatrix bV.toBasis bV'.toBasis B) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply']
  rw [hblocks, Matrix.det_fromBlocks_zero₂₁]

def linearCoareaCoordinates (L : E →ₗ[ℝ] F) :
    E →ₗ[ℝ] WithLp 2 (F × LinearMap.ker L) :=
  (WithLp.linearEquiv 2 ℝ (F × LinearMap.ker L)).symm.toLinearMap ∘ₗ
    L.prod (LinearMap.ker L).orthogonalProjectionOnto.toLinearMap

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] in
@[simp] theorem linearCoareaCoordinates_apply (L : E →ₗ[ℝ] F) (x : E) :
    linearCoareaCoordinates L x =
      WithLp.toLp 2 (L x, (LinearMap.ker L).orthogonalProjectionOnto x) :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
theorem linear_coarea_coordinates_normDet
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) :
    (linearCoareaCoordinates L).normDet = L.adjoint.normDet := by
  let K : Submodule ℝ E := LinearMap.ker L
  let R : Kᗮ →ₗ[ℝ] F := L.domRestrict Kᗮ
  let D : E →ₗ[ℝ] WithLp 2 (K × Kᗮ) := K.orthogonalDecomposition.toLinearMap
  let S : WithLp 2 (K × Kᗮ) →ₗ[ℝ] WithLp 2 (Kᗮ × K) :=
    (LinearIsometryEquiv.withLpProdComm 2 ℝ K Kᗮ).toLinearMap
  let P : WithLp 2 (Kᗮ × K) →ₗ[ℝ] WithLp 2 (F × K) :=
    ((R.prodMap (LinearMap.id (R := ℝ) (M := K))).withLpMap 2)
  have hfactor : linearCoareaCoordinates L = (P ∘ₗ S) ∘ₗ D := by
    ext x
    dsimp [linearCoareaCoordinates, P, S, D, R, K]
    rw [Submodule.orthogonalDecomposition_apply]
    change WithLp.toLp 2 (L x, L.ker.orthogonalProjectionOnto x) =
      WithLp.toLp 2
        (L ((L.kerᗮ.orthogonalProjectionOnto x : L.kerᗮ) : E),
          L.ker.orthogonalProjectionOnto x)
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · rw [Submodule.orthogonalProjectionOnto_orthogonal]
      change L x = L (x - L.ker.starProjection x)
      rw [L.map_sub, LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem L.ker x),
        sub_zero]
    · rfl
  have hdimD : Module.finrank ℝ E = Module.finrank ℝ (WithLp 2 (K × Kᗮ)) :=
    K.orthogonalDecomposition.toLinearEquiv.finrank_eq
  have hdimS : Module.finrank ℝ (WithLp 2 (K × Kᗮ)) =
      Module.finrank ℝ (WithLp 2 (Kᗮ × K)) :=
    (LinearIsometryEquiv.withLpProdComm 2 ℝ K Kᗮ).toLinearEquiv.finrank_eq
  have hR : Function.Bijective R := orthogonal_restrict_bijective L hL
  have hdimR : Module.finrank ℝ Kᗮ = Module.finrank ℝ F :=
    (LinearEquiv.ofBijective R hR).finrank_eq
  rw [hfactor, LinearMap.normDet_comp_of_finrank_eq D (P ∘ₗ S) hdimD,
    LinearMap.normDet_comp_of_finrank_eq S P hdimS]
  rw [show D.normDet = 1 from K.orthogonalDecomposition.toLinearIsometry.normDet_eq_one,
    show S.normDet = 1 from
      (LinearIsometryEquiv.withLpProdComm 2 ℝ K Kᗮ).toLinearIsometry.normDet_eq_one,
    mul_one, mul_one]
  rw [show P.normDet = R.normDet by
    simpa [P] using
      normDet_withLp_prodMap R (LinearMap.id (R := ℝ) (M := K)) hdimR rfl]
  exact linear_coarea_factor_eq_normDet_adjoint L hL

private lemma affine_subspace_to_orthogonal
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup V] [Module ℝ V]
    (L : U →ₗ[ℝ] V) :
    let K : Submodule ℝ U := LinearMap.ker L
    let A : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) Kᗮ
    ∃ e : A ≃ᵢ Kᗮ, ∀ x : A, (e x : U) = x := by
  dsimp
  let K : Submodule ℝ U := LinearMap.ker L
  let A : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) Kᗮ
  let φ : A → Kᗮ := fun x => ⟨x.1, by
    have hx := x.2
    change x.1 - (0 : U) ∈ Kᗮ at hx
    simpa using hx⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : x.1 = y.1 := by simpa [φ] using hxy
    exact Subtype.ext hxy'
  have hφsurj : Function.Surjective φ := by
    intro x
    refine ⟨⟨x.1, ?_⟩, ?_⟩
    · simp [A]
    · rfl
  have hφiso : Isometry φ := by
    intro x y
    rfl
  let e : A ≃ᵢ Kᗮ := IsometryEquiv.mk (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) hφiso
  refine ⟨e, ?_⟩
  intro x
  rfl

private lemma map_affine_orthogonal_restrict
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    (L : U →ₗ[ℝ] V) (hL : Function.Surjective L) :
    let K : Submodule ℝ U := LinearMap.ker L
    let A : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) Kᗮ
    let R : Kᗮ →ₗ[ℝ] V := L.domRestrict Kᗮ
    ∃ ψ : A → V, (∀ x : A, ψ x = L x.val) ∧
      Measure.map ψ (μHE[Module.finrank ℝ Kᗮ] : Measure A) =
        (ENNReal.ofReal R.normDet)⁻¹ • (volume : Measure V) ∧
      MeasurableEmbedding ψ := by
  dsimp
  let K : Submodule ℝ U := LinearMap.ker L
  let A : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) Kᗮ
  let R : Kᗮ →ₗ[ℝ] V := L.domRestrict Kᗮ
  have hR : Function.Bijective R := by
    apply orthogonal_restrict_bijective L hL
  obtain ⟨e, he⟩ := affine_subspace_to_orthogonal L
  let ψ : A → V := fun x => R (e x)
  have hμe := e.measurePreserving_euclideanHausdorffMeasure (Module.finrank ℝ Kᗮ)
  have hμe' : Measure.map e (μHE[Module.finrank ℝ Kᗮ] : Measure A) =
      (μHE[Module.finrank ℝ Kᗮ] : Measure Kᗮ) := hμe.map_eq
  have hμK : (μHE[Module.finrank ℝ Kᗮ] : Measure Kᗮ) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have hμR := map_volume_linear_equiv R hR
  let rE : Kᗮ ≃L[ℝ] V := (LinearEquiv.ofBijective R hR).toContinuousLinearEquiv
  have hψembed : MeasurableEmbedding ψ := by
    have hcomp := rE.toHomeomorph.measurableEmbedding.comp e.toHomeomorph.measurableEmbedding
    change MeasurableEmbedding ((rE : Kᗮ → V) ∘ e)
    exact hcomp
  refine ⟨ψ, ?_, ?_, hψembed⟩
  · intro x
    change L (e x : U) = L x.val
    exact congrArg L (he x)
  · have hcomp := Measure.map_map (μ := (μHE[Module.finrank ℝ Kᗮ] : Measure A))
      (g := (R : Kᗮ → V)) (f := (e : A → Kᗮ))
      R.continuous_of_finiteDimensional.measurable e.toHomeomorph.measurable
    rw [show ψ = (R : Kᗮ → V) ∘ e by rfl, ← hcomp]
    rw [hμe', hμK, hμR]

private lemma orthogonal_fiber_kernel
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace U] [BorelSpace U] (L : U →ₗ[ℝ] V) :
    let K : Submodule ℝ U := LinearMap.ker L
    let A : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) Kᗮ
    ∃ κ : A → Measure U, Measurable κ ∧
      (∀ x : A, κ x =
        (μHE[Module.finrank ℝ K] : Measure U).restrict (AffineSubspace.mk' x.val K)) ∧
      Measure.bind (μHE[Module.finrank ℝ Kᗮ] : Measure A) κ =
        (μHE[Module.finrank ℝ U] : Measure U) := by
  dsimp
  let K : Submodule ℝ U := LinearMap.ker L
  let A : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) Kᗮ
  let q : A × K → U := fun p => p.1.val + p.2.val
  let κ : A → Measure U := fun x =>
    Measure.map q (Measure.map (Prod.mk x) (μHE[Module.finrank ℝ K] : Measure K))
  have hq : Measurable q := by
    fun_prop
  have hκm : Measurable κ := by
    exact (Measure.measurable_map q hq).comp Measurable.map_prodMk_left
  have hκ : ∀ x : A, κ x =
      (μHE[Module.finrank ℝ K] : Measure U).restrict (AffineSubspace.mk' x.val K) := by
    intro x
    change Measure.map q
      (Measure.map (Prod.mk x) (μHE[Module.finrank ℝ K] : Measure K)) = _
    rw [Measure.map_map hq measurable_prodMk_left]
    let e : K → U := fun z => x.val + z.val
    have he : Isometry e := by
      exact (isometry_vadd U x.val).comp isometry_subtype_coe
    have hrange : range e = AffineSubspace.mk' x.val K := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        simp [e, w.2]
      · intro hz
        refine ⟨⟨z - x.val, ?_⟩, ?_⟩
        · exact (AffineSubspace.mem_mk').1 hz
        · simp [e]
    change Measure.map e (μHE[Module.finrank ℝ K] : Measure K) = _
    rw [he.map_euclideanHausdorffMeasure, hrange]
  refine ⟨κ, hκm, hκ, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.bind_apply hs hκm.aemeasurable]
  simp_rw [hκ, Measure.restrict_apply hs]
  have hdecomp := AffineSubspace.euclideanHausdorffMeasure_eq_lintegral A hs
  rw [show A.direction = Kᗮ by simp [A], Submodule.orthogonal_orthogonal K] at hdecomp
  exact hdecomp.symm

private lemma linear_coarea_formula_surjective_aux
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) (s : Set E)
    (hs : MeasurableSet s) :
    ∫⁻ y : F, μHE[Module.finrank ℝ (LinearMap.ker L)]
        (s ∩ L ⁻¹' {y}) =
      ENNReal.ofReal (L.domRestrict (LinearMap.ker L)ᗮ).normDet *
        μHE[Module.finrank ℝ E] s := by
  let K : Submodule ℝ E := LinearMap.ker L
  let A : AffineSubspace ℝ E := AffineSubspace.mk' (0 : E) Kᗮ
  let R : Kᗮ →ₗ[ℝ] F := L.domRestrict Kᗮ
  let hA : Nonempty A := ⟨⟨0, by simp [A]⟩⟩
  have hdecomp := @AffineSubspace.euclideanHausdorffMeasure_eq_lintegral
    E E _ _ _ _ _ _ _ _ _ A hA s hs
  rw [show A.direction = Kᗮ by simp [A]] at hdecomp
  rw [Submodule.orthogonal_orthogonal K] at hdecomp
  have hdecomp' :
      μHE[Module.finrank ℝ E] s =
        ∫⁻ x : A, μHE[Module.finrank ℝ K] (s ∩ AffineSubspace.mk' x.val K)
          ∂μHE[Module.finrank ℝ Kᗮ] := by
    simpa [A, Submodule.orthogonal_orthogonal] using hdecomp
  obtain ⟨ψ, hψ, hψmap, hψembed⟩ := map_affine_orthogonal_restrict L hL
  have hq : ∀ x : A,
      μHE[Module.finrank ℝ K] (s ∩ AffineSubspace.mk' x.val K) =
        μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {ψ x}) := by
    intro x
    congr 1
    ext z
    constructor
    · rintro ⟨hzs, hzK⟩
      refine ⟨hzs, ?_⟩
      have hzKmem : z - x.val ∈ K := (AffineSubspace.mem_mk').1 hzK
      have hzK' : L (z - x.val) = 0 := hzKmem
      have hLzx : L z = L x.val := by
        apply sub_eq_zero.mp
        simpa [L.map_sub] using hzK'
      simpa [hψ x] using hLzx
    · rintro ⟨hzs, hzy⟩
      refine ⟨hzs, ?_⟩
      have hLzx : L z = L x.val := by simpa [hψ x] using hzy
      have hzK' : L (z - x.val) = 0 := by
        rw [L.map_sub, hLzx, sub_self]
      exact hzK'
  have hmap_integral := hψembed.lintegral_map
    (μ := (μHE[Module.finrank ℝ Kᗮ] : Measure A))
    (fun y : F => μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {y}))
  rw [hψmap] at hmap_integral
  rw [lintegral_smul_measure] at hmap_integral
  have hmap' :
      (ENNReal.ofReal R.normDet)⁻¹ *
          (∫⁻ y : F, μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {y})) =
        ∫⁻ x : A, μHE[Module.finrank ℝ K]
          (s ∩ AffineSubspace.mk' x.val K) ∂μHE[Module.finrank ℝ Kᗮ] := by
    calc
      (ENNReal.ofReal R.normDet)⁻¹ *
          (∫⁻ y : F, μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {y})) =
          ∫⁻ x : A, μHE[Module.finrank ℝ K]
            (s ∩ L ⁻¹' {ψ x}) ∂μHE[Module.finrank ℝ Kᗮ] := by
        simpa only [ENNReal.smul_def, smul_eq_mul] using hmap_integral
      _ = ∫⁻ x : A, μHE[Module.finrank ℝ K]
          (s ∩ AffineSubspace.mk' x.val K) ∂μHE[Module.finrank ℝ Kᗮ] := by
        apply lintegral_congr
        intro x
        exact (hq x).symm
  have hmain :
      ∫⁻ y : F, μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {y}) =
        ENNReal.ofReal R.normDet *
          ∫⁻ x : A, μHE[Module.finrank ℝ K] (s ∩ AffineSubspace.mk' x.val K)
          ∂μHE[Module.finrank ℝ Kᗮ] := by
    have hdetpos : 0 < R.normDet := by
      have hker : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr
        (orthogonal_restrict_bijective L hL).1
      have hdet : R.normDet ≠ 0 := by
        intro hzero
        exact (R.normDet_eq_zero_iff_ker_ne_bot.mp hzero) hker
      exact lt_of_le_of_ne R.normDet_nonneg (Ne.symm hdet)
    have hc0 : ENNReal.ofReal R.normDet ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hdetpos).ne'
    have hctop : ENNReal.ofReal R.normDet ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      ∫⁻ y : F, μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {y}) =
          ENNReal.ofReal R.normDet *
            ((ENNReal.ofReal R.normDet)⁻¹ *
              (∫⁻ y : F, μHE[Module.finrank ℝ K] (s ∩ L ⁻¹' {y}))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
      _ = ENNReal.ofReal R.normDet *
          (∫⁻ x : A, μHE[Module.finrank ℝ K]
            (s ∩ AffineSubspace.mk' x.val K) ∂μHE[Module.finrank ℝ Kᗮ]) := by
        rw [hmap']
  rw [hmain, ← hdecomp']

private lemma linear_coarea_formula_surjective_weighted_aux
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) (s : Set E)
    (hs : MeasurableSet s) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y : F, ∫⁻ x in s ∩ L ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ (LinearMap.ker L)] =
      ENNReal.ofReal (L.domRestrict (LinearMap.ker L)ᗮ).normDet *
        ∫⁻ x in s, g x ∂μHE[Module.finrank ℝ E] := by
  let K : Submodule ℝ E := LinearMap.ker L
  let A : AffineSubspace ℝ E := AffineSubspace.mk' (0 : E) Kᗮ
  let R : Kᗮ →ₗ[ℝ] F := L.domRestrict Kᗮ
  obtain ⟨κ, hκm, hκ, hκbind⟩ := orthogonal_fiber_kernel L
  obtain ⟨ψ, hψ, hψmap, hψembed⟩ := map_affine_orthogonal_restrict L hL
  have hindicator : Measurable (s.indicator g) := hg.indicator hs
  have hbind := Measure.lintegral_bind
    (m := (μHE[Module.finrank ℝ Kᗮ] : Measure A)) (μ := κ)
    (f := s.indicator g) hκm.aemeasurable
    (hindicator.aemeasurable : AEMeasurable (s.indicator g)
      (Measure.bind (μHE[Module.finrank ℝ Kᗮ] : Measure A) κ))
  have hinner : ∀ x : A,
      (∫⁻ z, s.indicator g z ∂κ x) =
        ∫⁻ z in s ∩ AffineSubspace.mk' x.val K, g z
          ∂μHE[Module.finrank ℝ K] := by
    intro x
    rw [hκ x]
    simpa [K] using (MeasureTheory.setLIntegral_indicator
      (μ := (μHE[Module.finrank ℝ K] : Measure E))
      (t := (AffineSubspace.mk' x.val K : Set E)) hs g)
  have hparam :
      (∫⁻ x : A, ∫⁻ z in s ∩ AffineSubspace.mk' x.val K, g z
          ∂μHE[Module.finrank ℝ K] ∂μHE[Module.finrank ℝ Kᗮ]) =
        ∫⁻ z in s, g z ∂μHE[Module.finrank ℝ E] := by
    calc
      (∫⁻ x : A, ∫⁻ z in s ∩ AffineSubspace.mk' x.val K, g z
          ∂μHE[Module.finrank ℝ K] ∂μHE[Module.finrank ℝ Kᗮ]) =
          ∫⁻ x : A, ∫⁻ z, s.indicator g z ∂κ x
            ∂μHE[Module.finrank ℝ Kᗮ] := by
        apply lintegral_congr
        intro x
        exact (hinner x).symm
      _ = ∫⁻ z, s.indicator g z
          ∂Measure.bind (μHE[Module.finrank ℝ Kᗮ] : Measure A) κ := hbind.symm
      _ = ∫⁻ z, s.indicator g z ∂μHE[Module.finrank ℝ E] := by rw [hκbind]
      _ = ∫⁻ z in s, g z ∂μHE[Module.finrank ℝ E] :=
        MeasureTheory.lintegral_indicator hs g
  have hfiber : ∀ x : A,
      (∫⁻ z in s ∩ AffineSubspace.mk' x.val K, g z
          ∂μHE[Module.finrank ℝ K]) =
        ∫⁻ z in s ∩ L ⁻¹' {ψ x}, g z
          ∂μHE[Module.finrank ℝ K] := by
    intro x
    congr 2
    ext z
    constructor
    · rintro ⟨hzs, hzK⟩
      refine ⟨hzs, ?_⟩
      have hzKmem : z - x.val ∈ K := (AffineSubspace.mem_mk').1 hzK
      have hzK' : L (z - x.val) = 0 := hzKmem
      have hLzx : L z = L x.val := by
        apply sub_eq_zero.mp
        simpa [L.map_sub] using hzK'
      simpa [hψ x] using hLzx
    · rintro ⟨hzs, hzy⟩
      refine ⟨hzs, ?_⟩
      have hLzx : L z = L x.val := by simpa [hψ x] using hzy
      have hzK' : L (z - x.val) = 0 := by
        rw [L.map_sub, hLzx, sub_self]
      exact hzK'
  have hparam' :
      (∫⁻ x : A, ∫⁻ z in s ∩ L ⁻¹' {ψ x}, g z
          ∂μHE[Module.finrank ℝ K] ∂μHE[Module.finrank ℝ Kᗮ]) =
        ∫⁻ z in s, g z ∂μHE[Module.finrank ℝ E] := by
    rw [← hparam]
    apply lintegral_congr
    intro x
    exact (hfiber x).symm
  have hmap_integral := hψembed.lintegral_map
    (μ := (μHE[Module.finrank ℝ Kᗮ] : Measure A))
    (fun y : F => ∫⁻ z in s ∩ L ⁻¹' {y}, g z
      ∂μHE[Module.finrank ℝ K])
  rw [hψmap] at hmap_integral
  rw [lintegral_smul_measure] at hmap_integral
  have hmain :
      (∫⁻ y : F, ∫⁻ z in s ∩ L ⁻¹' {y}, g z
          ∂μHE[Module.finrank ℝ K]) =
        ENNReal.ofReal R.normDet *
          (∫⁻ x : A, ∫⁻ z in s ∩ L ⁻¹' {ψ x}, g z
            ∂μHE[Module.finrank ℝ K] ∂μHE[Module.finrank ℝ Kᗮ]) := by
    have hdetpos : 0 < R.normDet := by
      have hker : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr
        (orthogonal_restrict_bijective L hL).1
      have hdet : R.normDet ≠ 0 := by
        intro hzero
        exact (R.normDet_eq_zero_iff_ker_ne_bot.mp hzero) hker
      exact lt_of_le_of_ne R.normDet_nonneg (Ne.symm hdet)
    have hc0 : ENNReal.ofReal R.normDet ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hdetpos).ne'
    have hctop : ENNReal.ofReal R.normDet ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      (∫⁻ y : F, ∫⁻ z in s ∩ L ⁻¹' {y}, g z
          ∂μHE[Module.finrank ℝ K]) =
          ENNReal.ofReal R.normDet *
            ((ENNReal.ofReal R.normDet)⁻¹ *
              (∫⁻ y : F, ∫⁻ z in s ∩ L ⁻¹' {y}, g z
                ∂μHE[Module.finrank ℝ K])) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
      _ = ENNReal.ofReal R.normDet *
          (∫⁻ x : A, ∫⁻ z in s ∩ L ⁻¹' {ψ x}, g z
            ∂μHE[Module.finrank ℝ K] ∂μHE[Module.finrank ℝ Kᗮ]) := by
        rw [show (ENNReal.ofReal R.normDet)⁻¹ *
            (∫⁻ y : F, ∫⁻ z in s ∩ L ⁻¹' {y}, g z
              ∂μHE[Module.finrank ℝ K]) =
            ∫⁻ x : A, ∫⁻ z in s ∩ L ⁻¹' {ψ x}, g z
              ∂μHE[Module.finrank ℝ K] ∂μHE[Module.finrank ℝ Kᗮ] by
          simpa only [ENNReal.smul_def, smul_eq_mul] using hmap_integral]
  rw [hmain, hparam']

theorem linear_coarea_formula_weighted
    (L : E →ₗ[ℝ] F) (s : Set E) (hs : MeasurableSet s)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y : F, ∫⁻ x in s ∩ L ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
      ENNReal.ofReal L.adjoint.normDet *
        ∫⁻ x in s, g x ∂μHE[Module.finrank ℝ E] := by
  by_cases hL : Function.Surjective L
  · have hrange : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ F := by
      rw [LinearMap.range_eq_top.mpr hL]
      simp
    have hdim : Module.finrank ℝ E - Module.finrank ℝ F =
        Module.finrank ℝ (LinearMap.ker L) := by
      have hrank := L.finrank_range_add_finrank_ker
      omega
    rw [hdim, ← linear_coarea_factor_eq_normDet_adjoint L hL]
    exact linear_coarea_formula_surjective_weighted_aux L hL s hs g hg
  · have hrange : LinearMap.range L ≠ ⊤ := by
      exact fun h => hL (LinearMap.range_eq_top.mp h)
    have hrangezero : (volume : Measure F) (LinearMap.range L) = 0 :=
      Measure.addHaar_submodule volume (LinearMap.range L) hrange
    have hleft : (∫⁻ y : F, ∫⁻ x in s ∩ L ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) = 0 := by
      rw [← lintegral_zero]
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : F ∂(volume : Measure F), y ∉ LinearMap.range L := by
        apply ae_iff.mpr
        have hset : {y : F | ¬ y ∉ LinearMap.range L} =
            (LinearMap.range L : Set F) := by
          ext y
          simp
        rw [hset]
        exact hrangezero
      filter_upwards [hae] with y hy
      have hempty : L ⁻¹' {y} = ∅ := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        intro hxy
        exact hy ⟨x, hxy⟩
      simp [hempty]
    have hadjker : L.adjoint.ker ≠ ⊥ := by
      rw [← LinearMap.orthogonal_range]
      exact fun h => hrange (Submodule.orthogonal_eq_bot_iff.mp h)
    have hfactor : L.adjoint.normDet = 0 :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hadjker
    rw [hleft, hfactor]
    simp

theorem linear_coarea_formula
    (L : E →ₗ[ℝ] F) (s : Set E) (hs : MeasurableSet s) :
    ∫⁻ y : F, μHE[Module.finrank ℝ E - Module.finrank ℝ F]
        (s ∩ L ⁻¹' {y}) =
      ENNReal.ofReal L.adjoint.normDet * μHE[Module.finrank ℝ E] s := by
  simpa only [MeasureTheory.setLIntegral_one] using
    linear_coarea_formula_weighted L s hs (fun _ => (1 : ℝ≥0∞)) measurable_const

theorem linear_coarea_formula_surjective
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) (s : Set E)
    (hs : MeasurableSet s) :
    ∫⁻ y : F, μHE[Module.finrank ℝ (LinearMap.ker L)]
        (s ∩ L ⁻¹' {y}) =
      ENNReal.ofReal (L.domRestrict (LinearMap.ker L)ᗮ).normDet *
        μHE[Module.finrank ℝ E] s := by
  have hrange : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ F := by
    rw [LinearMap.range_eq_top.mpr hL]
    simp
  have hdim : Module.finrank ℝ E - Module.finrank ℝ F =
      Module.finrank ℝ (LinearMap.ker L) := by
    have hrank := L.finrank_range_add_finrank_ker
    omega
  rw [← hdim, linear_coarea_factor_eq_normDet_adjoint L hL]
  exact linear_coarea_formula L s hs

theorem linear_coarea_formula_surjective_weighted
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) (s : Set E)
    (hs : MeasurableSet s) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y : F, ∫⁻ x in s ∩ L ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ (LinearMap.ker L)] =
      ENNReal.ofReal (L.domRestrict (LinearMap.ker L)ᗮ).normDet *
        ∫⁻ x in s, g x ∂μHE[Module.finrank ℝ E] := by
  have hrange : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ F := by
    rw [LinearMap.range_eq_top.mpr hL]
    simp
  have hdim : Module.finrank ℝ E - Module.finrank ℝ F =
      Module.finrank ℝ (LinearMap.ker L) := by
    have hrank := L.finrank_range_add_finrank_ker
    omega
  rw [← hdim, linear_coarea_factor_eq_normDet_adjoint L hL]
  exact linear_coarea_formula_weighted L s hs g hg

omit [FiniteDimensional ℝ F] in
theorem linear_coarea_formula_range
    (L : E →ₗ[ℝ] F) (s : Set E) (hs : MeasurableSet s) :
    ∫⁻ y : LinearMap.range L,
        μHE[Module.finrank ℝ (LinearMap.ker L)]
          (s ∩ (L.rangeRestrict : E →ₗ[ℝ] LinearMap.range L) ⁻¹' {y}) =
      ENNReal.ofReal
          ((L.rangeRestrict : E →ₗ[ℝ] LinearMap.range L).domRestrict
            (LinearMap.ker L)ᗮ).normDet * μHE[Module.finrank ℝ E] s := by
  let L' : E →ₗ[ℝ] LinearMap.range L := L.rangeRestrict
  have hL' : Function.Surjective L' := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have h := linear_coarea_formula_surjective L' hL' s hs
  rw [LinearMap.ker_rangeRestrict] at h
  exact h

omit [FiniteDimensional ℝ F] in
theorem linear_coarea_formula_range_weighted
    (L : E →ₗ[ℝ] F) (s : Set E) (hs : MeasurableSet s)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y : LinearMap.range L, ∫⁻ x in
        s ∩ (L.rangeRestrict : E →ₗ[ℝ] LinearMap.range L) ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ (LinearMap.ker L)] =
      ENNReal.ofReal
          ((L.rangeRestrict : E →ₗ[ℝ] LinearMap.range L).domRestrict
            (LinearMap.ker L)ᗮ).normDet *
        ∫⁻ x in s, g x ∂μHE[Module.finrank ℝ E] := by
  let L' : E →ₗ[ℝ] LinearMap.range L := L.rangeRestrict
  have hL' : Function.Surjective L' := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have h := linear_coarea_formula_surjective_weighted L' hL' s hs g hg
  rw [LinearMap.ker_rangeRestrict] at h
  exact h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
theorem linear_coarea_restricted_factor_sq
    (L : E →ₗ[ℝ] F) :
    (L.domRestrict (LinearMap.ker L)ᗮ).normDet ^ 2 =
      ((L.domRestrict (LinearMap.ker L)ᗮ).adjoint ∘ₗ
        L.domRestrict (LinearMap.ker L)ᗮ).det := by
  exact LinearMap.normDet_sq _

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
theorem linear_coarea_factor_sq
    (L : E →ₗ[ℝ] F) :
    L.adjoint.normDet ^ 2 = (L ∘ₗ L.adjoint).det := by
  simpa using LinearMap.normDet_sq L.adjoint

private def orthogonalStretch (V : Submodule ℝ F) (c : ℝ) : F →ₗ[ℝ] F :=
  V.orthogonalDecomposition.symm.toLinearMap ∘ₗ
    (((LinearMap.id (R := ℝ) (M := V)).prodMap
      (c • LinearMap.id (R := ℝ) (M := Vᗮ))).withLpMap 2) ∘ₗ
        V.orthogonalDecomposition.toLinearMap

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem orthogonalStretch_apply (V : Submodule ℝ F) (c : ℝ) (x : F) :
    orthogonalStretch V c x =
      (V.orthogonalProjectionOnto x : F) +
        c • (Vᗮ.orthogonalProjectionOnto x : F) := by
  simp [orthogonalStretch, Submodule.orthogonalDecomposition_apply]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem orthogonalStretch_apply_of_mem (V : Submodule ℝ F) (c : ℝ)
    {x : F} (hx : x ∈ V) : orthogonalStretch V c x = x := by
  rw [orthogonalStretch_apply]
  have hV : (V.orthogonalProjectionOnto x : F) = x := by
    simpa using congrArg Subtype.val
      (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩)
  have hVo : (Vᗮ.orthogonalProjectionOnto x : F) = 0 := by
    exact congrArg Subtype.val
      (Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (V.le_orthogonal_orthogonal hx))
  rw [hV, hVo, smul_zero, add_zero]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem orthogonalStretch_norm_le (V : Submodule ℝ F) {c : ℝ}
    (hc : 1 ≤ c) (x : F) : ‖orthogonalStretch V c x‖ ≤ c * ‖x‖ := by
  rw [orthogonalStretch_apply]
  have horth : @inner ℝ F _ (V.orthogonalProjectionOnto x : F)
      (c • (Vᗮ.orthogonalProjectionOnto x : F)) = 0 := by
    rw [inner_smul_right]
    simp only [mul_eq_zero]
    right
    exact (V.mem_orthogonal _).1 (Vᗮ.orthogonalProjectionOnto x).2 _
      (V.orthogonalProjectionOnto x).2
  have hsum : ‖(V.orthogonalProjectionOnto x : F) +
      c • (Vᗮ.orthogonalProjectionOnto x : F)‖ ^ 2 =
        ‖(V.orthogonalProjectionOnto x : F)‖ ^ 2 +
          ‖c • (Vᗮ.orthogonalProjectionOnto x : F)‖ ^ 2 := by
    simpa only [sq] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hxsum : ‖x‖ ^ 2 = ‖(V.orthogonalProjectionOnto x : F)‖ ^ 2 +
      ‖(Vᗮ.orthogonalProjectionOnto x : F)‖ ^ 2 :=
    V.norm_sq_eq_add_norm_sq_projection x
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hc) (norm_nonneg _)),
    hsum, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hc), mul_pow]
  nlinarith [hxsum, sq_nonneg ‖(V.orthogonalProjectionOnto x : F)‖,
    mul_self_le_mul_self (show (0 : ℝ) ≤ 1 by positivity) hc]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem orthogonalStretch_normDet (V : Submodule ℝ F) (c : ℝ) :
    (orthogonalStretch V c).normDet = |c| ^ Module.finrank ℝ Vᗮ := by
  let D : F →ₗ[ℝ] WithLp 2 (V × Vᗮ) := V.orthogonalDecomposition.toLinearMap
  let B : WithLp 2 (V × Vᗮ) →ₗ[ℝ] WithLp 2 (V × Vᗮ) :=
    ((LinearMap.id (R := ℝ) (M := V)).prodMap
      (c • LinearMap.id (R := ℝ) (M := Vᗮ))).withLpMap 2
  have hdim : Module.finrank ℝ F = Module.finrank ℝ (WithLp 2 (V × Vᗮ)) :=
    V.orthogonalDecomposition.toLinearEquiv.finrank_eq
  rw [show orthogonalStretch V c =
      V.orthogonalDecomposition.symm.toLinearMap ∘ₗ (B ∘ₗ D) from rfl,
    LinearMap.normDet_comp_of_finrank_eq (B ∘ₗ D)
      V.orthogonalDecomposition.symm.toLinearMap hdim,
    LinearMap.normDet_comp_of_finrank_eq D B hdim]
  rw [show V.orthogonalDecomposition.symm.toLinearMap.normDet = 1 from
    V.orthogonalDecomposition.symm.toLinearIsometry.normDet_eq_one,
    show D.normDet = 1 from V.orthogonalDecomposition.toLinearIsometry.normDet_eq_one,
    one_mul, mul_one]
  rw [show B.normDet =
      (LinearMap.id (R := ℝ) (M := V)).normDet *
        (c • LinearMap.id (R := ℝ) (M := Vᗮ)).normDet by
    exact normDet_withLp_prodMap _ _ rfl rfl]
  simp [LinearMap.normDet_smul, Real.norm_eq_abs]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem orthogonalStretch_bijective (V : Submodule ℝ F) {c : ℝ} (hc : c ≠ 0) :
    Function.Bijective (orthogonalStretch V c) := by
  have hdet : (orthogonalStretch V c).normDet ≠ 0 := by
    rw [orthogonalStretch_normDet]
    positivity
  have hinj : Function.Injective (orthogonalStretch V c) :=
    LinearMap.normDet_ne_zero_tfae (orthogonalStretch V c) |>.out 0 4 |>.mp hdet
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hinj⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem ApproximatesLinearOn.lipschitzOnWith_orthogonalStretch_comp
    {f : E → F} {A : E →L[ℝ] F} {s : Set E} {δ M : ℝ≥0} {c : ℝ}
    (hf : ApproximatesLinearOn f A s δ) (hc : 1 ≤ c)
    (hcδ : c * δ ≤ 1) (hA : ‖A‖₊ ≤ M) :
    LipschitzOnWith (M + 1) (orthogonalStretch (LinearMap.range A.toLinearMap) c ∘ f) s := by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_dist_le'
    (K := ((M + 1 : ℝ≥0) : ℝ)) (fun x hx y hy => by
      simp only [dist_eq_norm]
      let e : F := f x - f y - A (x - y)
      have hdecomp : f x - f y = A (x - y) + e := by
        dsimp only [e]
        abel
      have he : ‖e‖ ≤ (δ : ℝ) * ‖x - y‖ := hf x hx y hy
      have hfix : orthogonalStretch (LinearMap.range A.toLinearMap) c (A (x - y)) =
          A (x - y) := by
        apply orthogonalStretch_apply_of_mem
        exact ⟨x - y, rfl⟩
      have herr : ‖orthogonalStretch (LinearMap.range A.toLinearMap) c e‖ ≤
          ‖x - y‖ := by
        calc
          ‖orthogonalStretch (LinearMap.range A.toLinearMap) c e‖ ≤ c * ‖e‖ :=
            orthogonalStretch_norm_le _ hc e
          _ ≤ c * ((δ : ℝ) * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left he (zero_le_one.trans hc)
          _ = (c * (δ : ℝ)) * ‖x - y‖ := by ring
          _ ≤ 1 * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right hcδ (norm_nonneg _)
          _ = ‖x - y‖ := one_mul _
      change ‖orthogonalStretch (LinearMap.range A.toLinearMap) c (f x) -
          orthogonalStretch (LinearMap.range A.toLinearMap) c (f y)‖ ≤ _
      rw [← map_sub, hdecomp, map_add, hfix]
      calc
        ‖A (x - y) + orthogonalStretch (LinearMap.range A.toLinearMap) c e‖ ≤
            ‖A (x - y)‖ +
              ‖orthogonalStretch (LinearMap.range A.toLinearMap) c e‖ := norm_add_le _ _
        _ ≤ ‖A‖ * ‖x - y‖ + ‖x - y‖ := add_le_add (A.le_opNorm _) herr
        _ ≤ (M : ℝ) * ‖x - y‖ + 1 * ‖x - y‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (norm_nonneg _)) (by simp)
        _ = ((M + 1 : ℝ≥0) : ℝ) * ‖x - y‖ := by
          push_cast
          ring)

omit [FiniteDimensional ℝ E] in
private theorem ApproximatesLinearOn.exists_measurable_hausdorffMeasure_fiber_majorant_of_not_surjective
    {f : E → F} {A : E →L[ℝ] F} {s : Set E} {δ M c : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hc : 1 ≤ c)
    (hcδ : c * δ ≤ 1) (hA : ‖A‖₊ ≤ M) (hAsurj : ¬ Function.Surjective A)
    {k : ℝ} (hk : 0 < k) (hfin : μH[k + Module.finrank ℝ F] s ≠ ∞) :
    ∃ q : F → ℝ≥0∞, Measurable q ∧
      (∀ y, μH[k] (s ∩ f ⁻¹' {y}) ≤ q y) ∧
        ∫⁻ y : F, q y ∂μHE[Module.finrank ℝ F] ≤
          (c : ℝ≥0∞)⁻¹ *
            ((M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
              volume (Metric.closedBall (0 : F) 1) *
                μH[k + Module.finrank ℝ F] s) := by
  let V : Submodule ℝ F := LinearMap.range A.toLinearMap
  let S : F →ₗ[ℝ] F := orthogonalStretch V c
  have hSlip : LipschitzOnWith (M + 1) (S ∘ f) s := by
    exact ApproximatesLinearOn.lipschitzOnWith_orthogonalStretch_comp hf hc hcδ hA
  obtain ⟨q, hqmeas, hqmajor, hqintegral⟩ :=
    hSlip.exists_measurable_hausdorffMeasure_fiber_majorant hk hfin
  have hSbij : Function.Bijective S := orthogonalStretch_bijective V (by positivity)
  have hSmeas : Measurable S := S.continuous_of_finiteDimensional.measurable
  have hfiber : ∀ y : F, s ∩ (S ∘ f) ⁻¹' {S y} = s ∩ f ⁻¹' {y} := by
    intro y
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Function.comp_apply]
    exact and_congr_right fun _ => hSbij.1.eq_iff
  have hVproper : V < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact fun hV => hAsurj (LinearMap.range_eq_top.mp hV)
  have hcodim : 0 < Module.finrank ℝ Vᗮ := by
    have hVrank : Module.finrank ℝ V < Module.finrank ℝ F :=
      by simpa only [finrank_top] using Submodule.finrank_lt_finrank_of_lt hVproper
    have hsum := V.finrank_add_finrank_orthogonal
    omega
  have hdet : ENNReal.ofReal S.normDet =
      (c : ℝ≥0∞) ^ Module.finrank ℝ Vᗮ := by
    rw [show S.normDet = (c : ℝ) ^ Module.finrank ℝ Vᗮ by
      simpa [S, V, abs_of_nonneg c.coe_nonneg] using orthogonalStretch_normDet V (c : ℝ)]
    rw [ENNReal.ofReal_pow c.coe_nonneg]
    simp
  have hcdet : (c : ℝ≥0∞) ≤ ENNReal.ofReal S.normDet := by
    rw [hdet]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hcodim.ne'
    rw [hr, pow_succ]
    exact le_mul_of_one_le_left (show (0 : ℝ≥0∞) ≤ c by positivity)
      (one_le_pow₀ (show (1 : ℝ≥0∞) ≤ (c : ℝ≥0∞) by exact_mod_cast hc))
  let Q : F → ℝ≥0∞ := q ∘ S
  refine ⟨Q, hqmeas.comp hSmeas, ?_, ?_⟩
  · intro y
    dsimp only [Q, Function.comp_apply]
    rw [← hfiber y]
    exact hqmajor (S y)
  · let e : F ≃L[ℝ] F :=
      (LinearEquiv.ofBijective S hSbij).toContinuousLinearEquiv
    have hmap : ∫⁻ a : F, q a ∂Measure.map S volume =
        ∫⁻ a : F, q (S a) ∂volume := by
      change ∫⁻ a : F, q a ∂Measure.map (e : F → F) volume =
        ∫⁻ a : F, q (e a) ∂volume
      exact e.toHomeomorph.measurableEmbedding.lintegral_map
        (μ := (volume : Measure F)) q
    rw [map_volume_linear_equiv S hSbij, lintegral_smul_measure] at hmap
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      show (∫⁻ y : F, Q y) =
        (ENNReal.ofReal S.normDet)⁻¹ * ∫⁻ y : F, q y by
          simpa only [Q, Function.comp_apply, ENNReal.smul_def, smul_eq_mul] using hmap.symm]
    calc
      (ENNReal.ofReal S.normDet)⁻¹ * ∫⁻ y : F, q y ≤
          (ENNReal.ofReal S.normDet)⁻¹ *
            ((M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
              volume (Metric.closedBall (0 : F) 1) *
                μH[k + Module.finrank ℝ F] s) := by
        apply mul_right_mono
        simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
          ENNReal.coe_add, ENNReal.coe_one] using hqintegral
      _ ≤ (c : ℝ≥0∞)⁻¹ *
            ((M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
              volume (Metric.closedBall (0 : F) 1) *
                μH[k + Module.finrank ℝ F] s) := by
        gcongr

private theorem hausdorffMeasure_finrank_ne_top_of_isCompact
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : IsCompact s) :
    μH[(Module.finrank ℝ X : ℝ)] s ≠ ∞ := by
  have hμ : μHE[Module.finrank ℝ X] s ≠ ∞ := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact hs.measure_lt_top.ne
  intro htop
  apply hμ
  rw [Measure.euclideanHausdorffMeasure_apply_eq_smul, htop]
  simp [MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

private theorem critical_lintegral_hausdorffMeasure_fiber_eq_zero_compact
    {f : E → F} (hf : ContDiff ℝ 1 f) {s : Set E} (hs : IsCompact s)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x))
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E) :
    Measurable (fun y : F =>
      μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)] (s ∩ f ⁻¹' {y})) ∧
      ∫⁻ y : F, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
          (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F] = 0 := by
  classical
  let k : ℕ := Module.finrank ℝ E - Module.finrank ℝ F
  have hk : 0 < k := Nat.sub_pos_of_lt hEF
  have hmeas : Measurable (fun y : F => μH[(k : ℝ)] (s ∩ f ⁻¹' {y})) :=
    hf.continuous.continuousOn.measurable_hausdorffMeasure_fiber hs (by exact_mod_cast hk)
  have hdim : (k : ℝ) + Module.finrank ℝ F = Module.finrank ℝ E := by
    exact_mod_cast Nat.sub_add_cancel hEF.le
  have hfin : μH[(k : ℝ) + Module.finrank ℝ F] s ≠ ∞ := by
    rw [hdim]
    exact hausdorffMeasure_finrank_ne_top_of_isCompact hs
  have hbdd : BddAbove ((fun x : E => ‖fderiv ℝ f x‖₊) '' s) :=
    IsCompact.bddAbove_image hs
      ((hf.continuous_fderiv one_ne_zero).nnnorm.continuousOn)
  obtain ⟨M, hM⟩ := bddAbove_def.mp hbdd
  have hMbound : ∀ x ∈ s, ‖fderiv ℝ f x‖₊ ≤ M := by
    intro x hx
    exact hM _ ⟨x, hx, rfl⟩
  have hf' : ∀ x ∈ s,
      HasFDerivWithinAt f (fderiv ℝ f x) s x := by
    intro x _
    exact (hf.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt
  let C : ℝ≥0∞ := (M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
    volume (Metric.closedBall (0 : F) 1) * μH[(k : ℝ) + Module.finrank ℝ F] s
  have hbound : ∀ p : ℕ,
      ∫⁻ y : F, μH[(k : ℝ)] (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F] ≤
        ((p + 1 : ℝ≥0) : ℝ≥0∞)⁻¹ * C := by
    intro p
    rcases eq_empty_or_nonempty s with rfl | hsne
    · simp
    let c : ℝ≥0 := p + 1
    have hc : 1 ≤ c := by simp [c]
    have hc0 : c ≠ 0 := by positivity
    obtain ⟨t, A, htdisj, htmeas, htcover, htapprox, htrep⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
        f s (fderiv ℝ f) hf'
          (fun _ => c⁻¹) (fun _ => inv_ne_zero hc0)
    have hs_union : s = ⋃ n, s ∩ t n := by
      rw [← inter_iUnion]
      exact Subset.antisymm (subset_inter Subset.rfl htcover) inter_subset_left
    have htmeas' : ∀ n, MeasurableSet (s ∩ t n) :=
      fun n => hs.measurableSet.inter (htmeas n)
    have htdisj' : Pairwise fun i j => Disjoint (s ∩ t i) (s ∩ t j) :=
      pairwise_disjoint_mono htdisj fun n => inter_subset_right
    have hmeasure : ∑' n, μH[(k : ℝ) + Module.finrank ℝ F] (s ∩ t n) =
        μH[(k : ℝ) + Module.finrank ℝ F] s := by
      rw [← measure_iUnion htdisj' htmeas', ← hs_union]
    have hpiece : ∀ n, ∃ q : F → ℝ≥0∞, Measurable q ∧
        (∀ y, μH[(k : ℝ)] ((s ∩ t n) ∩ f ⁻¹' {y}) ≤ q y) ∧
          ∫⁻ y : F, q y ∂μHE[Module.finrank ℝ F] ≤
            (c : ℝ≥0∞)⁻¹ *
              ((M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
                volume (Metric.closedBall (0 : F) 1) *
                  μH[(k : ℝ) + Module.finrank ℝ F] (s ∩ t n)) := by
      intro n
      obtain ⟨x, hxs, hAx⟩ := htrep hsne n
      apply ApproximatesLinearOn.exists_measurable_hausdorffMeasure_fiber_majorant_of_not_surjective
        (htapprox n) hc
      · simp [c, hc0]
      · rw [hAx]
        exact hMbound x hxs
      · rw [hAx]
        exact hcrit x hxs
      · exact_mod_cast hk
      · exact ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
    choose q hqmeas hqmajor hqintegral using hpiece
    let Q : F → ℝ≥0∞ := fun y => ∑' n, q n y
    have hQmeas : Measurable Q := Measurable.tsum hqmeas
    have hfiber_union : ∀ y : F,
        s ∩ f ⁻¹' {y} = ⋃ n, (s ∩ t n) ∩ f ⁻¹' {y} := by
      intro y
      calc
        s ∩ f ⁻¹' {y} = (⋃ n, s ∩ t n) ∩ f ⁻¹' {y} :=
          congrArg (fun u => u ∩ f ⁻¹' {y}) hs_union
        _ = ⋃ n, (s ∩ t n) ∩ f ⁻¹' {y} :=
          iUnion_inter (f ⁻¹' {y}) (fun n => s ∩ t n)
    have hpoint : ∀ y : F, μH[(k : ℝ)] (s ∩ f ⁻¹' {y}) ≤ Q y := by
      intro y
      rw [hfiber_union y]
      exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n => hqmajor n y)
    calc
      (∫⁻ y : F, μH[(k : ℝ)] (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F]) ≤
          ∫⁻ y : F, Q y ∂μHE[Module.finrank ℝ F] := lintegral_mono hpoint
      _ = ∑' n, ∫⁻ y : F, q n y ∂μHE[Module.finrank ℝ F] :=
        MeasureTheory.lintegral_tsum fun n => (hqmeas n).aemeasurable
      _ ≤ ∑' n, (c : ℝ≥0∞)⁻¹ *
            ((M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
              volume (Metric.closedBall (0 : F) 1) *
                μH[(k : ℝ) + Module.finrank ℝ F] (s ∩ t n)) :=
        ENNReal.tsum_le_tsum hqintegral
      _ = (c : ℝ≥0∞)⁻¹ * C := by
        rw [show C = (M + 1 : ℝ≥0∞) ^ Module.finrank ℝ F *
          volume (Metric.closedBall (0 : F) 1) *
            μH[(k : ℝ) + Module.finrank ℝ F] s from rfl, ← hmeasure]
        simp_rw [← mul_assoc]
        rw [ENNReal.tsum_mul_left]
      _ = ((p + 1 : ℝ≥0) : ℝ≥0∞)⁻¹ * C := by rfl
  have hCtop : C ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      · exact measure_closedBall_lt_top.ne
    · exact hfin
  have hinv : Filter.Tendsto (fun p : ℕ => ((p + 1 : ℝ≥0) : ℝ≥0∞)⁻¹)
      Filter.atTop (nhds 0) := by
    have hfun : (fun p : ℕ => ((p + 1 : ℝ≥0) : ℝ≥0∞)⁻¹) =
        (fun n : ℕ => (n : ℝ≥0∞)⁻¹) ∘ fun p => p + 1 := by
      funext p
      simp [Function.comp_apply]
    rw [hfun]
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
  have htend : Filter.Tendsto (fun p : ℕ => ((p + 1 : ℝ≥0) : ℝ≥0∞)⁻¹ * C)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hinv (Or.inr hCtop)
  refine ⟨by simpa only [k] using hmeas, ?_⟩
  exact bot_unique (ge_of_tendsto' htend hbound)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem normDet_adjoint_eq_zero_iff_not_surjective (L : E →ₗ[ℝ] F) :
    L.adjoint.normDet = 0 ↔ ¬ Function.Surjective L := by
  rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, ← LinearMap.orthogonal_range]
  constructor
  · intro h hsurj
    apply h
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  · intro h hbot
    apply h
    exact LinearMap.range_eq_top.mp (Submodule.orthogonal_eq_bot_iff.mp hbot)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem isClosed_not_surjective_fderiv
    {f : E → F} (hf : ContDiff ℝ 1 f) :
    IsClosed {x | ¬ Function.Surjective (fderiv ℝ f x)} := by
  have hcont : Continuous (fun x : E =>
      (fderiv ℝ f x).toLinearMap.adjoint.normDet) :=
    ContinuousLinearMap.continuous_normDet.comp
      (ContinuousLinearMap.adjoint.continuous.comp
        (hf.continuous_fderiv one_ne_zero))
  have hc : {x : E | ¬ Function.Surjective (fderiv ℝ f x)} =
      (fun x : E => (fderiv ℝ f x).toLinearMap.adjoint.normDet) ⁻¹' {0} := by
    ext x
    exact normDet_adjoint_eq_zero_iff_not_surjective
      (fderiv ℝ f x).toLinearMap |>.symm
  rw [hc]
  exact isClosed_singleton.preimage hcont

private theorem critical_lintegral_hausdorffMeasure_fiber_eq_zero
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E) :
    Measurable (fun y : F => μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
      ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})) ∧
      ∫⁻ y : F, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
          ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})
            ∂μHE[Module.finrank ℝ F] = 0 := by
  let c : Set E := {x | ¬ Function.Surjective (fderiv ℝ f x)}
  let t : ℕ → Set E := fun n => c ∩ Metric.closedBall 0 n
  have hcclosed : IsClosed c := isClosed_not_surjective_fderiv hf
  have htcompact : ∀ n, IsCompact (t n) := fun n =>
    IsCompact.inter_left (isCompact_closedBall (0 : E) n) hcclosed
  have htmono : Monotone t := by
    intro n m hnm
    exact inter_subset_inter_right c (Metric.closedBall_subset_closedBall (by exact_mod_cast hnm))
  have htunion : ⋃ n, t n = c := by
    exact Metric.iUnion_inter_closedBall_nat c 0
  have htcrit : ∀ n x, x ∈ t n →
      ¬ Function.Surjective (fderiv ℝ f x) := by
    intro n x hx
    exact hx.1
  have hlocal : ∀ n,
      Measurable (fun y : F =>
        μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)] (t n ∩ f ⁻¹' {y})) ∧
        ∫⁻ y : F, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
            (t n ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F] = 0 := by
    intro n
    exact critical_lintegral_hausdorffMeasure_fiber_eq_zero_compact hf
      (htcompact n) (htcrit n) hEF
  have hfibermono : Monotone (fun n => fun y : F =>
      μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)] (t n ∩ f ⁻¹' {y})) := by
    intro n m hnm y
    exact measure_mono (inter_subset_inter_left _ (htmono hnm))
  have hfiber : ∀ y : F,
      μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)] (c ∩ f ⁻¹' {y}) =
        ⨆ n, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
          (t n ∩ f ⁻¹' {y}) := by
    intro y
    rw [← htunion, iUnion_inter]
    exact (show Monotone (fun n => t n ∩ f ⁻¹' {y}) from fun _ _ hnm =>
      inter_subset_inter_left _ (htmono hnm)).directed_le.measure_iUnion
  refine ⟨?_, ?_⟩
  · rw [show (fun y : F =>
        μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
          ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})) =
      (fun y : F => ⨆ n, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
        (t n ∩ f ⁻¹' {y})) by
          funext y
          exact hfiber y]
    exact Measurable.iSup fun n => (hlocal n).1
  · rw [show (fun y : F =>
        μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
          ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})) =
      (fun y : F => ⨆ n, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
        (t n ∩ f ⁻¹' {y})) by
          funext y
          exact hfiber y]
    rw [MeasureTheory.lintegral_iSup (fun n => (hlocal n).1) hfibermono]
    simp_rw [(hlocal _).2]
    simp

omit [FiniteDimensional ℝ F] [MeasurableSpace E] in
theorem dimension_lowering_image_null
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (hEF : Module.finrank ℝ E < Module.finrank ℝ F) :
    μHE[Module.finrank ℝ F] (range f) = 0 := by
  have hdim : dimH (range f) < (Module.finrank ℝ F : ℝ≥0∞) := by
    exact lt_of_le_of_lt hf.dimH_range_le (by exact_mod_cast hEF)
  have hzero : μH[(Module.finrank ℝ F : ℝ)] (range f) = 0 := by
    simpa using (hausdorffMeasure_of_dimH_lt (d := (Module.finrank ℝ F : ℝ≥0)) hdim)
  rw [Measure.euclideanHausdorffMeasure_def]
  simp [hzero]

theorem critical_image_null
    {f : E → E} {s : Set E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, (f' x).det = 0) :
    volume (f '' s) = 0 := by
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (volume : Measure E) hf' hcrit

private theorem normDet_withLp_first_identity
    {F K K' : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    [NormedAddCommGroup K'] [InnerProductSpace ℝ K'] [FiniteDimensional ℝ K']
    (Q : WithLp 2 (F × K) →ₗ[ℝ] WithLp 2 (F × K'))
    (D : K →ₗ[ℝ] K') (hK : Module.finrank ℝ K = Module.finrank ℝ K')
    (hfst : ∀ x, (Q x).fst = x.fst)
    (hsnd : ∀ z, (Q (WithLp.toLp 2 (0, z))).snd = D z) :
    Q.normDet = D.normDet := by
  let bF := stdOrthonormalBasis ℝ F
  let bK := stdOrthonormalBasis ℝ K
  let bK' := (stdOrthonormalBasis ℝ K').reindex (Fin.castOrderIso hK.symm).toEquiv
  let Q0 : F × K →ₗ[ℝ] F × K' :=
    (WithLp.linearEquiv 2 ℝ (F × K')).toLinearMap ∘ₗ Q ∘ₗ
      (WithLp.linearEquiv 2 ℝ (F × K)).symm.toLinearMap
  rw [LinearMap.normDet_eq_norm_det_toMatrix Q (bF.prod bK) (bF.prod bK')]
  rw [LinearMap.normDet_eq_norm_det_toMatrix D bK bK']
  have hmatrix :
      LinearMap.toMatrix (bF.prod bK).toBasis (bF.prod bK').toBasis Q =
        LinearMap.toMatrix (bF.toBasis.prod bK.toBasis)
          (bF.toBasis.prod bK'.toBasis) Q0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply', OrthonormalBasis.prod, Module.Basis.prod_repr_inl,
        Module.Basis.prod_repr_inr, Q0]
  rw [hmatrix]
  have hblocks :
      LinearMap.toMatrix (bF.toBasis.prod bK.toBasis)
          (bF.toBasis.prod bK'.toBasis) Q0 =
        Matrix.fromBlocks 1 0
          (LinearMap.toMatrix bF.toBasis bK'.toBasis
            ((LinearMap.snd ℝ F K') ∘ₗ Q0 ∘ₗ LinearMap.inl ℝ F K))
          (LinearMap.toMatrix bK.toBasis bK'.toBasis D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply', Module.Basis.prod_repr_inl,
        Module.Basis.prod_repr_inr, Matrix.one_apply, Q0, hfst, hsnd]
  rw [hblocks, Matrix.det_fromBlocks_zero₁₂]
  simp

private theorem normDet_comp_vertical_mul_normDet
    {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    (A : E →ₗ[ℝ] WithLp 2 (F × K)) (hA : Function.Bijective A)
    (L : E →ₗ[ℝ] F) (hL : ∀ x, (A x).fst = L x) :
    ((LinearEquiv.ofBijective A hA).symm.toLinearMap ∘ₗ
        ((WithLp.linearEquiv 2 ℝ (F × K)).symm.toLinearMap ∘ₗ
          LinearMap.inr ℝ F K)).normDet * A.normDet =
      L.adjoint.normDet := by
  let e : E ≃ₗ[ℝ] WithLp 2 (F × K) := LinearEquiv.ofBijective A hA
  let I : K →ₗ[ℝ] WithLp 2 (F × K) :=
    (WithLp.linearEquiv 2 ℝ (F × K)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ F K
  let B : K →ₗ[ℝ] E := e.symm.toLinearMap ∘ₗ I
  have hLsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := hA.2 (WithLp.toLp 2 (y, 0))
    refine ⟨x, ?_⟩
    rw [← hL x, hx]
    rfl
  let K0 : Submodule ℝ E := LinearMap.ker L
  have hBmem : ∀ z, B z ∈ K0 := by
    intro z
    change L (B z) = 0
    rw [← hL (B z)]
    change (A (e.symm (I z))).fst = 0
    calc
      (A (e.symm (I z))).fst = (I z).fst := by
        exact congrArg WithLp.fst (e.apply_symm_apply (I z))
      _ = 0 := rfl
  let D : K →ₗ[ℝ] K0 := B.codRestrict K0 hBmem
  let C : E →ₗ[ℝ] WithLp 2 (F × K0) := linearCoareaCoordinates L
  let Q : WithLp 2 (F × K) →ₗ[ℝ] WithLp 2 (F × K0) :=
    C ∘ₗ e.symm.toLinearMap
  have hdimA : Module.finrank ℝ E = Module.finrank ℝ (WithLp 2 (F × K)) :=
    e.finrank_eq
  have hdimK : Module.finrank ℝ K = Module.finrank ℝ K0 := by
    have hWith : Module.finrank ℝ (WithLp 2 (F × K)) =
        Module.finrank ℝ (F × K) :=
      (WithLp.linearEquiv 2 ℝ (F × K)).finrank_eq
    have hdimA' : Module.finrank ℝ E = Module.finrank ℝ F + Module.finrank ℝ K := by
      rw [hdimA, hWith, Module.finrank_prod]
    have hrange : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ F := by
      rw [LinearMap.range_eq_top.mpr hLsurj]
      simp
    have hrank := L.finrank_range_add_finrank_ker
    change Module.finrank ℝ K = Module.finrank ℝ (LinearMap.ker L)
    omega
  have hQfst : ∀ x, (Q x).fst = x.fst := by
    intro x
    change L (e.symm x) = x.fst
    rw [← hL (e.symm x)]
    exact congrArg WithLp.fst (e.apply_symm_apply x)
  have hQsnd : ∀ z, (Q (WithLp.toLp 2 (0, z))).snd = D z := by
    intro z
    change K0.orthogonalProjectionOnto (e.symm (I z)) = D z
    change K0.orthogonalProjectionOnto (B z) = D z
    change K0.orthogonalProjectionOnto (B z) = ⟨B z, hBmem z⟩
    exact K0.orthogonalProjectionOnto_mem_subspace_eq_self ⟨B z, hBmem z⟩
  have hQdet : Q.normDet = D.normDet :=
    normDet_withLp_first_identity Q D hdimK hQfst hQsnd
  have hDdet : D.normDet = B.normDet := by
    exact LinearMap.normDet_codRestrict hBmem
  have hfactor : C = Q ∘ₗ A := by
    rw [show A = e.toLinearMap by rfl]
    ext x
    simp [Q]
  rw [← linear_coarea_coordinates_normDet L hLsurj, show linearCoareaCoordinates L = C from rfl]
  rw [hfactor, LinearMap.normDet_comp_of_finrank_eq A Q hdimA, hQdet, hDdet]

private theorem linearCoareaCoordinates_bijective
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) :
    Function.Bijective (linearCoareaCoordinates L) := by
  constructor
  · intro x y hxy
    have hzero : linearCoareaCoordinates L (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hLx : L (x - y) = 0 := by
      have := congrArg WithLp.fst hzero
      simpa using this
    have hxK : x - y ∈ LinearMap.ker L := hLx
    have hPx : (LinearMap.ker L).orthogonalProjectionOnto (x - y) = 0 := by
      have := congrArg WithLp.snd hzero
      simpa using this
    have hself :=
      (LinearMap.ker L).orthogonalProjectionOnto_mem_subspace_eq_self ⟨x - y, hxK⟩
    have : x - y = 0 := by
      simpa [hPx] using (congrArg Subtype.val hself).symm
    exact sub_eq_zero.mp this
  · intro p
    obtain ⟨x, hx⟩ := hL p.fst
    let P := (LinearMap.ker L).orthogonalProjectionOnto
    let z : LinearMap.ker L := p.snd
    refine ⟨x - (P x : E) + (z : E), ?_⟩
    apply (WithLp.equiv 2 (F × LinearMap.ker L)).injective
    apply Prod.ext
    · change L (x - (P x : E) + (z : E)) = p.fst
      rw [L.map_add, L.map_sub, hx]
      have hPx : L (P x : E) = 0 := (P x).2
      have hz : L (z : E) = 0 := z.2
      rw [hPx, hz, sub_zero, add_zero]
    · change P (x - (P x : E) + (z : E)) = z
      rw [map_add, map_sub]
      have hPP : P (P x : E) = P x :=
        (LinearMap.ker L).orthogonalProjectionOnto_mem_subspace_eq_self (P x)
      have hPz : P (z : E) = z :=
        (LinearMap.ker L).orthogonalProjectionOnto_mem_subspace_eq_self z
      rw [hPP, hPz, sub_self, zero_add]

section LocalCoordinates

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

private def coareaCoordinatesAt (f : E → F) (a : E) (x : E) :
    WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) :=
  WithLp.toLp 2
    (f x, (LinearMap.ker (fderiv ℝ f a).toLinearMap).orthogonalProjectionOnto (x - a))

private def coareaCoordinatesFDerivAt (f : E → F) (a x : E) :
    E →L[ℝ] WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F
      (LinearMap.ker (fderiv ℝ f a).toLinearMap)).symm.toContinuousLinearMap.comp
    ((fderiv ℝ f x).prod
      (LinearMap.ker (fderiv ℝ f a).toLinearMap).orthogonalProjectionOnto)

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem hasFDerivAt_coareaCoordinatesAt
    {f : E → F} (hf : Differentiable ℝ f) (a x : E) :
    HasFDerivAt (coareaCoordinatesAt f a) (coareaCoordinatesFDerivAt f a x) x := by
  let K := LinearMap.ker (fderiv ℝ f a).toLinearMap
  have hpair : HasFDerivAt
      (fun z : E => (f z, K.orthogonalProjectionOnto (z - a)))
      ((fderiv ℝ f x).prod K.orthogonalProjectionOnto) x := by
    exact (hf x).hasFDerivAt.prodMk
      (K.orthogonalProjectionOnto.hasFDerivAt.comp x (hasFDerivAt_sub_const a))
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ F K).symm.toContinuousLinearMap.hasFDerivAt.comp
    x hpair

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem coareaCoordinatesFDerivAt_self
    (f : E → F) (a : E) :
    (coareaCoordinatesFDerivAt f a a).toLinearMap =
      linearCoareaCoordinates (fderiv ℝ f a).toLinearMap := by
  rfl

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem contDiff_coareaCoordinatesAt
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E) :
    ContDiff ℝ 1 (coareaCoordinatesAt f a) := by
  let K := LinearMap.ker (fderiv ℝ f a).toLinearMap
  let T := (WithLp.prodContinuousLinearEquiv 2 ℝ F K).symm.toContinuousLinearMap
  change ContDiff ℝ 1 (fun x => T (f x, K.orthogonalProjectionOnto (x - a)))
  exact T.contDiff.comp
    (hf.prodMk (K.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem continuous_coareaCoordinatesFDerivAt_toLinearMap
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E) :
    Continuous (fun x => (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet) := by
  apply ContinuousLinearMap.continuous_normDet.comp
  let K := LinearMap.ker (fderiv ℝ f a).toLinearMap
  let T := (WithLp.prodContinuousLinearEquiv 2 ℝ F K).symm.toContinuousLinearMap
  have hprod : Continuous (fun x => (fderiv ℝ f x).prod K.orthogonalProjectionOnto) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
      ((hf.continuous_fderiv one_ne_zero).prodMk continuous_const)
  exact continuous_const.clm_comp hprod

private def coareaCoordinatesEquivAt
    (f : E → F) (a : E) (ha : Function.Surjective (fderiv ℝ f a)) :
    E ≃L[ℝ] WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) :=
  (LinearEquiv.ofBijective (coareaCoordinatesFDerivAt f a a).toLinearMap (by
    rw [coareaCoordinatesFDerivAt_self]
    exact linearCoareaCoordinates_bijective _ ha)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem coareaCoordinatesEquivAt_coe
    (f : E → F) (a : E) (ha : Function.Surjective (fderiv ℝ f a)) :
    (coareaCoordinatesEquivAt f a ha :
      E →L[ℝ] WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)) =
      coareaCoordinatesFDerivAt f a a := by
  rfl

private def regularCoareaChart
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) :
    OpenPartialHomeomorph E
      (WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)) :=
  (contDiff_coareaCoordinatesAt hf a).contDiffAt.toOpenPartialHomeomorph
    (coareaCoordinatesAt f a)
    (by
      rw [coareaCoordinatesEquivAt_coe f a ha]
      exact hasFDerivAt_coareaCoordinatesAt (hf.differentiable one_ne_zero) a a)
    one_ne_zero

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem regularCoareaChart_apply
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) (x : E) :
    regularCoareaChart hf a ha x = coareaCoordinatesAt f a x := by
  rfl

private def regularCoareaChartSource
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) : Set E :=
  (regularCoareaChart hf a ha).source ∩
    {x | (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet ≠ 0}

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem isOpen_regularCoareaChartSource
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) :
    IsOpen (regularCoareaChartSource hf a ha) := by
  apply (regularCoareaChart hf a ha).open_source.inter
  exact isClosed_singleton.isOpen_compl.preimage
    (continuous_coareaCoordinatesFDerivAt_toLinearMap hf a)

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem self_mem_regularCoareaChartSource
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) :
    a ∈ regularCoareaChartSource hf a ha := by
  refine ⟨(contDiff_coareaCoordinatesAt hf a).contDiffAt.mem_toOpenPartialHomeomorph_source
    (by
      rw [coareaCoordinatesEquivAt_coe f a ha]
      exact hasFDerivAt_coareaCoordinatesAt (hf.differentiable one_ne_zero) a a)
    one_ne_zero, ?_⟩
  change (coareaCoordinatesFDerivAt f a a).toLinearMap.normDet ≠ 0
  rw [coareaCoordinatesFDerivAt_self]
  exact (LinearMap.normDet_ne_zero_tfae
    (linearCoareaCoordinates (fderiv ℝ f a).toLinearMap) |>.out 4 0 |>.mp
      (linearCoareaCoordinates_bijective _ ha).1)

private def regularCoareaChartInverse
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) :
    WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) → E :=
  by
    classical
    exact (regularCoareaChart hf a ha).target.piecewise
      (regularCoareaChart hf a ha).symm 0

omit [FiniteDimensional ℝ F] in
private theorem measurable_regularCoareaChartInverse
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) :
    Measurable (regularCoareaChartInverse hf a ha) := by
  classical
  change Measurable ((regularCoareaChart hf a ha).target.piecewise
    (regularCoareaChart hf a ha).symm (fun _ => 0))
  exact (regularCoareaChart hf a ha).continuousOn_symm.measurable_piecewise
    continuous_const.continuousOn (regularCoareaChart hf a ha).open_target.measurableSet

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem regularCoareaChartInverse_eq_symm
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    {p : WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)}
    (hp : p ∈ (regularCoareaChart hf a ha).target) :
    regularCoareaChartInverse hf a ha p = (regularCoareaChart hf a ha).symm p := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hp

private def coareaCoordinatesEquivAtPoint
    (f : E → F) (a x : E) (ha : Function.Surjective (fderiv ℝ f a))
    (hx : (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet ≠ 0) :
    E ≃L[ℝ] WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) :=
  (LinearEquiv.ofBijective (coareaCoordinatesFDerivAt f a x).toLinearMap (by
    have hinj : Function.Injective (coareaCoordinatesFDerivAt f a x) :=
      LinearMap.normDet_ne_zero_tfae
        (coareaCoordinatesFDerivAt f a x).toLinearMap |>.out 0 4 |>.mp hx
    have hdim := (coareaCoordinatesEquivAt f a ha).toLinearEquiv.finrank_eq
    exact ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
    )).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem coareaCoordinatesEquivAtPoint_coe
    (f : E → F) (a x : E) (ha : Function.Surjective (fderiv ℝ f a))
    (hx : (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet ≠ 0) :
    (coareaCoordinatesEquivAtPoint f a x ha hx :
      E →L[ℝ] WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)) =
      coareaCoordinatesFDerivAt f a x := by
  rfl

private def coareaVertical
    (f : E → F) (a : E) :
    LinearMap.ker (fderiv ℝ f a).toLinearMap →L[ℝ]
      WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F
      (LinearMap.ker (fderiv ℝ f a).toLinearMap)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ F (LinearMap.ker (fderiv ℝ f a).toLinearMap))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem hasFDerivAt_regularCoareaChartInverse
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    {p : WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)}
    (hp : p ∈ (regularCoareaChart hf a ha).target)
    (hx : (coareaCoordinatesFDerivAt f a
      ((regularCoareaChart hf a ha).symm p)).toLinearMap.normDet ≠ 0) :
    HasFDerivAt (regularCoareaChartInverse hf a ha)
      ((coareaCoordinatesEquivAtPoint f a
        ((regularCoareaChart hf a ha).symm p) ha hx).symm :
          WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap) →L[ℝ] E) p := by
  let e := regularCoareaChart hf a ha
  let A := coareaCoordinatesEquivAtPoint f a (e.symm p) ha hx
  have hforward : HasFDerivAt e (A : E →L[ℝ] _) (e.symm p) := by
    rw [show (e : E → _) = coareaCoordinatesAt f a from rfl]
    rw [coareaCoordinatesEquivAtPoint_coe]
    exact hasFDerivAt_coareaCoordinatesAt (hf.differentiable one_ne_zero) a (e.symm p)
  have hinverse : HasFDerivAt e.symm (A.symm : _ →L[ℝ] E) p :=
    e.hasFDerivAt_symm hp hforward
  apply hinverse.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hp] with q hq
  simpa [e] using regularCoareaChartInverse_eq_symm hf a ha hq

private def regularCoareaFiberParam
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) (y : F)
    (z : LinearMap.ker (fderiv ℝ f a).toLinearMap) : E :=
  regularCoareaChartInverse hf a ha (WithLp.toLp 2 (y, z))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem hasFDerivAt_regularCoareaFiberParam
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) (y : F)
    {z : LinearMap.ker (fderiv ℝ f a).toLinearMap}
    (hp : WithLp.toLp 2 (y, z) ∈ (regularCoareaChart hf a ha).target)
    (hx : (coareaCoordinatesFDerivAt f a
      ((regularCoareaChart hf a ha).symm (WithLp.toLp 2 (y, z)))).toLinearMap.normDet ≠ 0) :
    HasFDerivAt (regularCoareaFiberParam hf a ha y)
      ((coareaCoordinatesEquivAtPoint f a
          ((regularCoareaChart hf a ha).symm (WithLp.toLp 2 (y, z))) ha hx).symm.toContinuousLinearMap.comp
        (coareaVertical f a)) z := by
  change HasFDerivAt
    (fun w : LinearMap.ker (fderiv ℝ f a).toLinearMap =>
      regularCoareaChartInverse hf a ha (WithLp.toLp 2 (y, w))) _ z
  apply (hasFDerivAt_regularCoareaChartInverse hf a ha hp hx).comp z
  let T := (WithLp.prodContinuousLinearEquiv 2 ℝ F
    (LinearMap.ker (fderiv ℝ f a).toLinearMap)).symm.toContinuousLinearMap
  change HasFDerivAt
    (fun w : LinearMap.ker (fderiv ℝ f a).toLinearMap => T (y, w))
    (coareaVertical f a) z
  exact T.hasFDerivAt.comp z ((hasFDerivAt_const y z).prodMk (hasFDerivAt_id z))

private def regularCoareaFiberJacobian
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    (p : WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)) : ℝ :=
  ((fderiv ℝ (regularCoareaChartInverse hf a ha) p).comp
    (coareaVertical f a)).toLinearMap.normDet

private theorem measurable_regularCoareaFiberJacobian
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a)) :
    Measurable (regularCoareaFiberJacobian hf a ha) := by
  apply ContinuousLinearMap.continuous_normDet.measurable.comp
  exact (ContinuousLinearMap.compL ℝ
      (LinearMap.ker (fderiv ℝ f a).toLinearMap)
      (WithLp 2 (F × LinearMap.ker (fderiv ℝ f a).toLinearMap)) E).continuous₂.measurable.comp
    ((measurable_fderiv ℝ (regularCoareaChartInverse hf a ha)).prodMk measurable_const)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem regularCoareaFiberJacobian_mul_chartJacobian
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    {x : E} (hx : x ∈ regularCoareaChartSource hf a ha) :
    regularCoareaFiberJacobian hf a ha (coareaCoordinatesAt f a x) *
        (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet =
      (fderiv ℝ f x).toLinearMap.adjoint.normDet := by
  let e := regularCoareaChart hf a ha
  have hxtarget : coareaCoordinatesAt f a x ∈ e.target := by
    rw [← regularCoareaChart_apply hf a ha]
    exact e.map_source hx.1
  have hsymm : e.symm (coareaCoordinatesAt f a x) = x := by
    rw [← regularCoareaChart_apply hf a ha]
    exact e.left_inv hx.1
  have hsymm' : (regularCoareaChart hf a ha).symm (coareaCoordinatesAt f a x) = x :=
    hsymm
  have hderiv := hasFDerivAt_regularCoareaChartInverse hf a ha hxtarget (by
    rw [hsymm]
    exact hx.2)
  have hfd : fderiv ℝ (regularCoareaChartInverse hf a ha)
      (coareaCoordinatesAt f a x) =
        (coareaCoordinatesEquivAtPoint f a x ha hx.2).symm := by
    simpa only [hsymm'] using hderiv.fderiv
  rw [regularCoareaFiberJacobian, hfd]
  apply normDet_comp_vertical_mul_normDet
    (coareaCoordinatesFDerivAt f a x).toLinearMap
  · have hinj : Function.Injective (coareaCoordinatesFDerivAt f a x) :=
      LinearMap.normDet_ne_zero_tfae
        (coareaCoordinatesFDerivAt f a x).toLinearMap |>.out 0 4 |>.mp hx.2
    have hdim := (coareaCoordinatesEquivAt f a ha).toLinearEquiv.finrank_eq
    exact ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  · intro v
    rfl

private theorem regular_coarea_chart_formula_weighted
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    {t : Set E} (ht : MeasurableSet t)
    (htU : t ⊆ regularCoareaChartSource hf a ha)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun y : F => ∫⁻ x in t ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ (LinearMap.ker (fderiv ℝ f a).toLinearMap)]) ∧
    ∫⁻ y : F, ∫⁻ x in t ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ (LinearMap.ker (fderiv ℝ f a).toLinearMap)] =
        ∫⁻ x in t, g x * ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
          ∂μHE[Module.finrank ℝ E] := by
  classical
  let K := LinearMap.ker (fderiv ℝ f a).toLinearMap
  let W := WithLp 2 (F × K)
  let e := regularCoareaChart hf a ha
  let H := regularCoareaChartInverse hf a ha
  let q : Set (F × K) :=
    (fun p : F × K => WithLp.toLp 2 p) ⁻¹' (e '' t)
  let w : W → ℝ≥0∞ := fun p =>
    g (H p) * ENNReal.ofReal (regularCoareaFiberJacobian hf a ha p)
  have ht_source : t ⊆ e.source := fun x hx => (htU hx).1
  have heimage : MeasurableSet (e '' t) :=
    ht.image_of_continuousOn_injOn (e.continuousOn.mono ht_source)
      (e.injOn.mono ht_source)
  have hq : MeasurableSet q :=
    heimage.preimage (WithLp.prod_continuous_toLp 2 F K).measurable
  have hH : Measurable H := measurable_regularCoareaChartInverse hf a ha
  have hw : Measurable w := by
    exact (hg.comp hH).mul
      ((measurable_regularCoareaFiberJacobian hf a ha).ennreal_ofReal)
  have hfiber : ∀ y : F,
      ∫⁻ x in t ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ K] =
        ∫⁻ z in Prod.mk y ⁻¹' q, w (WithLp.toLp 2 (y, z))
          ∂μHE[Module.finrank ℝ K] := by
    intro y
    let r : Set K := Prod.mk y ⁻¹' q
    let φ : K → E := regularCoareaFiberParam hf a ha y
    have hr : MeasurableSet r := hq.preimage measurable_prodMk_left
    have hr_target : ∀ z ∈ r, WithLp.toLp 2 (y, z) ∈ e.target := by
      intro z hz
      have hzimage : WithLp.toLp 2 (y, z) ∈ e '' t := hz
      obtain ⟨x, hxt, hxz⟩ := hzimage
      exact hxz ▸ e.map_source (ht_source hxt)
    have hr_reg : ∀ z ∈ r,
        (coareaCoordinatesFDerivAt f a
          (e.symm (WithLp.toLp 2 (y, z)))).toLinearMap.normDet ≠ 0 := by
      intro z hz
      have hzimage : WithLp.toLp 2 (y, z) ∈ e '' t := hz
      obtain ⟨x, hxt, hxz⟩ := hzimage
      have hxeq : e.symm (WithLp.toLp 2 (y, z)) = x := by
        rw [← hxz]
        exact e.left_inv (ht_source hxt)
      rw [hxeq]
      exact (htU hxt).2
    have hφderiv : ∀ z ∈ r, HasFDerivAt φ (fderiv ℝ φ z) z := by
      intro z hz
      have h := hasFDerivAt_regularCoareaFiberParam hf a ha y
        (hr_target z hz) (hr_reg z hz)
      exact h.congr_fderiv h.fderiv.symm
    have hφinj : InjOn φ r := by
      intro z hz z' hz' hzz'
      have hHz : H (WithLp.toLp 2 (y, z)) = e.symm (WithLp.toLp 2 (y, z)) := by
        dsimp only [H, e]
        exact regularCoareaChartInverse_eq_symm hf a ha (hr_target z hz)
      have hHz' : H (WithLp.toLp 2 (y, z')) = e.symm (WithLp.toLp 2 (y, z')) := by
        dsimp only [H, e]
        exact regularCoareaChartInverse_eq_symm hf a ha (hr_target z' hz')
      have hzright := e.right_inv (hr_target z hz)
      have hz'right := e.right_inv (hr_target z' hz')
      have hp : WithLp.toLp 2 (y, z) = WithLp.toLp 2 (y, z') := by
        change H (WithLp.toLp 2 (y, z)) = H (WithLp.toLp 2 (y, z')) at hzz'
        rw [hHz, hHz'] at hzz'
        rw [← hzright, ← hz'right]
        exact congrArg e hzz'
      exact congrArg WithLp.snd hp
    have hφimage : φ '' r = t ∩ f ⁻¹' {y} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzimage : WithLp.toLp 2 (y, z) ∈ e '' t := hz
        obtain ⟨u, hut, huz⟩ := hzimage
        have hu_source := ht_source hut
        have hHu : H (WithLp.toLp 2 (y, z)) = u := by
          dsimp only [H, e]
          rw [← huz, regularCoareaChartInverse_eq_symm hf a ha
            ((regularCoareaChart hf a ha).map_source hu_source)]
          exact e.left_inv hu_source
        have hfy : f u = y := by
          have := congrArg WithLp.fst huz
          simpa [e, regularCoareaChart_apply, coareaCoordinatesAt] using this
        have hφu : φ z = u := by
          simpa only [φ, regularCoareaFiberParam] using hHu
        refine ⟨?_, ?_⟩
        · rw [hφu]
          exact hut
        · change f (φ z) = y
          rw [hφu]
          exact hfy
      · rintro ⟨hxt, hfy⟩
        let z : K := (e x).snd
        have hxe : e x = WithLp.toLp 2 (y, z) := by
          apply (WithLp.equiv 2 (F × K)).injective
          apply Prod.ext
          · simpa [e, regularCoareaChart_apply, coareaCoordinatesAt] using hfy
          · rfl
        have hzq : z ∈ r := by
          change WithLp.toLp 2 (y, z) ∈ e '' t
          rw [← hxe]
          exact mem_image_of_mem e hxt
        refine ⟨z, hzq, ?_⟩
        change H (WithLp.toLp 2 (y, z)) = x
        dsimp only [H, e]
        rw [← hxe, regularCoareaChartInverse_eq_symm hf a ha
          ((regularCoareaChart hf a ha).map_source (ht_source hxt))]
        exact (regularCoareaChart hf a ha).left_inv (ht_source hxt)
    have harea := injective_area_formula_image_weighted (f := φ)
      (f' := fun z => fderiv ℝ φ z) g hr hφderiv hφinj
    rw [hφimage] at harea
    rw [harea]
    apply setLIntegral_congr_fun hr
    intro z hz
    have hp := hr_target z hz
    have hx := hr_reg z hz
    have hparam := hasFDerivAt_regularCoareaFiberParam hf a ha y hp hx
    have hinverse := hasFDerivAt_regularCoareaChartInverse hf a ha hp hx
    change ENNReal.ofReal (jacobian φ z) * g (φ z) =
      w (WithLp.toLp 2 (y, z))
    rw [jacobian_of_hasFDerivAt hparam]
    dsimp only [w, H, φ, regularCoareaFiberParam]
    unfold regularCoareaFiberJacobian
    change ENNReal.ofReal _ *
        g (regularCoareaChartInverse hf a ha (WithLp.toLp 2 (y, z))) =
      g (regularCoareaChartInverse hf a ha (WithLp.toLp 2 (y, z))) * ENNReal.ofReal
        ((fderiv ℝ (regularCoareaChartInverse hf a ha) (WithLp.toLp 2 (y, z))).comp
          (coareaVertical f a)).toLinearMap.normDet
    rw [hinverse.fderiv]
    exact mul_comm _ _
  have hfubini := linear_coarea_formula_prod_hmeasure_weighted
    (E := F) (F := K) q hq (g := fun p : F × K => w (WithLp.toLp 2 p))
      (hw.comp (WithLp.prod_continuous_toLp 2 F K).measurable)
  have houter :
      ∫⁻ y : F, ∫⁻ x in t ∩ f ⁻¹' {y}, g x ∂μHE[Module.finrank ℝ K] =
        ∫⁻ p in q, w (WithLp.toLp 2 p) := by
    calc
      ∫⁻ y : F, ∫⁻ x in t ∩ f ⁻¹' {y}, g x ∂μHE[Module.finrank ℝ K] =
          ∫⁻ y : F, ∫⁻ z in Prod.mk y ⁻¹' q, w (WithLp.toLp 2 (y, z))
            ∂μHE[Module.finrank ℝ K] := lintegral_congr hfiber
      _ = ∫⁻ p in q, w (WithLp.toLp 2 p) := hfubini
  have hqimage : (fun p : F × K => WithLp.toLp 2 p) '' q = e '' t := by
    exact Set.image_preimage_eq _ (MeasurableEquiv.toLp 2 (F × K)).surjective
  have htransport :
      ∫⁻ p in q, w (WithLp.toLp 2 p) = ∫⁻ p in e '' t, w p := by
    have h := (WithLp.volume_preserving_toLp F K).setLIntegral_comp_emb
      (MeasurableEquiv.toLp 2 (F × K)).measurableEmbedding w q
    rw [hqimage] at h
    exact h
  have hchart := injective_area_formula_image_weighted
    (f := coareaCoordinatesAt f a)
    (f' := coareaCoordinatesFDerivAt f a) w ht
    (fun x _ => hasFDerivAt_coareaCoordinatesAt (hf.differentiable one_ne_zero) a x)
    ((regularCoareaChart hf a ha).injOn.mono ht_source)
  have hdim : Module.finrank ℝ E = Module.finrank ℝ W :=
    (coareaCoordinatesEquivAt f a ha).toLinearEquiv.finrank_eq
  have hchart' :
      ∫⁻ p in e '' t, w p =
        ∫⁻ x in t, ENNReal.ofReal (jacobian (coareaCoordinatesAt f a) x) *
          w (coareaCoordinatesAt f a x) ∂μHE[Module.finrank ℝ E] := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := W), ← hdim]
    change
      ∫⁻ p in coareaCoordinatesAt f a '' t, w p ∂μHE[Module.finrank ℝ E] = _
    exact hchart
  have hsource :
      ∫⁻ x in t, ENNReal.ofReal (jacobian (coareaCoordinatesAt f a) x) *
          w (coareaCoordinatesAt f a x) ∂μHE[Module.finrank ℝ E] =
        ∫⁻ x in t, g x * ENNReal.ofReal
          ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
            ∂μHE[Module.finrank ℝ E] := by
    apply setLIntegral_congr_fun ht
    intro x hxt
    have hxU := htU hxt
    have hxsource := hxU.1
    have hHx : H (coareaCoordinatesAt f a x) = x := by
      dsimp only [H]
      rw [← regularCoareaChart_apply hf a ha,
        regularCoareaChartInverse_eq_symm hf a ha
          ((regularCoareaChart hf a ha).map_source hxsource)]
      exact (regularCoareaChart hf a ha).left_inv hxsource
    change ENNReal.ofReal (jacobian (coareaCoordinatesAt f a) x) *
        w (coareaCoordinatesAt f a x) =
      g x * ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
    rw [jacobian_of_hasFDerivAt
      (hasFDerivAt_coareaCoordinatesAt (hf.differentiable one_ne_zero) a x)]
    change ENNReal.ofReal _ *
        (g (H (coareaCoordinatesAt f a x)) * ENNReal.ofReal _) = _
    rw [hHx]
    calc
      ENNReal.ofReal (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet *
          (g x * ENNReal.ofReal
            (regularCoareaFiberJacobian hf a ha (coareaCoordinatesAt f a x))) =
        g x *
          (ENNReal.ofReal
              (regularCoareaFiberJacobian hf a ha (coareaCoordinatesAt f a x)) *
            ENNReal.ofReal (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet) := by
              ac_rfl
      _ =
        g x * ENNReal.ofReal
          (regularCoareaFiberJacobian hf a ha (coareaCoordinatesAt f a x) *
            (coareaCoordinatesFDerivAt f a x).toLinearMap.normDet) := by
              have hfiber_nonneg : 0 ≤ regularCoareaFiberJacobian hf a ha
                  (coareaCoordinatesAt f a x) := by
                exact LinearMap.normDet_nonneg _
              rw [ENNReal.ofReal_mul hfiber_nonneg]
      _ = g x * ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.adjoint.normDet) := by
        rw [regularCoareaFiberJacobian_mul_chartJacobian hf a ha hxU]
  have hproduct : Measurable (q.indicator (fun p : F × K => w (WithLp.toLp 2 p))) :=
    (hw.comp (WithLp.prod_continuous_toLp 2 F K).measurable).indicator hq
  have hsection : Measurable (fun y : F =>
      ∫⁻ z in Prod.mk y ⁻¹' q, w (WithLp.toLp 2 (y, z))
        ∂μHE[Module.finrank ℝ K]) := by
    have hmeas := hproduct.lintegral_prod_right'
      (ν := (μHE[Module.finrank ℝ K] : Measure K))
    convert hmeas using 1
    funext y
    rw [← MeasureTheory.lintegral_indicator (hq.preimage measurable_prodMk_left)]
    rfl
  refine ⟨?_, houter.trans (htransport.trans (hchart'.trans hsource))⟩
  rw [show (fun y : F => ∫⁻ x in t ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ K]) =
    (fun y : F => ∫⁻ z in Prod.mk y ⁻¹' q, w (WithLp.toLp 2 (y, z))
      ∂μHE[Module.finrank ℝ K]) from funext hfiber]
  exact hsection

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem surjective_fderiv_of_mem_regularCoareaChartSource
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    {x : E} (hx : x ∈ regularCoareaChartSource hf a ha) :
    Function.Surjective (fderiv ℝ f x) := by
  have hinj : Function.Injective (coareaCoordinatesFDerivAt f a x) :=
    LinearMap.normDet_ne_zero_tfae
      (coareaCoordinatesFDerivAt f a x).toLinearMap |>.out 0 4 |>.mp hx.2
  have hdim := (coareaCoordinatesEquivAt f a ha).toLinearEquiv.finrank_eq
  have hbij : Function.Bijective (coareaCoordinatesFDerivAt f a x) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  intro y
  obtain ⟨v, hv⟩ := hbij.2 (WithLp.toLp 2 (y, 0))
  refine ⟨v, ?_⟩
  have := congrArg WithLp.fst hv
  simpa [coareaCoordinatesFDerivAt] using this

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem finrank_ker_eq_sub_of_surjective
    (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) :
    Module.finrank ℝ (LinearMap.ker L) =
      Module.finrank ℝ E - Module.finrank ℝ F := by
  have hrange : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ F := by
    rw [LinearMap.range_eq_top.mpr hL]
    simp
  have hrank := L.finrank_range_add_finrank_ker
  omega

private theorem regular_coarea_chart_formula_weighted_dim
    {f : E → F} (hf : ContDiff ℝ 1 f) (a : E)
    (ha : Function.Surjective (fderiv ℝ f a))
    {t : Set E} (ht : MeasurableSet t)
    (htU : t ⊆ regularCoareaChartSource hf a ha)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun y : F => ∫⁻ x in t ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) ∧
    ∫⁻ y : F, ∫⁻ x in t ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
        ∫⁻ x in t, g x * ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
          ∂μHE[Module.finrank ℝ E] := by
  have hdim := finrank_ker_eq_sub_of_surjective (fderiv ℝ f a).toLinearMap ha
  simpa only [hdim] using regular_coarea_chart_formula_weighted hf a ha ht htU g hg

private theorem regular_coarea_formula_weighted
    {f : E → F} (hf : ContDiff ℝ 1 f)
    {s : Set E} (hs : MeasurableSet s)
    (hsreg : ∀ x ∈ s, Function.Surjective (fderiv ℝ f x))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun y : F => ∫⁻ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) ∧
    ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
        ∫⁻ x in s, g x * ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
          ∂μHE[Module.finrank ℝ E] := by
  classical
  rcases eq_empty_or_nonempty s with rfl | hsne
  · simp
  let R := {x : E // Function.Surjective (fderiv ℝ f x)}
  let _ : Nonempty R := ⟨⟨hsne.choose, hsreg hsne.choose hsne.choose_spec⟩⟩
  let U : R → Set E := fun x => regularCoareaChartSource hf x x.2
  have hUopen : ∀ x, IsOpen (U x) := fun x => isOpen_regularCoareaChartSource hf x x.2
  have hsU : s ⊆ ⋃ x, U x := by
    intro x hxs
    exact mem_iUnion.2 ⟨⟨x, hsreg x hxs⟩, self_mem_regularCoareaChartSource hf x (hsreg x hxs)⟩
  obtain ⟨a, ha⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    U hUopen hsU
  let v : ℕ → Set E := fun n => s ∩ U (a n)
  let t : ℕ → Set E := disjointed v
  have hvmeas : ∀ n, MeasurableSet (v n) := fun n => hs.inter (hUopen (a n)).measurableSet
  have htmeas : ∀ n, MeasurableSet (t n) := fun n => MeasurableSet.disjointed hvmeas n
  have htdisj : Pairwise fun i j => Disjoint (t i) (t j) := disjoint_disjointed v
  have htU : ∀ n, t n ⊆ U (a n) := by
    intro n
    exact (disjointed_subset v n).trans inter_subset_right
  have htcover : ⋃ n, t n = s := by
    rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_left
    · intro x hxs
      obtain ⟨n, hxn⟩ := mem_iUnion.1 (ha hxs)
      exact mem_iUnion.2 ⟨n, hxs, hxn⟩
  have hlocal : ∀ n,
      Measurable (fun y : F => ∫⁻ x in t n ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) ∧
      ∫⁻ y : F, ∫⁻ x in t n ∩ f ⁻¹' {y}, g x
            ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
          ∫⁻ x in t n, g x * ENNReal.ofReal
            ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
              ∂μHE[Module.finrank ℝ E] := by
    intro n
    exact regular_coarea_chart_formula_weighted_dim hf (a n) (a n).2
      (htmeas n) (htU n) g hg
  have hpreimage_meas : ∀ y : F, MeasurableSet (f ⁻¹' {y}) := fun y =>
    (MeasurableSet.singleton y).preimage hf.continuous.measurable
  have hfiber_union : ∀ y : F,
      ∫⁻ x in s ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
        ∑' n, ∫⁻ x in t n ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] := by
    intro y
    rw [← htcover, iUnion_inter]
    exact MeasureTheory.lintegral_iUnion
      (fun n => (htmeas n).inter (hpreimage_meas y))
      (fun i j hij => (htdisj hij).mono inter_subset_left inter_subset_left) g
  refine ⟨?_, ?_⟩
  · rw [show (fun y : F => ∫⁻ x in s ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) =
      (fun y : F => ∑' n, ∫⁻ x in t n ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) from funext hfiber_union]
    exact Measurable.tsum fun n => (hlocal n).1
  · calc
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, g x
            ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
          ∫⁻ y : F, ∑' n, ∫⁻ x in t n ∩ f ⁻¹' {y}, g x
            ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] :=
        lintegral_congr hfiber_union
      _ = ∑' n, ∫⁻ y : F, ∫⁻ x in t n ∩ f ⁻¹' {y}, g x
            ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] :=
        MeasureTheory.lintegral_tsum fun n => (hlocal n).1.aemeasurable
      _ = ∑' n, ∫⁻ x in t n, g x * ENNReal.ofReal
            ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
              ∂μHE[Module.finrank ℝ E] := tsum_congr fun n => (hlocal n).2
      _ = ∫⁻ x in ⋃ n, t n, g x * ENNReal.ofReal
            ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
              ∂μHE[Module.finrank ℝ E] :=
        (MeasureTheory.lintegral_iUnion htmeas htdisj _).symm
      _ = ∫⁻ x in s, g x * ENNReal.ofReal
            ((fderiv ℝ f x).toLinearMap.adjoint.normDet)
              ∂μHE[Module.finrank ℝ E] := by rw [htcover]

private theorem coarea_formula_weighted_aux
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E)
    {s : Set E} (hs : MeasurableSet s) (g : E → ℝ≥0∞) (hg : Measurable g) :
    AEMeasurable (fun y : F => ∫⁻ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) volume ∧
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, g x
            ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
        ∫⁻ x in s, g x * ENNReal.ofReal (coareaJacobian f x)
          ∂μHE[Module.finrank ℝ E] := by
  classical
  let r : Set E := s ∩ {x | Function.Surjective (fderiv ℝ f x)}
  let c : Set E := s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)}
  have hcritclosed : IsClosed {x : E | ¬ Function.Surjective (fderiv ℝ f x)} :=
    isClosed_not_surjective_fderiv hf
  have hregmeas : MeasurableSet {x : E | Function.Surjective (fderiv ℝ f x)} := by
    rw [show {x : E | Function.Surjective (fderiv ℝ f x)} =
      {x : E | ¬ Function.Surjective (fderiv ℝ f x)}ᶜ by ext x; simp]
    exact hcritclosed.measurableSet.compl
  have hrmeas : MeasurableSet r := hs.inter hregmeas
  have hcmeas : MeasurableSet c := hs.inter hcritclosed.measurableSet
  have hsplit : s = r ∪ c := by
    ext x
    simp only [r, c, mem_union, mem_inter_iff, mem_ofPred_eq]
    tauto
  have hrcdisj : Disjoint r c := by
    apply Set.disjoint_left.2
    intro x hxr hxc
    exact hxc.2 hxr.2
  have hreg := regular_coarea_formula_weighted hf hrmeas
    (fun x hx => hx.2) g hg
  have hcritraw := critical_lintegral_hausdorffMeasure_fiber_eq_zero hf hEF
  have hcritraw_volume :
      ∫⁻ y : F, μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
          ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y}) = 0 := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using hcritraw.2
  have hrawzero : (fun y : F =>
      μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
        ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ f ⁻¹' {y})) =ᵐ[
          volume] 0 :=
    (lintegral_eq_zero_iff hcritraw.1).mp hcritraw_volume
  have hcritical_weighted : (fun y : F =>
      ∫⁻ x in c ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) =ᵐ[
          volume] 0 := by
    filter_upwards [hrawzero] with y hy
    have hraw : μH[(Module.finrank ℝ E - Module.finrank ℝ F : ℕ)]
        (c ∩ f ⁻¹' {y}) = 0 := by
      apply measure_mono_null _ hy
      intro x hx
      exact ⟨hx.1.2, hx.2⟩
    have hnormalized : μHE[Module.finrank ℝ E - Module.finrank ℝ F]
        (c ∩ f ⁻¹' {y}) = 0 := by
      rw [Measure.euclideanHausdorffMeasure_apply_eq_smul, hraw, mul_zero]
    have hrestrict : (μHE[Module.finrank ℝ E - Module.finrank ℝ F] : Measure E).restrict
        (c ∩ f ⁻¹' {y}) = 0 := Measure.restrict_eq_zero.mpr hnormalized
    rw [hrestrict]
    exact lintegral_zero_measure g
  have hfibersplit : ∀ y : F,
      s ∩ f ⁻¹' {y} = (r ∩ f ⁻¹' {y}) ∪ (c ∩ f ⁻¹' {y}) := by
    intro y
    exact (congrArg (fun u => u ∩ f ⁻¹' {y}) hsplit).trans
      (union_inter_distrib_right _ _ _)
  have htotal_eq : (fun y : F => ∫⁻ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) =ᵐ[
        volume]
      (fun y : F => ∫⁻ x in r ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) := by
    filter_upwards [hcritical_weighted] with y hy
    have hy' : ∫⁻ x in c ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] = 0 := by
      simpa only [Pi.zero_apply] using hy
    rw [hfibersplit y, lintegral_union
      (hcmeas.inter ((MeasurableSet.singleton y).preimage hf.continuous.measurable))
      (hrcdisj.mono inter_subset_left inter_subset_left), hy', add_zero]
  have hcritical_source : ∫⁻ x in c,
      g x * ENNReal.ofReal (coareaJacobian f x)
        ∂μHE[Module.finrank ℝ E] = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem hcmeas] with x hx
    have hzero : (fderiv ℝ f x).toLinearMap.adjoint.normDet = 0 :=
      (normDet_adjoint_eq_zero_iff_not_surjective
        (fderiv ℝ f x).toLinearMap).2 hx.2
    simp only [coareaJacobian, hzero, ENNReal.ofReal_zero, mul_zero, Pi.zero_apply]
  have hsourcerestrict :
      (∫⁻ x in s, g x * ENNReal.ofReal (coareaJacobian f x)
          ∂μHE[Module.finrank ℝ E]) =
        ∫⁻ x in r, g x * ENNReal.ofReal (coareaJacobian f x)
          ∂μHE[Module.finrank ℝ E] := by
    rw [hsplit, lintegral_union hcmeas hrcdisj, hcritical_source, add_zero]
  refine ⟨hreg.1.aemeasurable.congr htotal_eq.symm, ?_⟩
  calc
    (∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, g x
        ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) =
        ∫⁻ y : F, ∫⁻ x in r ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] :=
      lintegral_congr_ae htotal_eq
    _ = ∫⁻ x in r, g x * ENNReal.ofReal (coareaJacobian f x)
          ∂μHE[Module.finrank ℝ E] := by
      simpa only [coareaJacobian] using hreg.2
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (coareaJacobian f x)
          ∂μHE[Module.finrank ℝ E] := hsourcerestrict.symm

theorem aemeasurable_coarea_fiber_integral
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E)
    {s : Set E} (hs : MeasurableSet s) (g : E → ℝ≥0∞) (hg : Measurable g) :
    AEMeasurable (fun y : F => ∫⁻ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F]) volume :=
  (coarea_formula_weighted_aux hf hEF hs g hg).1

theorem coarea_formula_weighted
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E)
    {s : Set E} (hs : MeasurableSet s) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, g x
          ∂μHE[Module.finrank ℝ E - Module.finrank ℝ F] =
      ∫⁻ x in s, g x * ENNReal.ofReal (coareaJacobian f x)
        ∂μHE[Module.finrank ℝ E] :=
  (coarea_formula_weighted_aux hf hEF hs g hg).2

theorem coarea_formula
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E)
    {s : Set E} (hs : MeasurableSet s) :
    ∫⁻ y : F, μHE[Module.finrank ℝ E - Module.finrank ℝ F]
          (s ∩ f ⁻¹' {y}) =
      ∫⁻ x in s, ENNReal.ofReal (coareaJacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
  simpa using coarea_formula_weighted hf hEF hs (fun _ => (1 : ℝ≥0∞)) measurable_const

end LocalCoordinates

end Area
