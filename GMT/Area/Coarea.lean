import GMT.Area.Formula
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
    [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U]
    (L : U →ₗ[ℝ] V) :
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

end Area
