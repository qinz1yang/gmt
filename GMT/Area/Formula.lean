import GMT.Area.Jacobian
import GMT.Analysis.Lipschitz
import GMT.Measure.Hausdorff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Data.Set.Card.Arithmetic

noncomputable section

open Set
open MeasureTheory
open Filter
open scoped ENNReal MeasureTheory Function NNReal Topology

namespace Area

def multiplicity {E F : Type*} (f : E → F) (s : Set E) (y : F) : ℝ≥0∞ :=
  ENat.toENNReal (encard (s ∩ f ⁻¹' {y}))

def weightedMultiplicity {E F : Type*} (f : E → F) (s : Set E)
    (g : E → ℝ≥0∞) (y : F) : ℝ≥0∞ :=
  ∑' x, (s ∩ f ⁻¹' {y}).indicator g x

theorem weightedMultiplicity_one {E F : Type*} (f : E → F) (s : Set E) (y : F) :
    weightedMultiplicity f s (fun _ => 1) y = multiplicity f s y := by
  rw [weightedMultiplicity, ← tsum_subtype, ENNReal.tsum_set_one, multiplicity]

theorem weightedMultiplicity_comp {E F : Type*} (f : E → F) (s : Set E)
    (g : F → ℝ≥0∞) (y : F) :
    weightedMultiplicity f s (g ∘ f) y = multiplicity f s y * g y := by
  rw [weightedMultiplicity, ← tsum_subtype]
  calc
    (∑' x : ↑(s ∩ f ⁻¹' {y}), g (f x)) = ∑' _ : ↑(s ∩ f ⁻¹' {y}), g y := by
      apply tsum_congr
      intro x
      rw [show f x = y from x.2.2]
    _ = ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) * g y :=
      ENNReal.tsum_set_const (s ∩ f ⁻¹' {y}) (g y)
    _ = multiplicity f s y * g y := by rfl

theorem aemeasurable_multiplicity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : NullMeasurableSet s μH[(Module.finrank ℝ E : ℝ)])
    (hfin : μH[(Module.finrank ℝ E : ℝ)] s ≠ ∞) :
    AEMeasurable (multiplicity f s) μH[(Module.finrank ℝ E : ℝ)] := by
  change AEMeasurable
    (fun y => ENat.toENNReal (encard (s ∩ f ⁻¹' {y})))
    μH[(Module.finrank ℝ E : ℝ)]
  exact LipschitzOnWith.aemeasurable_encard_fiber hf
    (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity) hs hfin

theorem lintegral_multiplicity_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : NullMeasurableSet s μH[(Module.finrank ℝ E : ℝ)])
    (hfin : μH[(Module.finrank ℝ E : ℝ)] s ≠ ∞) :
    ∫⁻ y : F, multiplicity f s y ∂μH[(Module.finrank ℝ E : ℝ)] ≤
      (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) *
        μH[(Module.finrank ℝ E : ℝ)] s := by
  change (∫⁻ y : F, ENat.toENNReal (encard (s ∩ f ⁻¹' {y}))
      ∂μH[(Module.finrank ℝ E : ℝ)]) ≤
    (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * μH[(Module.finrank ℝ E : ℝ)] s
  exact LipschitzOnWith.lintegral_encard_fiber_le hf
    (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity) hs hfin

theorem multiplicity_eq_zero_of_not_mem_image {E F : Type*} {f : E → F} {s : Set E} {y : F}
    (hy : y ∉ f '' s) : multiplicity f s y = 0 := by
  have hset : s ∩ f ⁻¹' {y} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
      iff_false]
    rintro ⟨hxs, hxy⟩
    exact hy ⟨x, hxs, hxy⟩
  rw [multiplicity, hset, Set.encard_empty, ENat.toENNReal_zero]

theorem multiplicity_eq_one_of_injOn {E F : Type*} {f : E → F} {s : Set E} (hf : InjOn f s)
    {y : F} (hy : y ∈ f '' s) : multiplicity f s y = 1 := by
  obtain ⟨x, hxs, rfl⟩ := hy
  have hset : s ∩ f ⁻¹' {f x} = {x} := by
    ext z
    constructor
    · rintro ⟨hzs, hzf⟩
      have : z = x := hf hzs hxs (by simpa only [mem_preimage, mem_singleton_iff] using hzf)
      simp [this]
    · intro hz
      simp only [mem_singleton_iff] at hz
      subst hz
      exact ⟨hxs, rfl⟩
  rw [multiplicity, hset, encard_eq_one.mpr ⟨x, rfl⟩, ENat.toENNReal_one]

theorem mul_le_euclideanHausdorffMeasure_image_of_lt_normDet
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (A : E →L[ℝ] F) {c : ℝ≥0}
    (hc : (c : ℝ≥0∞) < ENNReal.ofReal A.toLinearMap.normDet) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → F),
        ApproximatesLinearOn f A s δ →
          (c : ℝ≥0∞) * μHE[Module.finrank ℝ E] s ≤
            μHE[Module.finrank ℝ E] (f '' s) := by
  have hAnormDet : A.toLinearMap.normDet ≠ 0 := by
    intro hA
    simp [hA] at hc
  have hAker : A.ker = ⊥ :=
    LinearMap.normDet_ne_zero_tfae A.toLinearMap |>.out 0 1 |>.mp hAnormDet
  have hAinj : Function.Injective A := LinearMap.ker_eq_bot.mp hAker
  let V : Submodule ℝ F := LinearMap.range A.toLinearMap
  let P : F →L[ℝ] V := V.orthogonalProjectionOnto
  have hdim : Module.finrank ℝ E = Module.finrank ℝ V := by
    simpa [V] using (LinearMap.finrank_range_of_inj hAinj).symm
  let e : V ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ E) (finCongr hdim.symm)
  let AR : E →L[ℝ] V := A.rangeRestrict
  let B : E →L[ℝ] E := e.toContinuousLinearMap.comp AR
  have hBnormDet : B.toLinearMap.normDet = A.toLinearMap.normDet := by
    change (e.toLinearIsometry.toLinearMap ∘ₗ AR.toLinearMap).normDet = _
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ hdim]
    simp [AR, e.toLinearIsometry.normDet_eq_one]
  have hBdet : |B.det| = A.toLinearMap.normDet := by
    rw [← LinearMap.normDet_eq_abs_det, hBnormDet]
  have hcB : (c : ℝ≥0∞) < ENNReal.ofReal |B.det| := by
    simpa [hBdet] using hc
  have H := MeasureTheory.mul_le_addHaar_image_of_lt_det
    (volume : Measure E) B hcB
  filter_upwards [H] with δ hδ
  intro s f hf
  let g : E → E := fun x => e (P (f x))
  have hPA : P.comp A = AR := by
    ext x
    exact V.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
  have hg : ApproximatesLinearOn g B s δ := by
    intro x hx y hy
    calc
      ‖g x - g y - B (x - y)‖ =
          ‖P (f x - f y - A (x - y))‖ := by
            rw [← e.norm_map]
            simp only [map_sub, g, B, ContinuousLinearMap.comp_apply]
            rw [← hPA]
            rfl
      _ ≤ ‖f x - f y - A (x - y)‖ :=
        V.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ δ * ‖x - y‖ := hf x hx y hy
  have hsame : (c : ℝ≥0∞) * μHE[Module.finrank ℝ E] s ≤
      μHE[Module.finrank ℝ E] (g '' s) := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact hδ s g hg
  have himage : g '' s = e '' (P '' (f '' s)) := by
    simp only [g, image_image]
  have hiso : μHE[Module.finrank ℝ E] (g '' s) =
      μHE[Module.finrank ℝ E] (P '' (f '' s)) := by
    rw [himage]
    exact e.isometry.euclideanHausdorffMeasure_image _
  have hproj : μHE[Module.finrank ℝ E] (P '' (f '' s)) ≤
      μHE[Module.finrank ℝ E] (f '' s) := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
      Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    gcongr
    simpa [P] using hausdorffMeasure_orthogonalProjectionOnto_le V
      (Module.finrank ℝ E) (f '' s)
      (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity)
  exact hsame.trans (hiso.le.trans hproj)

private theorem euclideanHausdorffMeasure_image_le_mul_of_normDet_lt_of_injective
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (A : E →L[ℝ] F) (hAinj : Function.Injective A) {c : ℝ≥0}
    (hc : ENNReal.ofReal A.toLinearMap.normDet < (c : ℝ≥0∞)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → F),
        ApproximatesLinearOn f A s δ →
          μHE[Module.finrank ℝ E] (f '' s) ≤
            (c : ℝ≥0∞) * μHE[Module.finrank ℝ E] s := by
  by_cases hE : Subsingleton E
  · have hdim : Module.finrank ℝ E = 0 := Module.finrank_zero_of_subsingleton
    have hc1 : (1 : ℝ≥0∞) ≤ c := by
      have hnorm : A.toLinearMap.normDet = 1 := by
        have hAz : A.toLinearMap = 0 := Subsingleton.elim _ _
        simp [hAz]
      simpa [hnorm] using hc.le
    filter_upwards
    intro δ s f hf
    have hLip : LipschitzOnWith 1 f s := by
      intro x hx y hy
      simp [Subsingleton.elim x y]
    rw [hdim, Measure.euclideanHausdorffMeasure_zero,
      Measure.euclideanHausdorffMeasure_zero]
    calc
      μH[0] (f '' s) ≤ (1 : ℝ≥0∞) ^ (0 : ℝ) * μH[0] s :=
        hLip.hausdorffMeasure_image_le le_rfl
      _ = μH[0] s := by simp
      _ ≤ (c : ℝ≥0∞) * μH[0] s := by
        simpa only [one_mul] using
          (mul_le_mul (a := (1 : ℝ≥0∞)) (b := (c : ℝ≥0∞))
            (c := μH[0] s) (d := μH[0] s) hc1 le_rfl bot_le bot_le)
  · have hAnormDet : A.toLinearMap.normDet ≠ 0 :=
      LinearMap.normDet_ne_zero_tfae A.toLinearMap |>.out 1 0 |>.mp
        (LinearMap.ker_eq_bot.mpr hAinj)
    let V : Submodule ℝ F := LinearMap.range A.toLinearMap
    let P : F →L[ℝ] V := V.orthogonalProjectionOnto
    have hdim : Module.finrank ℝ E = Module.finrank ℝ V := by
      simpa [V] using (LinearMap.finrank_range_of_inj hAinj).symm
    let e : V ≃ₗᵢ[ℝ] E :=
      (stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ E) (finCongr hdim.symm)
    let AR : E →L[ℝ] V := A.rangeRestrict
    let B : E →L[ℝ] E := e.toContinuousLinearMap.comp AR
    have hBnormDet : B.toLinearMap.normDet = A.toLinearMap.normDet := by
      change (e.toLinearIsometry.toLinearMap ∘ₗ AR.toLinearMap).normDet = _
      rw [LinearMap.normDet_comp_of_finrank_eq _ _ hdim]
      simp [AR, e.toLinearIsometry.normDet_eq_one]
    have hBdet : |B.det| = A.toLinearMap.normDet := by
      rw [← LinearMap.normDet_eq_abs_det, hBnormDet]
    have hBdetne : B.det ≠ 0 := by
      intro h
      apply hAnormDet
      rw [← hBdet, h, abs_zero]
    let b : E ≃L[ℝ] E := B.toContinuousLinearEquivOfDetNeZero hBdetne
    have hb : (b : E →L[ℝ] E) = B := rfl
    let N : ℝ≥0 := ‖(b.symm : E →L[ℝ] E)‖₊
    have hN : 0 < N := b.subsingleton_or_nnnorm_symm_pos.resolve_left hE
    have hNinv : N⁻¹ ≠ 0 := inv_ne_zero hN.ne'
    have hcNN : Real.toNNReal A.toLinearMap.normDet < c := by
      simpa [ENNReal.ofReal] using hc
    obtain ⟨q, hAq, hqc⟩ : ∃ q : ℝ≥0,
        Real.toNNReal A.toLinearMap.normDet < q ∧ q < c := exists_between hcNN
    have hAq' : ENNReal.ofReal |B.det| < (q : ℝ≥0∞) := by
      simpa [hBdet, ENNReal.ofReal] using hAq
    have Hmeasure := MeasureTheory.addHaar_image_le_mul_of_det_lt
      (volume : Measure E) B hAq'
    let K : ℝ≥0 → ℝ≥0 := fun δ => 1 + 2 * δ * (N⁻¹ - δ)⁻¹
    have hK : Tendsto K (𝓝 0) (𝓝 1) := by
      have hsub : ContinuousAt (fun δ : ℝ≥0 => N⁻¹ - δ) 0 :=
        continuousAt_const.sub continuousAt_id
      have hinv : ContinuousAt (fun δ : ℝ≥0 => (N⁻¹ - δ)⁻¹) 0 :=
        hsub.inv₀ (by simpa using hNinv)
      have hcont : ContinuousAt (fun δ : ℝ≥0 => 1 + 2 * δ * (N⁻¹ - δ)⁻¹) 0 :=
        continuousAt_const.add ((continuousAt_const.mul continuousAt_id).mul hinv)
      simpa [K] using hcont.tendsto
    have hfactor : Tendsto
        (fun δ : ℝ≥0 => ((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) * q)
        (𝓝 0) (𝓝 q) := by
      have hKcoe : Tendsto (fun δ : ℝ≥0 => (K δ : ℝ≥0∞)) (𝓝 0) (𝓝 1) :=
        ENNReal.continuous_coe.tendsto 1 |>.comp hK
      have hp : Tendsto
          (fun z : ℝ≥0∞ => z ^ (Module.finrank ℝ E : ℝ)) (𝓝 1) (𝓝 1) := by
        simpa using
          (ENNReal.continuous_rpow_const
            (y := (Module.finrank ℝ E : ℝ))).tendsto (1 : ℝ≥0∞)
      simpa using ENNReal.Tendsto.mul_const (hp.comp hKcoe)
        (Or.inr ENNReal.coe_ne_top)
    have Hfactor : ∀ᶠ δ : ℝ≥0 in 𝓝 0,
        ((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) * q ≤ c :=
      ((tendsto_order.1 hfactor).2 (c : ℝ≥0∞) (by exact_mod_cast hqc)).mono
        fun _ h => h.le
    have Hsmall : Iio N⁻¹ ∈ 𝓝 (0 : ℝ≥0) := Iio_mem_nhds hNinv.bot_lt
    have Hsmall' : Iio N⁻¹ ∈ 𝓝[>] (0 : ℝ≥0) := nhdsWithin_le_nhds Hsmall
    have Hfactor' : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0,
        ((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) * q ≤ c :=
      Hfactor.filter_mono nhdsWithin_le_nhds
    filter_upwards [Hmeasure, Hfactor', Hsmall'] with δ hmeasure hfactorδ hδ
    intro s f hf
    let h : E → E := fun x => e (P (f x))
    have hPA : P.comp A = AR := by
      ext x
      exact V.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
    have hh : ApproximatesLinearOn h B s δ := by
      intro x hx y hy
      calc
        ‖h x - h y - B (x - y)‖ =
            ‖P (f x - f y - A (x - y))‖ := by
              rw [← e.norm_map]
              simp only [map_sub, h, B, ContinuousLinearMap.comp_apply]
              rw [← hPA]
              rfl
        _ ≤ ‖f x - f y - A (x - y)‖ :=
          V.norm_orthogonalProjectionOnto_apply_le _
        _ ≤ δ * ‖x - y‖ := hf x hx y hy
    have hh' : ApproximatesLinearOn h (b : E →L[ℝ] E) s δ := by
      simpa [hb] using hh
    have hδ' : δ < N⁻¹ := by simpa using hδ
    have hhinj : InjOn h s := hh'.injOn (Or.inr hδ')
    let inv : E → E := Function.invFunOn h s
    let φ : E → F := fun z => f (inv z)
    have hinv : ∀ x ∈ s, inv (h x) = x := hhinj.leftInvOn_invFunOn
    have hφ : LipschitzOnWith (K δ) φ (h '' s) := by
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro z hz w hw
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨y, hy, rfl⟩ := hw
      rw [show φ (h x) = f x by simp [φ, hinv x hx],
        show φ (h y) = f y by simp [φ, hinv y hy]]
      have hxy : ‖x - y‖ ≤ ((N⁻¹ - δ)⁻¹ : ℝ≥0) * ‖h x - h y‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact (hh'.antilipschitz (Or.inr hδ')).le_mul_dist ⟨x, hx⟩ ⟨y, hy⟩
      have hAB : ‖A (x - y)‖ = ‖B (x - y)‖ := by
        change ‖A (x - y)‖ = ‖e (AR (x - y))‖
        rw [e.norm_map]
        rfl
      calc
        ‖f x - f y‖ ≤ ‖A (x - y)‖ + ‖f x - f y - A (x - y)‖ := by
          nth_rw 1 [show f x - f y = A (x - y) + (f x - f y - A (x - y)) by abel]
          exact norm_add_le _ _
        _ ≤ ‖B (x - y)‖ + δ * ‖x - y‖ := by
          rw [hAB]
          exact add_le_add le_rfl (hf x hx y hy)
        _ ≤ (‖h x - h y‖ + δ * ‖x - y‖) + δ * ‖x - y‖ := by
          have hBbound : ‖B (x - y)‖ ≤ ‖h x - h y‖ + δ * ‖x - y‖ := by
            nth_rw 1 [show B (x - y) =
              h x - h y - (h x - h y - B (x - y)) by abel]
            calc
              ‖h x - h y - (h x - h y - B (x - y))‖ ≤
                  ‖h x - h y‖ + ‖h x - h y - B (x - y)‖ := norm_sub_le _ _
              _ ≤ ‖h x - h y‖ + δ * ‖x - y‖ :=
                add_le_add le_rfl (hh x hx y hy)
          exact add_le_add hBbound le_rfl
        _ ≤ (K δ : ℝ≥0) * ‖h x - h y‖ := by
          rw [show K δ = 1 + 2 * δ * (N⁻¹ - δ)⁻¹ by rfl]
          push_cast
          calc
            (‖h x - h y‖ + δ * ‖x - y‖) + δ * ‖x - y‖ =
                ‖h x - h y‖ + 2 * δ * ‖x - y‖ := by ring
            _ ≤ ‖h x - h y‖ + 2 * δ *
                (((N⁻¹ - δ)⁻¹ : ℝ≥0) * ‖h x - h y‖) := by gcongr
            _ = (1 + 2 * δ * (N⁻¹ - δ)⁻¹) * ‖h x - h y‖ := by
              push_cast
              ring
    have himage : f '' s = φ '' (h '' s) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨h x, ⟨x, hx, rfl⟩, by simp [φ, hinv x hx]⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, by simp [φ, hinv x hx]⟩
    have hφmeasure : μHE[Module.finrank ℝ E] (f '' s) ≤
        ((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
          μHE[Module.finrank ℝ E] (h '' s) := by
      rw [himage, Measure.euclideanHausdorffMeasure_apply_eq_smul,
        Measure.euclideanHausdorffMeasure_apply_eq_smul]
      calc
        _ ≤ Measure.addHaarScalarFactor
              (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
              μH[Module.finrank ℝ E] *
            (((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
              μH[(Module.finrank ℝ E : ℝ)] (h '' s)) := by
          gcongr
          exact hφ.hausdorffMeasure_image_le
            (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity)
        _ = _ := by ring
    have hhmeasure : μHE[Module.finrank ℝ E] (h '' s) ≤
        (q : ℝ≥0∞) * μHE[Module.finrank ℝ E] s := by
      rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact hmeasure s h hh
    calc
      μHE[Module.finrank ℝ E] (f '' s) ≤
          ((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
            μHE[Module.finrank ℝ E] (h '' s) := hφmeasure
      _ ≤ ((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
            ((q : ℝ≥0∞) * μHE[Module.finrank ℝ E] s) := by gcongr
      _ = (((K δ : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) * q) *
            μHE[Module.finrank ℝ E] s := by ring
      _ ≤ (c : ℝ≥0∞) * μHE[Module.finrank ℝ E] s := by gcongr

theorem euclideanHausdorffMeasure_image_le_mul_of_normDet_lt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (A : E →L[ℝ] F) {c : ℝ≥0}
    (hc : ENNReal.ofReal A.toLinearMap.normDet < (c : ℝ≥0∞)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → F),
        ApproximatesLinearOn f A s δ →
          μHE[Module.finrank ℝ E] (f '' s) ≤
            (c : ℝ≥0∞) * μHE[Module.finrank ℝ E] s := by
  by_cases hAinj : Function.Injective A
  · exact euclideanHausdorffMeasure_image_le_mul_of_normDet_lt_of_injective
      A hAinj hc
  · have hAnormDet : A.toLinearMap.normDet = 0 := by
      rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot]
      intro hker
      exact hAinj (LinearMap.ker_eq_bot.mp hker)
    let i : F × E →L[ℝ] WithLp 2 (F × E) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F E).symm
    let aug : ℝ≥0 → E →L[ℝ] WithLp 2 (F × E) := fun η =>
      i.comp (A.prod ((η : ℝ) • ContinuousLinearMap.id ℝ E))
    have haug : Continuous aug := by
      dsimp [aug]
      apply Continuous.const_clm_comp
      change Continuous (fun η : ℝ≥0 => (ContinuousLinearMap.prodₗᵢ ℝ)
        (A, (η : ℝ) • ContinuousLinearMap.id ℝ E))
      exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
        (continuous_const.prodMk (NNReal.continuous_coe.smul continuous_const))
    have hnormaug : Continuous (fun η =>
        ENNReal.ofReal (aug η).toLinearMap.normDet) :=
      ENNReal.continuous_ofReal.comp
        (ContinuousLinearMap.continuous_normDet.comp haug)
    have haug0inj : ¬Function.Injective (aug 0) := by
      intro h
      apply hAinj
      intro x y hxy
      apply sub_eq_zero.mp
      apply h
      simp [aug, i, hxy]
    have haug0 : (aug 0).toLinearMap.normDet = 0 := by
      rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot]
      intro hker
      exact haug0inj (LinearMap.ker_eq_bot.mp hker)
    have hc0 : (0 : ℝ≥0∞) < c := by simpa [hAnormDet] using hc
    have Haug : ∀ᶠ η : ℝ≥0 in 𝓝 0,
        ENNReal.ofReal (aug η).toLinearMap.normDet < c :=
      hnormaug.continuousAt.eventually_lt continuousAt_const (by
        simpa [haug0] using hc0)
    have Haug' : ∀ᶠ η : ℝ≥0 in 𝓝[>] 0,
        ENNReal.ofReal (aug η).toLinearMap.normDet < c :=
      Haug.filter_mono nhdsWithin_le_nhds
    obtain ⟨η, hηc, hηpos⟩ := (Haug'.and self_mem_nhdsWithin).exists
    have hη : (0 : ℝ≥0) < η := by simpa using hηpos
    have hauginj : Function.Injective (aug η) := by
      intro x y hxy
      have hsnd := congrArg (fun z : WithLp 2 (F × E) => z.snd) hxy
      have hηreal : (0 : ℝ) < η := by exact_mod_cast hη
      simpa [aug, i, hηreal.ne'] using hsnd
    have H := euclideanHausdorffMeasure_image_le_mul_of_normDet_lt_of_injective
      (aug η) hauginj hηc
    filter_upwards [H] with δ hδ
    intro s f hf
    let faug : E → WithLp 2 (F × E) := fun x => WithLp.toLp 2 (f x, (η : ℝ) • x)
    have hfaug : ApproximatesLinearOn faug (aug η) s δ := by
      intro x hx y hy
      simpa [faug, aug, i, map_sub, ← WithLp.toLp_sub] using hf x hx y hy
    have hmain : μHE[Module.finrank ℝ E] (faug '' s) ≤
        (c : ℝ≥0∞) * μHE[Module.finrank ℝ E] s := hδ s faug hfaug
    have hfst : LipschitzWith 1 (fun z : WithLp 2 (F × E) => z.fst) := by
      intro x y
      simpa only [ENNReal.coe_one, one_mul] using WithLp.edist_fst_le x y
    have himage : (fun z : WithLp 2 (F × E) => z.fst) '' (faug '' s) = f '' s := by
      simp [faug, image_image]
    have hproj : μHE[Module.finrank ℝ E] (f '' s) ≤
        μHE[Module.finrank ℝ E] (faug '' s) := by
      rw [← himage, Measure.euclideanHausdorffMeasure_apply_eq_smul,
        Measure.euclideanHausdorffMeasure_apply_eq_smul]
      gcongr
      simpa using hfst.hausdorffMeasure_image_le
        (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity) (faug '' s)
    exact hproj.trans hmain

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}

private theorem image_le_lintegral_normDet_aux1
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {ε : ℝ≥0} (εpos : 0 < ε) :
    μHE[Module.finrank ℝ E] (f '' s) ≤
      (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E]) +
        2 * ε * μHE[Module.finrank ℝ E] s := by
  have hlocal :
      ∀ A : E →L[ℝ] F,
        ∃ δ : ℝ≥0,
          0 < δ ∧
            (∀ B : E →L[ℝ] F, ‖B - A‖ ≤ δ →
              |B.toLinearMap.normDet - A.toLinearMap.normDet| ≤ ε) ∧
              ∀ (t : Set E) (g : E → F), ApproximatesLinearOn g A t δ →
                μHE[Module.finrank ℝ E] (g '' t) ≤
                  (ENNReal.ofReal A.toLinearMap.normDet + ε) *
                    μHE[Module.finrank ℝ E] t := by
    intro A
    let c : ℝ≥0 := Real.toNNReal A.toLinearMap.normDet + ε
    have hc : ENNReal.ofReal A.toLinearMap.normDet < (c : ℝ≥0∞) := by
      simp only [c, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((euclideanHausdorffMeasure_image_le_mul_of_normDet_lt A hc).and
      self_mem_nhdsWithin).exists with ⟨δ, hδ, δpos⟩
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ δ' : ℝ, 0 < δ' ∧
        ∀ B : E →L[ℝ] F, dist B A < δ' →
          dist B.toLinearMap.normDet A.toLinearMap.normDet < ε := by
      refine Metric.continuousAt_iff.1
        ContinuousLinearMap.continuous_normDet.continuousAt ε εpos
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      calc
        ‖B - A‖ ≤ (min δ δ'' : ℝ≥0) := hB
        _ ≤ δ'' := by simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
        _ < δ' := half_lt_self δ'pos
    · intro t g htg
      exact hδ t g (htg.mono_num (min_le_left _ _))
  choose δ hδ using hlocal
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      fun A => (hδ A).1.ne'
  calc
    μHE[Module.finrank ℝ E] (f '' s) ≤
        μHE[Module.finrank ℝ E] (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact Set.image_mono (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μHE[Module.finrank ℝ E] (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ENNReal.ofReal (A n).toLinearMap.normDet + ε) *
        μHE[Module.finrank ℝ E] (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      exact (hδ (A n)).2.2 _ _ (ht n)
    _ = ∑' n, ∫⁻ _ in s ∩ t n,
        ENNReal.ofReal (A n).toLinearMap.normDet + ε
        ∂μHE[Module.finrank ℝ E] := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
    _ ≤ ∑' n, ∫⁻ x in s ∩ t n,
        ENNReal.ofReal ((f' x).toLinearMap.normDet) + 2 * ε
        ∂μHE[Module.finrank ℝ E] := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).ae_norm_fderiv_sub_le
          (μHE[Module.finrank ℝ E] : Measure E) (hs.inter (t_meas n)) f'
          fun x hx => (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have hnorm : (A n).toLinearMap.normDet ≤
          (f' x).toLinearMap.normDet + ε := by
        calc
          (A n).toLinearMap.normDet ≤ (f' x).toLinearMap.normDet +
              |(f' x).toLinearMap.normDet - (A n).toLinearMap.normDet| := by
            linarith [neg_le_abs ((f' x).toLinearMap.normDet -
              (A n).toLinearMap.normDet)]
          _ ≤ (f' x).toLinearMap.normDet + ε :=
            add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal (A n).toLinearMap.normDet + ε ≤
            ENNReal.ofReal ((f' x).toLinearMap.normDet + ε) + ε := by gcongr
        _ = ENNReal.ofReal ((f' x).toLinearMap.normDet) + 2 * ε := by
          simp only [ENNReal.ofReal_add, LinearMap.normDet_nonneg, two_mul, add_assoc,
            NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ x in ⋃ n, s ∩ t n,
        ENNReal.ofReal ((f' x).toLinearMap.normDet) + 2 * ε
        ∂μHE[Module.finrank ℝ E] := by
      have hmeas : ∀ n : ℕ, MeasurableSet (s ∩ t n) := fun n => hs.inter (t_meas n)
      rw [lintegral_iUnion hmeas]
      exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ = ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet) + 2 * ε
        ∂μHE[Module.finrank ℝ E] := by
      rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
    _ = (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E]) +
        2 * ε * μHE[Module.finrank ℝ E] s := by
      simp only [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]

private theorem image_le_lintegral_normDet_aux2
    (hs : MeasurableSet s) (hfin : μHE[Module.finrank ℝ E] s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μHE[Module.finrank ℝ E] (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E] := by
  have hlim : Tendsto
      (fun ε : ℝ≥0 =>
        (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
          ∂μHE[Module.finrank ℝ E]) +
          2 * ε * μHE[Module.finrank ℝ E] s)
      (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
          ∂μHE[Module.finrank ℝ E]) +
          2 * (0 : ℝ≥0) * μHE[Module.finrank ℝ E] s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hfin)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id)
      (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact image_le_lintegral_normDet_aux1 hs hf' εpos

private theorem image_le_lintegral_normDet
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μHE[Module.finrank ℝ E] (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E] := by
  let u n := disjointed (spanningSets (μHE[Module.finrank ℝ E] : Measure E)) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets (μHE[Module.finrank ℝ E] : Measure E) i
  have hs_union : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    μHE[Module.finrank ℝ E] (f '' s) ≤
        ∑' n, μHE[Module.finrank ℝ E] (f '' (s ∩ u n)) := by
      conv_lhs => rw [hs_union, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in s ∩ u n,
        ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E] := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply image_le_lintegral_normDet_aux2 (hs.inter (u_meas n)) _
        fun x hx => (hf' x hx.1).mono inter_subset_left
      have hlt : μHE[Module.finrank ℝ E] (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
          (measure_spanningSets_lt_top (μHE[Module.finrank ℝ E] : Measure E) n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) hlt)
    _ = ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E] := by
      conv_rhs => rw [hs_union]
      rw [lintegral_iUnion]
      · intro n
        exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right

private theorem lintegral_normDet_le_image_aux1
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfinj : InjOn f s) {ε : ℝ≥0} (εpos : 0 < ε) :
    (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
      ∂μHE[Module.finrank ℝ E]) ≤
      μHE[Module.finrank ℝ E] (f '' s) +
        2 * ε * μHE[Module.finrank ℝ E] s := by
  have hlocal :
      ∀ A : E →L[ℝ] F,
        ∃ δ : ℝ≥0,
          0 < δ ∧
            (∀ B : E →L[ℝ] F, ‖B - A‖ ≤ δ →
              |B.toLinearMap.normDet - A.toLinearMap.normDet| ≤ ε) ∧
              ∀ (t : Set E) (g : E → F), ApproximatesLinearOn g A t δ →
                ENNReal.ofReal A.toLinearMap.normDet * μHE[Module.finrank ℝ E] t ≤
                  μHE[Module.finrank ℝ E] (g '' t) +
                    ε * μHE[Module.finrank ℝ E] t := by
    intro A
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ δ' : ℝ, 0 < δ' ∧
        ∀ B : E →L[ℝ] F, dist B A < δ' →
          dist B.toLinearMap.normDet A.toLinearMap.normDet < ε := by
      refine Metric.continuousAt_iff.1
        ContinuousLinearMap.continuous_normDet.continuousAt ε εpos
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    have hcont : ∀ B : E →L[ℝ] F, ‖B - A‖ ≤ δ'' →
        |B.toLinearMap.normDet - A.toLinearMap.normDet| ≤ ε := by
      intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      exact hB.trans_lt (half_lt_self δ'pos)
    rcases eq_or_ne A.toLinearMap.normDet 0 with hA | hA
    · refine ⟨δ'', half_pos δ'pos, hcont, ?_⟩
      simp only [hA, forall_const, zero_mul, ENNReal.ofReal_zero, imp_true_iff, zero_le]
    let c : ℝ≥0 := Real.toNNReal A.toLinearMap.normDet - ε
    have hApos : 0 < A.toLinearMap.normDet :=
      lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm hA)
    have hc : (c : ℝ≥0∞) < ENNReal.ofReal A.toLinearMap.normDet := by
      simp only [c, ENNReal.ofReal, ENNReal.coe_sub]
      apply ENNReal.sub_lt_self ENNReal.coe_ne_top
      · simpa only [ENNReal.coe_eq_zero, Ne] using
          (ne_of_gt (Real.toNNReal_pos.mpr hApos))
      · simp only [εpos.ne', ENNReal.coe_eq_zero, Ne, not_false_iff]
    rcases ((mul_le_euclideanHausdorffMeasure_image_of_lt_normDet A hc).and
      self_mem_nhdsWithin).exists with ⟨δ, hδ, δpos⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      apply hcont B (hB.trans _)
      simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
    · intro t g htg
      rcases eq_or_ne (μHE[Module.finrank ℝ E] t) ∞ with htop | htop
      · simp only [htop, εpos.ne', ENNReal.mul_top, ENNReal.coe_eq_zero, le_top,
          Ne, not_false_iff, _root_.add_top]
      have hmain := hδ t g (htg.mono_num (min_le_left _ _))
      rwa [ENNReal.coe_sub, ENNReal.sub_mul, tsub_le_iff_right] at hmain
      simp only [htop, imp_true_iff, Ne, not_false_iff]
  choose δ hδ using hlocal
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      fun A => (hδ A).1.ne'
  have hs_union : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
  calc
    (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E]) =
        ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal ((f' x).toLinearMap.normDet)
          ∂μHE[Module.finrank ℝ E] := by
      conv_lhs => rw [hs_union]
      rw [lintegral_iUnion]
      · exact fun n => hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ ≤ ∑' n, ∫⁻ _ in s ∩ t n,
        ENNReal.ofReal (A n).toLinearMap.normDet + ε
        ∂μHE[Module.finrank ℝ E] := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).ae_norm_fderiv_sub_le
          (μHE[Module.finrank ℝ E] : Measure E) (hs.inter (t_meas n)) f'
          fun x hx => (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have hnorm : (f' x).toLinearMap.normDet ≤
          (A n).toLinearMap.normDet + ε := by
        calc
          (f' x).toLinearMap.normDet ≤ (A n).toLinearMap.normDet +
              |(f' x).toLinearMap.normDet - (A n).toLinearMap.normDet| := by
            linarith [le_abs_self ((f' x).toLinearMap.normDet -
              (A n).toLinearMap.normDet)]
          _ ≤ (A n).toLinearMap.normDet + ε :=
            add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal ((f' x).toLinearMap.normDet) ≤
            ENNReal.ofReal ((A n).toLinearMap.normDet + ε) :=
          ENNReal.ofReal_le_ofReal hnorm
        _ = ENNReal.ofReal (A n).toLinearMap.normDet + ε := by
          simp only [ENNReal.ofReal_add, LinearMap.normDet_nonneg, NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    _ = ∑' n, (ENNReal.ofReal (A n).toLinearMap.normDet *
        μHE[Module.finrank ℝ E] (s ∩ t n) +
          ε * μHE[Module.finrank ℝ E] (s ∩ t n)) := by
      simp only [setLIntegral_const, lintegral_add_right _ measurable_const]
    _ ≤ ∑' n, (μHE[Module.finrank ℝ E] (f '' (s ∩ t n)) +
        ε * μHE[Module.finrank ℝ E] (s ∩ t n) +
          ε * μHE[Module.finrank ℝ E] (s ∩ t n)) := by
      gcongr
      exact (hδ (A _)).2.2 _ _ (ht _)
    _ = μHE[Module.finrank ℝ E] (f '' s) +
        2 * ε * μHE[Module.finrank ℝ E] s := by
      conv_rhs => rw [hs_union]
      rw [image_iUnion, measure_iUnion]
      rotate_left
      · intro i j hij
        apply Disjoint.image _ hfinj inter_subset_left inter_subset_left
        exact Disjoint.mono inter_subset_right inter_subset_right (t_disj hij)
      · intro i
        have hcont : ContinuousOn f (s ∩ t i) := fun x hx =>
          (hf' x hx.1).differentiableWithinAt.mono inter_subset_left |>.continuousWithinAt
        exact (hs.inter (t_meas i)).image_of_continuousOn_injOn hcont
          (hfinj.mono inter_subset_left)
      rw [measure_iUnion]
      rotate_left
      · exact pairwise_disjoint_mono t_disj fun i => inter_subset_right
      · exact fun i => hs.inter (t_meas i)
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      congr 1
      ext1 i
      rw [mul_assoc, two_mul, add_assoc]

private theorem lintegral_normDet_le_image_aux2
    (hs : MeasurableSet s) (hfin : μHE[Module.finrank ℝ E] s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfinj : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
      ∂μHE[Module.finrank ℝ E]) ≤
      μHE[Module.finrank ℝ E] (f '' s) := by
  have hlim : Tendsto
      (fun ε : ℝ≥0 => μHE[Module.finrank ℝ E] (f '' s) +
        2 * ε * μHE[Module.finrank ℝ E] s)
      (𝓝[>] 0)
      (𝓝 (μHE[Module.finrank ℝ E] (f '' s) +
        2 * (0 : ℝ≥0) * μHE[Module.finrank ℝ E] s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hfin)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id)
      (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact lintegral_normDet_le_image_aux1 hs hf' hfinj εpos

private theorem lintegral_normDet_le_image
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfinj : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
      ∂μHE[Module.finrank ℝ E]) ≤
      μHE[Module.finrank ℝ E] (f '' s) := by
  let u n := disjointed (spanningSets (μHE[Module.finrank ℝ E] : Measure E)) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets (μHE[Module.finrank ℝ E] : Measure E) i
  have hs_union : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    (∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E]) =
        ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal ((f' x).toLinearMap.normDet)
          ∂μHE[Module.finrank ℝ E] := by
      conv_lhs => rw [hs_union]
      rw [lintegral_iUnion]
      · intro n
        exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
    _ ≤ ∑' n, μHE[Module.finrank ℝ E] (f '' (s ∩ u n)) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_normDet_le_image_aux2 (hs.inter (u_meas n)) _
        (fun x hx => (hf' x hx.1).mono inter_subset_left)
        (hfinj.mono inter_subset_left)
      have hlt : μHE[Module.finrank ℝ E] (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
          (measure_spanningSets_lt_top (μHE[Module.finrank ℝ E] : Measure E) n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) hlt)
    _ = μHE[Module.finrank ℝ E] (f '' s) := by
      conv_rhs => rw [hs_union, image_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        apply Disjoint.image _ hfinj inter_subset_left inter_subset_left
        exact Disjoint.mono inter_subset_right inter_subset_right
          (disjoint_disjointed _ hij)
      · intro i
        have hcont : ContinuousOn f (s ∩ u i) := fun x hx =>
          (hf' x hx.1).differentiableWithinAt.mono inter_subset_left |>.continuousWithinAt
        exact (hs.inter (u_meas i)).image_of_continuousOn_injOn hcont
          (hfinj.mono inter_subset_left)

theorem injective_area_formula
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfinj : InjOn f s) :
    μHE[Module.finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E] :=
  le_antisymm (image_le_lintegral_normDet hs hf')
    (lintegral_normDet_le_image hs hf' hfinj)

theorem injective_area_formula_of_hasFDerivAt
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hfinj : InjOn f s) :
    μHE[Module.finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
  rw [injective_area_formula hs (fun x hx => (hf' x hx).hasFDerivWithinAt) hfinj]
  apply setLIntegral_congr_fun hs
  intro x hx
  change ENNReal.ofReal ((f' x).toLinearMap.normDet) = ENNReal.ofReal (jacobian f x)
  rw [jacobian_of_hasFDerivAt (hf' x hx)]

private theorem restrict_map_withDensity_jacobian
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hfinj : InjOn f s) :
    Measure.map (s.domRestrict f)
        (Measure.comap ((↑) : s → E)
          ((μHE[Module.finrank ℝ E] : Measure E).withDensity
            fun x => ENNReal.ofReal (jacobian f x))) =
      (μHE[Module.finrank ℝ E] : Measure F).restrict (f '' s) := by
  have hfcont : ContinuousOn f s := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hφ : MeasurableEmbedding (s.domRestrict f) :=
    hfcont.measurableEmbedding hs hfinj
  apply Measure.ext
  intro t ht
  let r : Set E := s ∩ f ⁻¹' t
  have hpre : MeasurableSet ((s.domRestrict f) ⁻¹' t) := hφ.measurable ht
  have hrange : ((↑) : s → E) '' ((s.domRestrict f) ⁻¹' t) = r := by
    ext x
    simp [r, and_comm]
  have hr : MeasurableSet r := by
    rw [← hrange]
    exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image' hpre
  have himage : f '' r = t ∩ f '' s := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
      exact ⟨hxt, ⟨x, hxs, rfl⟩⟩
    · rintro ⟨hyt, x, hxs, rfl⟩
      exact ⟨x, ⟨hxs, hyt⟩, rfl⟩
  rw [hφ.map_apply _ t]
  rw [(MeasurableEmbedding.subtype_coe hs).comap_apply]
  rw [hrange, withDensity_apply _ hr]
  rw [Measure.restrict_apply ht, ← himage]
  rw [injective_area_formula_of_hasFDerivAt hr
    (fun x hx => hf' x hx.1) (hfinj.mono inter_subset_left)]

theorem injective_area_formula_image_weighted
    (g : F → ℝ≥0∞) (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hfinj : InjOn f s) :
    ∫⁻ y in f '' s, g y ∂μHE[Module.finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x)
        ∂μHE[Module.finrank ℝ E] := by
  have hfcont : ContinuousOn f s := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hφ : MeasurableEmbedding (s.domRestrict f) :=
    hfcont.measurableEmbedding hs hfinj
  rw [← restrict_map_withDensity_jacobian hs hf' hfinj, hφ.lintegral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map,
    map_comap_subtype_coe hs,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀
      (μHE[Module.finrank ℝ E] : Measure E)
      (measurable_jacobian f |>.ennreal_ofReal.aemeasurable.restrict) (g ∘ f) hs]
  · rfl
  · filter_upwards [] with x
    exact ENNReal.ofReal_lt_top

omit [FiniteDimensional ℝ F] in
private theorem exists_measurable_weightedMultiplicity_eq_indicator
    (g : E → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hfinj : InjOn f s) (hg : Measurable g) :
    ∃ h : F → ℝ≥0∞, Measurable h ∧
      (∀ y, weightedMultiplicity f s g y = (f '' s).indicator h y) ∧
      ∀ x ∈ s, h (f x) = g x := by
  classical
  rcases eq_empty_or_nonempty s with rfl | hsne
  · exact ⟨0, measurable_const, by simp [weightedMultiplicity], by simp⟩
  let _ : Nonempty s := hsne.coe_sort
  let φ : s → F := s.domRestrict f
  have hfcont : ContinuousOn f s := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hφ : MeasurableEmbedding φ := hfcont.measurableEmbedding hs hfinj
  let h : F → ℝ≥0∞ := fun y => g (hφ.invFun y)
  have hh : Measurable h :=
    hg.comp (measurable_subtype_coe.comp hφ.measurable_invFun)
  refine ⟨h, hh, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ f '' s
    · obtain ⟨x, hxs, rfl⟩ := hy
      have hfiber : s ∩ f ⁻¹' {f x} = {x} := by
        ext z
        constructor
        · rintro ⟨hzs, hzf⟩
          exact mem_singleton_iff.mpr (hfinj hzs hxs (by simpa using hzf))
        · intro hz
          rw [mem_singleton_iff] at hz
          subst z
          exact ⟨hxs, by simp⟩
      rw [weightedMultiplicity, hfiber]
      simp only [Set.indicator_singleton, tsum_pi_single]
      rw [Set.indicator_of_mem (mem_image_of_mem f hxs)]
      change g x = g (hφ.invFun (f x))
      rw [show f x = φ ⟨x, hxs⟩ by rfl, hφ.leftInverse_invFun]
    · have hfiber : s ∩ f ⁻¹' {y} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false]
        rintro ⟨hxs, hxy⟩
        exact hy ⟨x, hxs, hxy⟩
      rw [weightedMultiplicity, hfiber]
      simp [Set.indicator, hy]
  · intro x hx
    change g (hφ.invFun (f x)) = g x
    rw [show f x = φ ⟨x, hx⟩ by rfl, hφ.leftInverse_invFun]

theorem injective_area_formula_weighted
    (g : E → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hfinj : InjOn f s) (hg : Measurable g) :
    ∫⁻ y : F, weightedMultiplicity f s g y ∂μHE[Module.finrank ℝ E] =
      ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
  classical
  obtain ⟨h, hh, hpoint, hgf⟩ :=
    exists_measurable_weightedMultiplicity_eq_indicator g hs hf' hfinj hg
  calc
    ∫⁻ y, weightedMultiplicity f s g y ∂μHE[Module.finrank ℝ E] =
        ∫⁻ y, (f '' s).indicator h y ∂μHE[Module.finrank ℝ E] :=
      lintegral_congr hpoint
    _ = ∫⁻ y in f '' s, h y ∂μHE[Module.finrank ℝ E] :=
      MeasureTheory.lintegral_indicator
      (hs.image_of_continuousOn_injOn
        (fun x hx => (hf' x hx).continuousAt.continuousWithinAt) hfinj) h
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * h (f x)
        ∂μHE[Module.finrank ℝ E] :=
      injective_area_formula_image_weighted h hs hf' hfinj
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change ENNReal.ofReal (jacobian f x) * h (f x) =
        g x * ENNReal.ofReal (jacobian f x)
      rw [hgf x hx, mul_comm]

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem injective_area_formula_image_weighted_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} {K : ℝ≥0} (g : E → ℝ≥0∞)
    (hs : MeasurableSet s) (hf : LipschitzWith K f) (hfinj : InjOn f s) :
    ∫⁻ y in f '' s, g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  let t : Set E := s ∩ {x | DifferentiableAt ℝ f x}
  have ht : MeasurableSet t := hs.inter (measurableSet_of_differentiableAt ℝ f)
  have hst : s =ᵐ[volume] t := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [show s \ t = s \ {x | DifferentiableAt ℝ f x} by
        ext x
        simp [t]]
      apply measure_mono_null (t := {x | ¬DifferentiableAt ℝ f x}) (by
        intro x hx
        exact hx.2)
      exact (ae_iff.mp hf.ae_differentiableAt)
    · rw [sdiff_eq_empty.mpr inter_subset_left]
      simp
  have hnull : volume (f '' (s \ t)) = 0 := by
    have hsourceHE : (μHE[Module.finrank ℝ E] : Measure E) (s \ t) = 0 := by
      rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact measure_mono_null (t := {x | ¬DifferentiableAt ℝ f x}) (by
        intro x hx
        change ¬DifferentiableAt ℝ f x
        intro hdx
        exact hx.2 ⟨hx.1, hdx⟩)
        (ae_iff.mp hf.ae_differentiableAt)
    have hsourceH : μH[(Module.finrank ℝ E : ℝ)] (s \ t) = 0 := by
      have hsourceHE' := hsourceHE
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
        smul_eq_mul] at hsourceHE'
      exact (mul_eq_zero.mp hsourceHE').resolve_left (by
        simpa using
          (MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero
            (Module.finrank ℝ E)))
    have himageH : μH[(Module.finrank ℝ E : ℝ)] (f '' (s \ t)) = 0 := by
      apply le_antisymm
      · calc
          μH[(Module.finrank ℝ E : ℝ)] (f '' (s \ t)) ≤
              (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) *
                μH[(Module.finrank ℝ E : ℝ)] (s \ t) :=
            hf.hausdorffMeasure_image_le (by positivity) _
          _ = 0 := by rw [hsourceH, mul_zero]
      · exact bot_le
    have himageHE : (μHE[Module.finrank ℝ E] : Measure E) (f '' (s \ t)) = 0 := by
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
        smul_eq_mul, himageH, mul_zero]
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at himageHE
    exact himageHE
  have himage : f '' s =ᵐ[volume] f '' t := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · apply measure_mono_null
        (show f '' s \ f '' t ⊆ f '' (s \ t) by
          rintro y ⟨⟨x, hxs, rfl⟩, hy⟩
          refine ⟨x, ⟨hxs, ?_⟩, rfl⟩
          intro hxt
          exact hy ⟨x, hxt, rfl⟩)
      exact hnull
    · rw [sdiff_eq_empty.mpr (image_mono inter_subset_left)]
      simp
  have himage_restrict : volume.restrict (f '' s) = volume.restrict (f '' t) :=
    Measure.restrict_congr_set himage
  have hsource_restrict : volume.restrict s = volume.restrict t :=
    Measure.restrict_congr_set hst
  have hmain := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure E) ht
    (fun x hx => (show DifferentiableAt ℝ f x from hx.2).hasFDerivAt.hasFDerivWithinAt)
    (hfinj.mono inter_subset_left) g
  calc
    ∫⁻ y in f '' s, g y = ∫⁻ y in f '' t, g y := by
      rw [himage_restrict]
    _ = ∫⁻ x in t, ENNReal.ofReal (jacobian f x) * g (f x) := by
      calc
        ∫⁻ y in f '' t, g y = ∫⁻ x in t,
            ENNReal.ofReal |(fderiv ℝ f x).det| * g (f x) := hmain
        _ = ∫⁻ x in t, ENNReal.ofReal (jacobian f x) * g (f x) := by
          apply setLIntegral_congr_fun ht
          intro x hx
          change ENNReal.ofReal |(fderiv ℝ f x).det| * g (f x) =
            ENNReal.ofReal (jacobian f x) * g (f x)
          rw [jacobian, (show DifferentiableAt ℝ f x from hx.2).hasFDerivAt.fderiv]
          simp [LinearMap.normDet_eq_abs_det]
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [hsource_restrict]

theorem injective_area_formula_weighted_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} {K : ℝ≥0} (g : E → ℝ≥0∞)
    (hs : MeasurableSet s) (hf : LipschitzWith K f) (hfinj : InjOn f s)
    (hg : Measurable g) :
    ∫⁻ y, weightedMultiplicity f s g y =
      ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) := by
  let t : Set E := s ∩ {x | DifferentiableAt ℝ f x}
  have ht : MeasurableSet t := hs.inter (measurableSet_of_differentiableAt ℝ f)
  have hst : s =ᵐ[volume] t := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [show s \ t = s \ {x | DifferentiableAt ℝ f x} by
        ext x
        simp [t]]
      apply measure_mono_null (t := {x | ¬DifferentiableAt ℝ f x}) (by
        intro x hx
        exact hx.2)
      exact ae_iff.mp hf.ae_differentiableAt
    · rw [sdiff_eq_empty.mpr inter_subset_left]
      simp
  have hnull : volume (f '' (s \ t)) = 0 := by
    have hsourceHE : (μHE[Module.finrank ℝ E] : Measure E) (s \ t) = 0 := by
      rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact measure_mono_null (t := {x | ¬DifferentiableAt ℝ f x}) (by
        intro x hx
        change ¬DifferentiableAt ℝ f x
        intro hdx
        exact hx.2 ⟨hx.1, hdx⟩)
        (ae_iff.mp hf.ae_differentiableAt)
    have hsourceH : μH[(Module.finrank ℝ E : ℝ)] (s \ t) = 0 := by
      have hsourceHE' := hsourceHE
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
        smul_eq_mul] at hsourceHE'
      exact (mul_eq_zero.mp hsourceHE').resolve_left (by
        simpa using
          (MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero
            (Module.finrank ℝ E)))
    have himageH : μH[(Module.finrank ℝ E : ℝ)] (f '' (s \ t)) = 0 := by
      apply le_antisymm
      · calc
          μH[(Module.finrank ℝ E : ℝ)] (f '' (s \ t)) ≤
              (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) *
                μH[(Module.finrank ℝ E : ℝ)] (s \ t) :=
            hf.hausdorffMeasure_image_le (by positivity) _
          _ = 0 := by rw [hsourceH, mul_zero]
      · exact bot_le
    have himageHE : (μHE[Module.finrank ℝ E] : Measure E) (f '' (s \ t)) = 0 := by
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
        smul_eq_mul, himageH, mul_zero]
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at himageHE
    exact himageHE
  have hformula : ∫⁻ y, weightedMultiplicity f t g y =
      ∫⁻ x in t, g x * ENNReal.ofReal (jacobian f x) :=
    by
      simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
        injective_area_formula_weighted g ht
          (fun x hx => (show DifferentiableAt ℝ f x from hx.2).hasFDerivAt)
          (hfinj.mono inter_subset_left) hg
  have hleft : ∫⁻ y, weightedMultiplicity f s g y =
      ∫⁻ y, weightedMultiplicity f t g y := by
    apply lintegral_congr_ae
    have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' (s \ t) := by
      apply ae_iff.mpr
      have hset : {a : E | ¬ a ∉ f '' (s \ t)} = f '' (s \ t) := by
        ext a
        simp only [mem_ofPred_eq, not_not]
      rw [hset]
      exact hnull
    filter_upwards [hae] with y hy
    have hset : s ∩ f ⁻¹' {y} = t ∩ f ⁻¹' {y} := by
      ext x
      constructor
      · rintro ⟨hxs, hxy⟩
        by_cases hxt : x ∈ t
        · exact ⟨hxt, hxy⟩
        · exfalso
          apply hy
          exact ⟨x, ⟨hxs, hxt⟩, hxy⟩
      · rintro ⟨hxt, hxy⟩
        exact ⟨hxt.1, hxy⟩
    rw [weightedMultiplicity, weightedMultiplicity, hset]
  have hsource_restrict : volume.restrict s = volume.restrict t :=
    Measure.restrict_congr_set hst
  calc
    ∫⁻ y, weightedMultiplicity f s g y =
        ∫⁻ y, weightedMultiplicity f t g y := hleft
    _ = ∫⁻ x in t, g x * ENNReal.ofReal (jacobian f x) := hformula
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) := by
      rw [hsource_restrict]

theorem injective_area_formula_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} {K : ℝ≥0}
    (hs : MeasurableSet s) (hf : LipschitzWith K f) (hfinj : InjOn f s) :
    μHE[Module.finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) := by
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  simpa only [MeasureTheory.setLIntegral_one, mul_one] using
    (injective_area_formula_image_weighted_lipschitz (f := f) (s := s)
      (fun _ => (1 : ℝ≥0∞)) hs hf hfinj)

theorem monotone_area_formula_real
    {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s) :
    ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf g

theorem monotone_area_formula_real_unweighted
    {f f' : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s) :
    volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal (f' x) := by
  exact (MeasureTheory.lintegral_deriv_eq_volume_image_of_monotoneOn hs hf' hf).symm

theorem antitone_area_formula_real
    {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s) :
    ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (-f' x) * g (f x) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hf' hf g

theorem antitone_area_formula_real_unweighted
    {f f' : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s) :
    volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal (-f' x) := by
  exact (MeasureTheory.lintegral_deriv_eq_volume_image_of_antitoneOn hs hf' hf).symm

theorem monotone_area_formula_real_with_multiplicity
    {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s) :
    ∫⁻ y : ℝ, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) := by
  let bad : Set ℝ := {c | ∃ x y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c}
  have hbad : bad.Countable := hf.countable_setOfPred_two_preimages
  have hbad_ae : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ∉ bad := by
    apply ae_iff.mpr
    simpa [bad] using hbad.measure_zero (volume : Measure ℝ)
  have hpoint : ∀ y, y ∉ bad →
      multiplicity f s y * g y = (f '' s).indicator g y := by
    intro y hybad
    by_cases hy : y ∈ f '' s
    · have hyimage : y ∈ f '' s := hy
      obtain ⟨x, hxs, hxy⟩ := hy
      have hset : s ∩ f ⁻¹' {y} = {x} := by
        ext z
        constructor
        · rintro ⟨hzs, hzf⟩
          have hzy : f z = y := by simpa using hzf
          by_cases hzx : z = x
          · simp [hzx]
          · rcases lt_or_gt_of_ne hzx with hzx | hzx
            · exfalso
              apply hybad
              exact ⟨z, x, hzs, hxs, hzx, hzy, hxy⟩
            · exfalso
              apply hybad
              exact ⟨x, z, hxs, hzs, hzx, hxy, hzy⟩
        · intro hz
          simp only [mem_singleton_iff] at hz
          subst hz
          exact ⟨hxs, by simp [hxy]⟩
      rw [multiplicity, hset, encard_eq_one.mpr ⟨x, rfl⟩, ENat.toENNReal_one]
      simp [Set.indicator, hyimage]
    · have hyimage : y ∉ f '' s := hy
      rw [multiplicity_eq_zero_of_not_mem_image hyimage]
      simp [Set.indicator, hyimage]
  calc
    ∫⁻ y : ℝ, multiplicity f s y * g y =
        ∫⁻ y : ℝ, (f '' s).indicator g y :=
      lintegral_congr_ae (hbad_ae.mono fun y hy => hpoint y hy)
    _ = ∫⁻ y in f '' s, g y :=
      MeasureTheory.lintegral_indicator (hs.image_of_monotoneOn hf) g
    _ = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) :=
      MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf g

theorem area_formula_of_finite_injective_partition_image_weighted
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (n : ℕ)
    (t : Fin n → Set E) (g : E → ℝ≥0∞)
    (hpart : (⋃ i, t i) = s) (ht : ∀ i, MeasurableSet (t i))
    (hdisj : ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (t i) (t j))
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i : Fin n, InjOn f (t i))
    (hg : Measurable g) :
    ∫⁻ y, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  classical
  have hmult : ∀ y, multiplicity f s y = ∑ i, multiplicity f (t i) y := by
    intro y
    simp only [multiplicity, ← hpart]
    rw [Set.iUnion_inter]
    have hpair : Pairwise (Function.onFun Disjoint (fun i : Fin n => t i ∩ f ⁻¹' {y})) := by
      intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    rw [Set.encard_iUnion_of_finite hpair]
    rw [← finsum_mem_univ,
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite (Set.univ : Set (Fin n)))]
    let u : Finset (Fin n) := Finset.univ
    have hsum (q : Fin n → ℕ∞) : ENat.toENNReal (∑ i ∈ u, q i) =
        ∑ i ∈ u, ENat.toENNReal (q i) := by
      induction u using Finset.induction_on with
      | empty => simp
      | @insert a u ha ih => simp [Finset.sum_insert, ha, ENat.toENNReal_add, ih]
    simpa [u] using hsum (fun i => (t i ∩ f ⁻¹' {y}).encard)
  have hsubset : ∀ (i : Fin n) x, x ∈ t i → x ∈ s := by
    intro i x hx
    rw [← hpart]
    exact mem_iUnion.2 ⟨i, hx⟩
  have himage : ∀ i : Fin n, MeasurableSet (f '' t i) := by
    intro i
    exact MeasureTheory.measurable_image_of_fderivWithin (ht i)
      (fun x hx => (hf' x (hsubset i x hx)).hasFDerivWithinAt) (hfinj i)
  have hpiece : ∀ i : Fin n, ∫⁻ y, multiplicity f (t i) y * g y =
      ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    calc
      ∫⁻ y, multiplicity f (t i) y * g y = ∫⁻ y, (f '' t i).indicator g y :=
        lintegral_congr (fun y => hpoint y)
      _ = ∫⁻ y in f '' t i, g y := MeasureTheory.lintegral_indicator (himage i) g
      _ = ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) :=
        by
          simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
            injective_area_formula_image_weighted g (ht i)
              (fun x hx => hf' x (hsubset i x hx)) (hfinj i)
  have hmeas : ∀ i : Fin n, Measurable (fun y => multiplicity f (t i) y * g y) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    rw [show (fun y => multiplicity f (t i) y * g y) = (f '' t i).indicator g by
      funext y; exact hpoint y]
    exact hg.indicator (himage i)
  calc
    ∫⁻ y, multiplicity f s y * g y =
        ∫⁻ y, (∑ i, multiplicity f (t i) y) * g y :=
      lintegral_congr (fun y => by rw [hmult y])
    _ = ∫⁻ y, ∑ i, multiplicity f (t i) y * g y := by
      apply lintegral_congr
      intro y
      rw [Finset.sum_mul]
    _ = ∑ i, ∫⁻ y, multiplicity f (t i) y * g y := by
      simpa using MeasureTheory.lintegral_finsetSum (μ := (volume : Measure E))
        (Finset.univ : Finset (Fin n)) (fun i _ => hmeas i)
    _ = ∑ i, ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpiece i
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [← hpart, Measure.restrict_iUnion hdisj ht, MeasureTheory.lintegral_sum_measure]
      simp [tsum_fintype]

private lemma countable_multiplicity
    {E F : Type*} {f : E → F} {t : ℕ → Set E}
    (hdisj : Pairwise (Disjoint on t))
    (hfinj : ∀ i, InjOn f (t i)) (y : F) :
    multiplicity f (⋃ i, t i) y = ∑' i, multiplicity f (t i) y := by
  let u : ℕ → Set E := fun i => t i ∩ f ⁻¹' {y}
  let I : Set ℕ := {i | (u i).Nonempty}
  have hdisju : Pairwise (Disjoint on u) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  have hterm : ∀ i, multiplicity f (t i) y = I.indicator (fun _ => (1 : ℝ≥0∞)) i := by
    intro i
    by_cases hi : i ∈ I
    · have hne : (u i).Nonempty := hi
      obtain ⟨x, hx⟩ := hne
      have hset : u i = {x} := by
        ext z
        constructor
        · intro hz
          exact Set.mem_singleton_iff.mpr ((hfinj i) hz.1 hx.1 (by
            calc f z = y := hz.2
            _ = f x := hx.2.symm))
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          exact hx
      rw [multiplicity, show t i ∩ f ⁻¹' {y} = u i from rfl, hset,
        encard_eq_one.mpr ⟨x, rfl⟩, ENat.toENNReal_one]
      simp [Set.indicator, hi]
    · have hempty : u i = ∅ := not_nonempty_iff_eq_empty.mp hi
      rw [multiplicity, show t i ∩ f ⁻¹' {y} = u i from rfl, hempty, Set.encard_empty,
        ENat.toENNReal_zero]
      simp [Set.indicator, hi]
  have htsum : (∑' i, multiplicity f (t i) y) = I.encard := by
    rw [show (fun i => multiplicity f (t i) y) = I.indicator (fun _ => (1 : ℝ≥0∞)) by
      funext i; exact hterm i]
    rw [← tsum_subtype I (fun _ : ℕ => (1 : ℝ≥0∞)), ENNReal.tsum_set_one]
  have hunion : (⋃ i, u i).encard = I.encard := by
    obtain hfin | hinf := I.finite_or_infinite
    · have finiteI : Finite I := hfin.fintype.finite
      let v : I → Set E := fun i => u i.1
      have hvdisj : Pairwise (Disjoint on v) := by
        intro i j hij
        apply hdisju
        intro h
        apply hij
        exact Subtype.ext h
      have henc := Set.encard_iUnion_of_finite hvdisj
      have hEq : (⋃ i : I, v i) = ⋃ i : ℕ, u i := by
        ext z
        constructor
        · intro hz
          obtain ⟨i, hz⟩ := mem_iUnion.1 hz
          exact mem_iUnion.2 ⟨i.1, hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := mem_iUnion.1 hz
          by_cases hIi : i ∈ I
          · exact mem_iUnion.2 ⟨⟨i, hIi⟩, hi⟩
          · change ¬ (u i).Nonempty at hIi
            exact False.elim (hIi ⟨z, hi⟩)
      have hvcard : ∀ i : I, (v i).encard = 1 := by
        intro i
        apply encard_eq_one.mpr
        refine ⟨i.2.choose, ?_⟩
        ext z
        constructor
        · intro hz
          apply Set.mem_singleton_iff.mpr
          apply (hfinj i.1) hz.1 i.2.choose_spec.1
          calc f z = y := hz.2
            _ = f i.2.choose := i.2.choose_spec.2.symm
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          exact i.2.choose_spec
      rw [← hEq, henc]
      simp_rw [hvcard]
      let e : (↑hfin.toFinset) ≃ I :=
        { toFun := fun i => ⟨i, hfin.mem_toFinset.mp i.2⟩
          invFun := fun i => ⟨i, hfin.mem_toFinset.mpr i.2⟩
          left_inv := by intro i; rfl
          right_inv := by intro i; rfl }
      let J : Finset I := hfin.toFinset.attach.map e.toEmbedding
      have hsupport : Function.support (fun _ : I => (1 : ℕ∞)) ⊆ J := by
        intro i hi
        apply Finset.mem_map.mpr
        refine ⟨e.symm i, Finset.mem_attach _ _, ?_⟩
        simp [e]
      rw [finsum_eq_sum_of_support_subset (fun _ : I => (1 : ℕ∞)) (s := J) hsupport]
      rw [Finset.sum_const, show J.card = hfin.toFinset.card by simp [J]]
      have hcard : I.encard = (hfin.toFinset.card : ℕ∞) := by
        change ENat.card I = (hfin.toFinset.card : ℕ∞)
        rw [@ENat.card_eq_coe_natCard I finiteI, Nat.card_coe_set_eq,
          Set.ncard_eq_toFinset_card I hfin]
      calc
        hfin.toFinset.card • (1 : ℕ∞) = (hfin.toFinset.card : ℕ∞) := by
          rw [nsmul_eq_mul, mul_one]
        _ = I.encard := hcard.symm
    · have hIinf : Infinite I := infinite_coe_iff.mpr hinf
      let fset : I → Set E := fun i => u i.1
      have hfset_inj : Function.Injective fset := by
        intro i j hij
        by_contra hne
        have hd : Disjoint (u i.1) (u j.1) := by
          apply hdisju
          intro h
          apply hne
          exact Subtype.ext h
        obtain ⟨x, hx⟩ := j.2
        apply hd.le_bot
        exact ⟨by
          change x ∈ fset i
          rw [hij]
          exact hx, hx⟩
      have huinf : (⋃ i : I, fset i).Infinite := Set.infinite_iUnion hfset_inj
      have hEq : (⋃ i : I, fset i) = ⋃ i : ℕ, u i := by
        ext z
        constructor
        · intro hz
          obtain ⟨i, hz⟩ := mem_iUnion.1 hz
          exact mem_iUnion.2 ⟨i.1, hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := mem_iUnion.1 hz
          have hIi : i ∈ I := ⟨z, hi⟩
          exact mem_iUnion.2 ⟨⟨i, hIi⟩, hi⟩
      rw [← hEq, encard_eq_top huinf, encard_eq_top hinf]
  rw [multiplicity, show (⋃ i, t i) ∩ f ⁻¹' {y} = ⋃ i, u i by
    ext z
    simp [u], hunion, htsum]

theorem area_formula_of_countable_injective_partition_image_weighted
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (t : ℕ → Set E)
    (g : E → ℝ≥0∞) (hpart : (⋃ i, t i) = s) (ht : ∀ i, MeasurableSet (t i))
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (t i) (t j))
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i : ℕ, InjOn f (t i))
    (hg : Measurable g) :
    ∫⁻ y, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  classical
  have hsubset : ∀ i x, x ∈ t i → x ∈ s := by
    intro i x hx
    rw [← hpart]
    exact mem_iUnion.2 ⟨i, hx⟩
  have himage : ∀ i : ℕ, MeasurableSet (f '' t i) := by
    intro i
    exact MeasureTheory.measurable_image_of_fderivWithin (ht i)
      (fun x hx => (hf' x (hsubset i x hx)).hasFDerivWithinAt) (hfinj i)
  have hpiece : ∀ i : ℕ, ∫⁻ y, multiplicity f (t i) y * g y =
      ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    calc
      ∫⁻ y, multiplicity f (t i) y * g y = ∫⁻ y, (f '' t i).indicator g y :=
        lintegral_congr (fun y => hpoint y)
      _ = ∫⁻ y in f '' t i, g y := MeasureTheory.lintegral_indicator (himage i) g
      _ = ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) :=
        by
          simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
            injective_area_formula_image_weighted g (ht i)
              (fun x hx => hf' x (hsubset i x hx)) (hfinj i)
  have hmeas : ∀ i : ℕ, AEMeasurable (fun y => multiplicity f (t i) y * g y)
      (volume : Measure E) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    rw [show (fun y => multiplicity f (t i) y * g y) = (f '' t i).indicator g by
      funext y; exact hpoint y]
    exact (hg.indicator (himage i)).aemeasurable
  have hmult : ∀ y, multiplicity f s y = ∑' i, multiplicity f (t i) y := by
    intro y
    rw [← hpart]
    exact countable_multiplicity hdisj hfinj y
  calc
    ∫⁻ y, multiplicity f s y * g y =
        ∫⁻ y, (∑' i, multiplicity f (t i) y) * g y :=
      lintegral_congr (fun y => by rw [hmult y])
    _ = ∫⁻ y, ∑' i, multiplicity f (t i) y * g y := by
      apply lintegral_congr
      intro y
      rw [ENNReal.tsum_mul_right]
    _ = ∑' i, ∫⁻ y, multiplicity f (t i) y * g y :=
      MeasureTheory.lintegral_tsum hmeas
    _ = ∑' i, ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
      apply tsum_congr
      intro i
      exact hpiece i
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [← hpart, MeasureTheory.lintegral_iUnion ht hdisj]

private theorem countable_weightedMultiplicity
    {E F : Type*} {f : E → F} {t : ℕ → Set E} (g : E → ℝ≥0∞)
    (hdisj : Pairwise (Disjoint on t)) (y : F) :
    weightedMultiplicity f (⋃ i, t i) g y =
      ∑' i, weightedMultiplicity f (t i) g y := by
  classical
  rw [weightedMultiplicity]
  calc
    (∑' x, ((⋃ i, t i) ∩ f ⁻¹' {y}).indicator g x) =
        ∑' x, ∑' i, (t i ∩ f ⁻¹' {y}).indicator g x := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ (⋃ i, t i) ∩ f ⁻¹' {y}
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.1
        rw [tsum_eq_single i]
        · rw [Set.indicator_of_mem (show x ∈ t i ∩ f ⁻¹' {y} from ⟨hxi, hx.2⟩)]
        · intro j hji
          rw [Set.indicator_of_notMem]
          intro hxj
          exact Set.disjoint_left.mp (hdisj hji) hxj.1 hxi
      · rw [Set.indicator_of_notMem hx]
        rw [show (fun i => (t i ∩ f ⁻¹' {y}).indicator g x) =
            (fun _ : ℕ => (0 : ℝ≥0∞)) by
          funext i
          apply Set.indicator_of_notMem
          intro hxi
          exact hx ⟨mem_iUnion.mpr ⟨i, hxi.1⟩, hxi.2⟩]
        exact tsum_zero.symm
    _ = ∑' i, ∑' x, (t i ∩ f ⁻¹' {y}).indicator g x := ENNReal.tsum_comm
    _ = ∑' i, weightedMultiplicity f (t i) g y := by rfl

theorem area_formula_of_countable_injective_partition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (t : ℕ → Set E)
    (g : E → ℝ≥0∞) (hpart : (⋃ i, t i) = s) (ht : ∀ i, MeasurableSet (t i))
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (t i) (t j))
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i : ℕ, InjOn f (t i))
    (hg : Measurable g) :
    ∫⁻ y, weightedMultiplicity f s g y =
      ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) := by
  classical
  have hsubset : ∀ i x, x ∈ t i → x ∈ s := by
    intro i x hx
    rw [← hpart]
    exact mem_iUnion.2 ⟨i, hx⟩
  have hpiece : ∀ i, ∫⁻ y, weightedMultiplicity f (t i) g y =
      ∫⁻ x in t i, g x * ENNReal.ofReal (jacobian f x) := by
    intro i
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
      injective_area_formula_weighted g (ht i)
        (fun x hx => hf' x (hsubset i x hx)) (hfinj i) hg
  have hmeas : ∀ i, AEMeasurable (weightedMultiplicity f (t i) g)
      (volume : Measure E) := by
    intro i
    obtain ⟨h, hh, hpoint, _⟩ :=
      exists_measurable_weightedMultiplicity_eq_indicator g (ht i)
        (fun x hx => hf' x (hsubset i x hx)) (hfinj i) hg
    rw [show weightedMultiplicity f (t i) g = (f '' t i).indicator h by
      funext y
      exact hpoint y]
    exact (hh.indicator (MeasureTheory.measurable_image_of_fderivWithin (ht i)
      (fun x hx => (hf' x (hsubset i x hx)).hasFDerivWithinAt) (hfinj i))).aemeasurable
  have hmult : ∀ y, weightedMultiplicity f s g y =
      ∑' i, weightedMultiplicity f (t i) g y := by
    intro y
    rw [← hpart]
    exact countable_weightedMultiplicity g hdisj y
  calc
    ∫⁻ y, weightedMultiplicity f s g y =
        ∫⁻ y, ∑' i, weightedMultiplicity f (t i) g y := lintegral_congr hmult
    _ = ∑' i, ∫⁻ y, weightedMultiplicity f (t i) g y :=
      MeasureTheory.lintegral_tsum hmeas
    _ = ∑' i, ∫⁻ x in t i, g x * ENNReal.ofReal (jacobian f x) := by
      apply tsum_congr
      intro i
      exact hpiece i
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) := by
      rw [← hpart, MeasureTheory.lintegral_iUnion ht hdisj]

private def equiv_of_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (h : A.det ≠ 0) : E ≃L[ℝ] E := by
  apply ContinuousLinearEquiv.ofBijective A
  · have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hk
      apply h
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
    exact hker
  · apply LinearMap.range_eq_top.mpr
    apply LinearMap.injective_iff_surjective.mp
    have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hk
      apply h
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
    exact (LinearMap.ker_eq_bot).mp hker

private theorem equiv_of_det_ne_zero_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (h : A.det ≠ 0) :
    (equiv_of_det_ne_zero A h : E →L[ℝ] E) = A := by
  change ↑(ContinuousLinearEquiv.ofBijective A _ _) = A
  exact ContinuousLinearEquiv.coe_ofBijective A _ _

theorem area_formula_image_weighted
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} (g : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
      ∫⁻ y, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  classical
  let f' : E → E →L[ℝ] E := fun x => fderiv ℝ f x
  let d : E → ℝ := fun x => (f' x).det
  let r : Set E := s ∩ d ⁻¹' {0}ᶜ
  let c : Set E := s \ r
  have hfd : ∀ x, HasFDerivAt f (f' x) x := by
    intro x
    exact (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hdm : Measurable d := by
    exact ContinuousLinearMap.continuous_det.measurable.comp
      (hf.continuous_fderiv one_ne_zero).measurable
  have hr : MeasurableSet r := by
    exact hs.inter ((MeasurableSet.singleton (0 : ℝ)).compl.preimage hdm)
  have hc : MeasurableSet c := hs.diff hr
  have hcrit : volume (f '' c) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (volume : Measure E)
    · intro x hx
      exact (hfd x).hasFDerivWithinAt
    · intro x hx
      have hxsr : x ∈ s := hx.1
      have hxnr : x ∉ r := hx.2
      have hxd : d x = 0 := by
        by_contra hne
        apply hxnr
        exact ⟨hxsr, hne⟩
      exact hxd
  have hjzero : ∀ x ∈ c, jacobian f x = 0 := by
    intro x hxc
    have hxd : d x = 0 := by
      by_contra hne
      apply hxc.2
      exact ⟨hxc.1, hne⟩
    have hdet : (f' x).det = 0 := by simpa [d] using hxd
    rw [jacobian_of_hasFDerivAt (hfd x), LinearMap.normDet_eq_norm_det]
    simp [hdet]
  have hreg_deriv : ∀ x ∈ r, HasFDerivWithinAt f (f' x) r x := by
    intro x hx
    exact (hfd x).hasFDerivWithinAt
  let ρ : (E →L[ℝ] E) → ℝ≥0 := fun A =>
    if hE : Subsingleton E then 1
    else if hA : A.det ≠ 0 then (NNNorm.nnnorm ((equiv_of_det_ne_zero A hA).symm : E →L[ℝ] E))⁻¹ / 2
    else 1
  have hρ : ∀ A, ρ A ≠ 0 := by
    intro A
    by_cases hE : Subsingleton E
    · simp [ρ, hE]
    · simp only [ρ, hE, ↓reduceDIte]
      split_ifs with hA
      · have hpos : 0 < NNNorm.nnnorm ((equiv_of_det_ne_zero A hA).symm : E →L[ℝ] E) :=
          (equiv_of_det_ne_zero A hA).subsingleton_or_nnnorm_symm_pos.resolve_left hE
        exact div_ne_zero (inv_ne_zero hpos.ne') (by norm_num)
      · simp
  obtain ⟨t, A, ht_disj, ht_meas, ht_cover, ht_approx, ht_repr⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f r f' hreg_deriv ρ hρ
  have hreg_nonempty_or : r.Nonempty ∨ r = ∅ := by
    rcases eq_empty_or_nonempty r with hre | hrne
    · exact Or.inr hre
    · exact Or.inl hrne
  rcases hreg_nonempty_or with hrne | hre
  · have hpiece_inj : ∀ n : ℕ, InjOn f (r ∩ t n) := by
      intro n
      obtain ⟨y, hyr, hAn⟩ := ht_repr hrne n
      have hdet : (A n).det ≠ 0 := by
        rw [hAn]
        simpa [r, d] using hyr.2
      let e := equiv_of_det_ne_zero (A n) hdet
      have he : (e : E →L[ℝ] E) = A n := by
        exact equiv_of_det_ne_zero_coe (A n) hdet
      have happrox : ApproximatesLinearOn f (e : E →L[ℝ] E) (r ∩ t n) (ρ (A n)) := by
        simpa [he] using ht_approx n
      have hc' : Subsingleton E ∨ ρ (A n) < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := by
        rcases e.subsingleton_or_nnnorm_symm_pos with hE | hpos
        · exact Or.inl hE
        · right
          have hEnot : ¬ Subsingleton E := by
            intro hE
            have hz : (e.symm : E →L[ℝ] E) = 0 := Subsingleton.elim _ _
            simp [hz] at hpos
          simpa [ρ, hEnot, hdet, e] using (NNReal.half_lt_self (inv_ne_zero hpos.ne'))
      exact happrox.injOn hc'
    let u : ℕ → Set E := fun n => r ∩ t n
    have hu_meas : ∀ n, MeasurableSet (u n) := fun n => hr.inter (ht_meas n)
    have hu_disj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (u i) (u j) := by
      intro i j hij
      exact (ht_disj hij).mono inter_subset_right inter_subset_right
    have hu_part : (⋃ n, u n) = r := by
      dsimp [u]
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
        exact hxn.1
      · intro x hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 (ht_cover hx)
        exact mem_iUnion.2 ⟨n, ⟨hx, hxn⟩⟩
    have hformula : ∫⁻ y, multiplicity f r y * g y =
        ∫⁻ x in r, ENNReal.ofReal (jacobian f x) * g (f x) := by
      exact area_formula_of_countable_injective_partition_image_weighted u g hu_part hu_meas hu_disj
        (fun x _ => hfd x) hpiece_inj hg
    have hleft : ∫⁻ y, multiplicity f s y * g y = ∫⁻ y, multiplicity f r y * g y := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' c := by
        apply ae_iff.mpr
        have hset : {a : E | ¬ a ∉ f '' c} = f '' c := by
          ext a
          simp
        rw [hset]
        exact hcrit
      filter_upwards [hae] with y hy
      have hset : s ∩ f ⁻¹' {y} = r ∩ f ⁻¹' {y} := by
        ext x
        constructor
        · rintro ⟨hxs, hxy⟩
          by_cases hxr : x ∈ r
          · exact ⟨hxr, hxy⟩
          · exfalso
            apply hy
            exact ⟨x, ⟨hxs, hxr⟩, hxy⟩
        · rintro ⟨hxr, hxy⟩
          exact ⟨hxr.1, hxy⟩
      rw [multiplicity, multiplicity, hset]
    have hright : ∫⁻ x in r, ENNReal.ofReal (jacobian f x) * g (f x) =
        ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [← MeasureTheory.lintegral_indicator hr, ← MeasureTheory.lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hxr : x ∈ r
      · have hxs : x ∈ s := hxr.1
        simp [Set.indicator, hxr, hxs]
      · by_cases hxs : x ∈ s
        · have hxc : x ∈ c := ⟨hxs, hxr⟩
          rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxr, hjzero x hxc]
          simp
        · simp [Set.indicator, hxr, hxs]
    exact hleft.trans (hformula.trans hright)
  · have hceq : c = s := by
      ext x
      constructor
      · exact fun hx => hx.1
      · intro hxs
        exact ⟨hxs, by simp [hre]⟩
    have hcrit' : volume (f '' s) = 0 := by simpa [hceq] using hcrit
    have hleft : ∫⁻ y, multiplicity f s y * g y = 0 := by
      rw [← lintegral_zero]
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' s := by
        apply ae_iff.mpr
        have hset : {a : E | ¬ a ∉ f '' s} = f '' s := by
          ext a
          simp
        rw [hset]
        exact hcrit'
      filter_upwards [hae] with y hy
      rw [multiplicity_eq_zero_of_not_mem_image hy]
      simp
    have hright : ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) = 0 := by
      rw [← MeasureTheory.lintegral_indicator hs, ← lintegral_zero]
      apply lintegral_congr_ae
      filter_upwards [] with x
      by_cases hxs : x ∈ s
      · have hxc : x ∈ c := by simpa [hceq] using hxs
        rw [Set.indicator_of_mem hxs, hjzero x hxc]
        simp
      · simp [Set.indicator, hxs]
    exact hleft.trans hright.symm

theorem area_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} (g : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
    ∫⁻ y, weightedMultiplicity f s g y =
      ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) := by
  classical
  let f' : E → E →L[ℝ] E := fun x => fderiv ℝ f x
  let d : E → ℝ := fun x => (f' x).det
  let r : Set E := s ∩ d ⁻¹' {0}ᶜ
  let c : Set E := s \ r
  have hfd : ∀ x, HasFDerivAt f (f' x) x := by
    intro x
    exact (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hdm : Measurable d := by
    exact ContinuousLinearMap.continuous_det.measurable.comp
      (hf.continuous_fderiv one_ne_zero).measurable
  have hr : MeasurableSet r := by
    exact hs.inter ((MeasurableSet.singleton (0 : ℝ)).compl.preimage hdm)
  have hc : MeasurableSet c := hs.diff hr
  have hcrit : volume (f '' c) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (volume : Measure E)
    · intro x hx
      exact (hfd x).hasFDerivWithinAt
    · intro x hx
      have hxsr : x ∈ s := hx.1
      have hxnr : x ∉ r := hx.2
      have hxd : d x = 0 := by
        by_contra hne
        apply hxnr
        exact ⟨hxsr, hne⟩
      exact hxd
  have hjzero : ∀ x ∈ c, jacobian f x = 0 := by
    intro x hxc
    have hxd : d x = 0 := by
      by_contra hne
      apply hxc.2
      exact ⟨hxc.1, hne⟩
    have hdet : (f' x).det = 0 := by simpa [d] using hxd
    rw [jacobian_of_hasFDerivAt (hfd x), LinearMap.normDet_eq_norm_det]
    simp [hdet]
  have hreg_deriv : ∀ x ∈ r, HasFDerivWithinAt f (f' x) r x := by
    intro x hx
    exact (hfd x).hasFDerivWithinAt
  let ρ : (E →L[ℝ] E) → ℝ≥0 := fun A =>
    if hE : Subsingleton E then 1
    else if hA : A.det ≠ 0 then
      (NNNorm.nnnorm ((equiv_of_det_ne_zero A hA).symm : E →L[ℝ] E))⁻¹ / 2
    else 1
  have hρ : ∀ A, ρ A ≠ 0 := by
    intro A
    by_cases hE : Subsingleton E
    · simp [ρ, hE]
    · simp only [ρ, hE, ↓reduceDIte]
      split_ifs with hA
      · have hpos : 0 < NNNorm.nnnorm
            ((equiv_of_det_ne_zero A hA).symm : E →L[ℝ] E) :=
          (equiv_of_det_ne_zero A hA).subsingleton_or_nnnorm_symm_pos.resolve_left hE
        exact div_ne_zero (inv_ne_zero hpos.ne') (by norm_num)
      · simp
  obtain ⟨t, A, ht_disj, ht_meas, ht_cover, ht_approx, ht_repr⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f r f' hreg_deriv ρ hρ
  rcases eq_empty_or_nonempty r with hre | hrne
  · have hceq : c = s := by
      ext x
      constructor
      · exact fun hx => hx.1
      · intro hxs
        exact ⟨hxs, by simp [hre]⟩
    have hcrit' : volume (f '' s) = 0 := by simpa [hceq] using hcrit
    have hleft : ∫⁻ y, weightedMultiplicity f s g y = 0 := by
      rw [← lintegral_zero]
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' s := by
        apply ae_iff.mpr
        have hset : {a : E | ¬ a ∉ f '' s} = f '' s := by
          ext a
          simp
        rw [hset]
        exact hcrit'
      filter_upwards [hae] with y hy
      have hfiber : s ∩ f ⁻¹' {y} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false]
        rintro ⟨hxs, hxy⟩
        exact hy ⟨x, hxs, hxy⟩
      rw [weightedMultiplicity, hfiber]
      simp
    have hright : ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) = 0 := by
      rw [← MeasureTheory.lintegral_indicator hs, ← lintegral_zero]
      apply lintegral_congr_ae
      filter_upwards [] with x
      by_cases hxs : x ∈ s
      · have hxc : x ∈ c := by simpa [hceq] using hxs
        rw [Set.indicator_of_mem hxs, hjzero x hxc]
        simp
      · simp [Set.indicator, hxs]
    exact hleft.trans hright.symm
  · have hpiece_inj : ∀ n : ℕ, InjOn f (r ∩ t n) := by
      intro n
      obtain ⟨y, hyr, hAn⟩ := ht_repr hrne n
      have hdet : (A n).det ≠ 0 := by
        rw [hAn]
        simpa [r, d] using hyr.2
      let e := equiv_of_det_ne_zero (A n) hdet
      have he : (e : E →L[ℝ] E) = A n := equiv_of_det_ne_zero_coe (A n) hdet
      have happrox : ApproximatesLinearOn f (e : E →L[ℝ] E)
          (r ∩ t n) (ρ (A n)) := by
        simpa [he] using ht_approx n
      have hc' : Subsingleton E ∨ ρ (A n) < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := by
        rcases e.subsingleton_or_nnnorm_symm_pos with hE | hpos
        · exact Or.inl hE
        · right
          have hEnot : ¬ Subsingleton E := by
            intro hE
            have hz : (e.symm : E →L[ℝ] E) = 0 := Subsingleton.elim _ _
            simp [hz] at hpos
          simpa [ρ, hEnot, hdet, e] using
            (NNReal.half_lt_self (inv_ne_zero hpos.ne'))
      exact happrox.injOn hc'
    let u : ℕ → Set E := fun n => r ∩ t n
    have hu_meas : ∀ n, MeasurableSet (u n) := fun n => hr.inter (ht_meas n)
    have hu_disj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (u i) (u j) := by
      intro i j hij
      exact (ht_disj hij).mono inter_subset_right inter_subset_right
    have hu_part : (⋃ n, u n) = r := by
      dsimp [u]
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
        exact hxn.1
      · intro x hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 (ht_cover hx)
        exact mem_iUnion.2 ⟨n, ⟨hx, hxn⟩⟩
    have hformula : ∫⁻ y, weightedMultiplicity f r g y =
        ∫⁻ x in r, g x * ENNReal.ofReal (jacobian f x) :=
      area_formula_of_countable_injective_partition u g hu_part hu_meas hu_disj
        (fun x _ => hfd x) hpiece_inj hg
    have hleft : ∫⁻ y, weightedMultiplicity f s g y =
        ∫⁻ y, weightedMultiplicity f r g y := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' c := by
        apply ae_iff.mpr
        have hset : {a : E | ¬ a ∉ f '' c} = f '' c := by
          ext a
          simp
        rw [hset]
        exact hcrit
      filter_upwards [hae] with y hy
      have hset : s ∩ f ⁻¹' {y} = r ∩ f ⁻¹' {y} := by
        ext x
        constructor
        · rintro ⟨hxs, hxy⟩
          by_cases hxr : x ∈ r
          · exact ⟨hxr, hxy⟩
          · exfalso
            apply hy
            exact ⟨x, ⟨hxs, hxr⟩, hxy⟩
        · rintro ⟨hxr, hxy⟩
          exact ⟨hxr.1, hxy⟩
      rw [weightedMultiplicity, weightedMultiplicity, hset]
    have hright : ∫⁻ x in r, g x * ENNReal.ofReal (jacobian f x) =
        ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x) := by
      rw [← MeasureTheory.lintegral_indicator hr, ← MeasureTheory.lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hxr : x ∈ r
      · have hxs : x ∈ s := hxr.1
        simp [Set.indicator, hxr, hxs]
      · by_cases hxs : x ∈ s
        · have hxc : x ∈ c := ⟨hxs, hxr⟩
          rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxr, hjzero x hxc]
          simp
        · simp [Set.indicator, hxr, hxs]
    exact hleft.trans (hformula.trans hright)

theorem area_formula_image_weighted_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} (g : F → ℝ≥0∞)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
    ∫⁻ y, multiplicity f s y * g y ∂μHE[Module.finrank ℝ F] =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x)
        ∂μHE[Module.finrank ℝ E] := by
  let e : F ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hfinrank.symm)
  let h : E → E := e ∘ f
  let g' : E → ℝ≥0∞ := fun z => g (e.symm z)
  have hmap : Measure.map (e : F → E) (μHE[Module.finrank ℝ F] : Measure F) =
      μHE[Module.finrank ℝ E] := by
    apply Measure.ext
    intro t ht
    rw [Measure.map_apply e.continuous.measurable ht]
    rw [show Module.finrank ℝ E = Module.finrank ℝ F from hfinrank]
    simpa only [Set.image_preimage_eq t e.surjective] using
      (e.isometry.euclideanHausdorffMeasure_image (d := Module.finrank ℝ F) (e ⁻¹' t)).symm
  have hfd : ∀ x, HasFDerivAt f (fderiv ℝ f x) x := by
    intro x
    exact (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hjac : ∀ x, jacobian h x = jacobian f x := by
    intro x
    have hcomp := e.toContinuousLinearMap.hasFDerivAt.comp x (hfd x)
    have hcomp' : HasFDerivAt (fun z => e (f z))
        (e.toContinuousLinearMap.comp (fderiv ℝ f x)) x := by
      rw [show (fun z => e (f z)) = (fun z => e.toContinuousLinearMap (f z)) by rfl]
      exact hcomp
    change jacobian (fun z => e (f z)) x = jacobian f x
    rw [jacobian_of_hasFDerivAt hcomp', jacobian_of_hasFDerivAt (hfd x)]
    change (e.toLinearIsometry.toLinearMap ∘ₗ (fderiv ℝ f x).toLinearMap).normDet =
      (fderiv ℝ f x).toLinearMap.normDet
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ hfinrank]
    simp [e.toLinearIsometry.normDet_eq_one]
  have hmult : ∀ y : F, multiplicity h s (e y) = multiplicity f s y := by
    intro y
    unfold multiplicity
    apply (ENat.toENNReal_inj).mpr
    have hset : s ∩ h ⁻¹' {e y} = s ∩ f ⁻¹' {y} := by
      ext x
      simp [h, e.injective.eq_iff]
    rw [hset]
  have hformula := area_formula_image_weighted (f := h) (s := s) g' hs
    (by exact e.contDiff.comp hf) (hg.comp e.symm.continuous.measurable)
  have hformula' :
      ∫⁻ z : E, multiplicity h s z * g' z ∂μHE[Module.finrank ℝ E] =
        ∫⁻ x in s, ENNReal.ofReal (jacobian h x) * g' (h x)
          ∂μHE[Module.finrank ℝ E] := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact hformula
  have hleft :
      ∫⁻ z : E, multiplicity h s z * g' z ∂μHE[Module.finrank ℝ E] =
        ∫⁻ y : F, multiplicity h s (e y) * g y ∂μHE[Module.finrank ℝ F] := by
    rw [← hmap]
    simpa [g', e.symm_apply_apply] using
      e.toHomeomorph.measurableEmbedding.lintegral_map
        (fun z : E => multiplicity h s z * g' z)
  calc
    ∫⁻ y : F, multiplicity f s y * g y ∂μHE[Module.finrank ℝ F] =
        ∫⁻ y : F, multiplicity h s (e y) * g y ∂μHE[Module.finrank ℝ F] := by
      apply lintegral_congr
      intro y
      rw [hmult]
    _ = ∫⁻ z : E, multiplicity h s z * g' z ∂μHE[Module.finrank ℝ E] := hleft.symm
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian h x) * g' (h x)
        ∂μHE[Module.finrank ℝ E] := hformula'
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x)
        ∂μHE[Module.finrank ℝ E] := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change ENNReal.ofReal (jacobian h x) * g' (h x) =
        ENNReal.ofReal (jacobian f x) * g (f x)
      rw [hjac x]
      simp [h, g', e.symm_apply_apply]

theorem area_formula_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} (g : E → ℝ≥0∞)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
    ∫⁻ y, weightedMultiplicity f s g y ∂μHE[Module.finrank ℝ F] =
      ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
  let e : F ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hfinrank.symm)
  let h : E → E := e ∘ f
  have hmap : Measure.map (e : F → E) (μHE[Module.finrank ℝ F] : Measure F) =
      μHE[Module.finrank ℝ E] := by
    apply Measure.ext
    intro t ht
    rw [Measure.map_apply e.continuous.measurable ht]
    rw [show Module.finrank ℝ E = Module.finrank ℝ F from hfinrank]
    simpa only [Set.image_preimage_eq t e.surjective] using
      (e.isometry.euclideanHausdorffMeasure_image (d := Module.finrank ℝ F) (e ⁻¹' t)).symm
  have hfd : ∀ x, HasFDerivAt f (fderiv ℝ f x) x := by
    intro x
    exact (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hjac : ∀ x, jacobian h x = jacobian f x := by
    intro x
    have hcomp := e.toContinuousLinearMap.hasFDerivAt.comp x (hfd x)
    have hcomp' : HasFDerivAt (fun z => e (f z))
        (e.toContinuousLinearMap.comp (fderiv ℝ f x)) x := by
      rw [show (fun z => e (f z)) = (fun z => e.toContinuousLinearMap (f z)) by rfl]
      exact hcomp
    change jacobian (fun z => e (f z)) x = jacobian f x
    rw [jacobian_of_hasFDerivAt hcomp', jacobian_of_hasFDerivAt (hfd x)]
    change (e.toLinearIsometry.toLinearMap ∘ₗ (fderiv ℝ f x).toLinearMap).normDet =
      (fderiv ℝ f x).toLinearMap.normDet
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ hfinrank]
    simp [e.toLinearIsometry.normDet_eq_one]
  have hmult : ∀ y : F, weightedMultiplicity h s g (e y) =
      weightedMultiplicity f s g y := by
    intro y
    unfold weightedMultiplicity
    have hset : s ∩ h ⁻¹' {e y} = s ∩ f ⁻¹' {y} := by
      ext x
      simp [h, e.injective.eq_iff]
    rw [hset]
  have hformula := area_formula (f := h) (s := s) g hs
    (by exact e.contDiff.comp hf) hg
  have hformula' :
      ∫⁻ z : E, weightedMultiplicity h s g z ∂μHE[Module.finrank ℝ E] =
        ∫⁻ x in s, g x * ENNReal.ofReal (jacobian h x)
          ∂μHE[Module.finrank ℝ E] := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact hformula
  have hleft :
      ∫⁻ z : E, weightedMultiplicity h s g z ∂μHE[Module.finrank ℝ E] =
        ∫⁻ y : F, weightedMultiplicity h s g (e y) ∂μHE[Module.finrank ℝ F] := by
    rw [← hmap]
    simpa using e.toHomeomorph.measurableEmbedding.lintegral_map
      (weightedMultiplicity h s g)
  calc
    ∫⁻ y : F, weightedMultiplicity f s g y ∂μHE[Module.finrank ℝ F] =
        ∫⁻ y : F, weightedMultiplicity h s g (e y) ∂μHE[Module.finrank ℝ F] := by
      apply lintegral_congr
      intro y
      rw [hmult]
    _ = ∫⁻ z : E, weightedMultiplicity h s g z ∂μHE[Module.finrank ℝ E] := hleft.symm
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian h x)
        ∂μHE[Module.finrank ℝ E] := hformula'
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change g x * ENNReal.ofReal (jacobian h x) =
        g x * ENNReal.ofReal (jacobian f x)
      rw [hjac x]

theorem area_formula_of_finrank_eq_unweighted
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) :
    ∫⁻ y, multiplicity f s y ∂μHE[Module.finrank ℝ F] =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) ∂μHE[Module.finrank ℝ E] := by
  simpa only [weightedMultiplicity_one, one_mul] using
    (area_formula_of_finrank_eq (f := f) (s := s) (fun _ => (1 : ℝ≥0∞))
      hfinrank hs hf measurable_const)

theorem injective_area_formula_weighted_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} (g : E → ℝ≥0∞)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hfinj : InjOn f s) (hg : Measurable g) :
    ∫⁻ y, weightedMultiplicity f s g y ∂μHE[Module.finrank ℝ F] =
      ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
  let e : F ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hfinrank.symm)
  let h : E → E := e ∘ f
  let h' : E → E →L[ℝ] E := fun x => e.toContinuousLinearMap.comp (f' x)
  have hh' : ∀ x ∈ s, HasFDerivAt h (h' x) x := by
    intro x hx
    exact e.toContinuousLinearMap.hasFDerivAt.comp x (hf' x hx)
  have hhinj : InjOn h s := fun x hx y hy hxy => hfinj hx hy (e.injective hxy)
  have hmap : Measure.map (e : F → E) (μHE[Module.finrank ℝ F] : Measure F) =
      μHE[Module.finrank ℝ E] := by
    apply Measure.ext
    intro t ht
    rw [Measure.map_apply e.continuous.measurable ht]
    rw [show Module.finrank ℝ E = Module.finrank ℝ F from hfinrank]
    simpa only [Set.image_preimage_eq t e.surjective] using
      (e.isometry.euclideanHausdorffMeasure_image (d := Module.finrank ℝ F) (e ⁻¹' t)).symm
  have hjac : ∀ x ∈ s, jacobian h x = jacobian f x := by
    intro x hx
    rw [jacobian_of_hasFDerivAt (hh' x hx), jacobian_of_hasFDerivAt (hf' x hx)]
    change (e.toLinearIsometry.toLinearMap ∘ₗ (f' x).toLinearMap).normDet =
      (f' x).toLinearMap.normDet
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ hfinrank]
    simp [e.toLinearIsometry.normDet_eq_one]
  have hmult : ∀ y : F, weightedMultiplicity h s g (e y) =
      weightedMultiplicity f s g y := by
    intro y
    unfold weightedMultiplicity
    have hset : s ∩ h ⁻¹' {e y} = s ∩ f ⁻¹' {y} := by
      ext x
      simp [h, e.injective.eq_iff]
    rw [hset]
  have hformula := injective_area_formula_weighted g hs hh' hhinj hg
  have hformula' :
      ∫⁻ z : E, weightedMultiplicity h s g z ∂μHE[Module.finrank ℝ E] =
        ∫⁻ x in s, g x * ENNReal.ofReal (jacobian h x)
          ∂μHE[Module.finrank ℝ E] := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using hformula
  have hleft :
      ∫⁻ z : E, weightedMultiplicity h s g z ∂μHE[Module.finrank ℝ E] =
        ∫⁻ y : F, weightedMultiplicity h s g (e y) ∂μHE[Module.finrank ℝ F] := by
    rw [← hmap]
    simpa using e.toHomeomorph.measurableEmbedding.lintegral_map
      (weightedMultiplicity h s g)
  calc
    ∫⁻ y : F, weightedMultiplicity f s g y ∂μHE[Module.finrank ℝ F] =
        ∫⁻ y : F, weightedMultiplicity h s g (e y) ∂μHE[Module.finrank ℝ F] := by
      apply lintegral_congr
      intro y
      rw [hmult]
    _ = ∫⁻ z : E, weightedMultiplicity h s g z ∂μHE[Module.finrank ℝ E] := hleft.symm
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian h x)
        ∂μHE[Module.finrank ℝ E] := hformula'
    _ = ∫⁻ x in s, g x * ENNReal.ofReal (jacobian f x)
        ∂μHE[Module.finrank ℝ E] := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change g x * ENNReal.ofReal (jacobian h x) =
        g x * ENNReal.ofReal (jacobian f x)
      rw [hjac x hx]

theorem injective_area_formula_image_weighted_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} (g : F → ℝ≥0∞)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) (hg : Measurable g)
    (hfinj : InjOn f s) :
    ∫⁻ y in f '' s, g y ∂μHE[Module.finrank ℝ F] =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x)
        ∂μHE[Module.finrank ℝ E] := by
  let e : F ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hfinrank.symm)
  let h : E → E := e ∘ f
  have hfinj' : InjOn h s := by
    intro x hx y hy hxy
    exact hfinj hx hy (e.injective hxy)
  have hfd : ∀ x, HasFDerivAt f (fderiv ℝ f x) x := by
    intro x
    exact (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have himage : MeasurableSet (f '' s) := by
    have himage' : MeasurableSet (h '' s) := by
      apply MeasureTheory.measurable_image_of_fderivWithin hs
        (fun x hx => (e.toContinuousLinearMap.hasFDerivAt.comp x (hfd x)).hasFDerivWithinAt)
        hfinj'
    have heq : f '' s = e.symm '' (h '' s) := by
      ext y
      constructor
      · rintro ⟨x, hxs, rfl⟩
        exact ⟨e (f x), ⟨x, hxs, rfl⟩, e.symm_apply_apply _⟩
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, hxs, hxz⟩ := hz
        refine ⟨x, hxs, ?_⟩
        simpa [h] using congrArg e.symm hxz
    rw [heq]
    exact e.symm.toHomeomorph.measurableEmbedding.measurableSet_image.mpr himage'
  have hmult : ∀ y : F, multiplicity f s y * g y = (f '' s).indicator g y := by
    intro y
    by_cases hy : y ∈ f '' s
    · rw [multiplicity_eq_one_of_injOn hfinj hy]
      simp [Set.indicator, hy]
    · rw [multiplicity_eq_zero_of_not_mem_image hy]
      simp [Set.indicator, hy]
  calc
    ∫⁻ y in f '' s, g y ∂μHE[Module.finrank ℝ F] =
        ∫⁻ y : F, (f '' s).indicator g y ∂μHE[Module.finrank ℝ F] :=
      (MeasureTheory.lintegral_indicator himage g).symm
    _ = ∫⁻ y : F, multiplicity f s y * g y ∂μHE[Module.finrank ℝ F] := by
      apply lintegral_congr
      intro y
      rw [hmult]
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x)
        ∂μHE[Module.finrank ℝ E] :=
      area_formula_image_weighted_of_finrank_eq g hfinrank hs hf hg

theorem area_formula_unweighted
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) :
      ∫⁻ y, multiplicity f s y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) := by
  simpa only [weightedMultiplicity_one, one_mul] using
    (area_formula (f := f) (s := s) (fun _ => (1 : ℝ≥0∞)) hs hf measurable_const)

end Area
