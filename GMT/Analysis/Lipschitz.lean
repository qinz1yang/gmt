import GMT.Measure.Lusin
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open Filter Metric Set
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal MeasureTheory NNReal Pointwise Topology

theorem LipschitzWith.exists_isClosed_differentiableAt_continuousOn_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set E, IsClosed s ∧ (Measure.addHaar : Measure E) sᶜ < ε ∧
      (∀ x ∈ s, DifferentiableAt ℝ f x) ∧ ContinuousOn (fderiv ℝ f) s := by
  let D : Set E := {x | DifferentiableAt ℝ f x}
  have hDmeas : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hfderiv : StronglyMeasurable (fderiv ℝ f) :=
    (measurable_fderiv ℝ f).stronglyMeasurable
  obtain ⟨s, hsD, hsclosed, hsmeasure, hscontinuous⟩ :=
    StronglyMeasurable.exists_isClosed_continuousOn_of_isLocallyFiniteMeasure
      (mu := (Measure.addHaar : Measure E)) hfderiv hDmeas hε
  have hDnull : (Measure.addHaar : Measure E) Dᶜ = 0 := by
    change (Measure.addHaar : Measure E) {x | ¬DifferentiableAt ℝ f x} = 0
    exact ae_iff.1 (hf.ae_differentiableAt (μ := (Measure.addHaar : Measure E)))
  have hsubset : sᶜ ⊆ (D \ s) ∪ Dᶜ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl ⟨hxD, hx⟩
    · exact Or.inr hxD
  refine ⟨s, hsclosed, ?_, fun x hx => hsD hx, hscontinuous⟩
  calc
    (Measure.addHaar : Measure E) sᶜ ≤
        (Measure.addHaar : Measure E) ((D \ s) ∪ Dᶜ) := measure_mono hsubset
    _ ≤ (Measure.addHaar : Measure E) (D \ s) +
        (Measure.addHaar : Measure E) Dᶜ := measure_union_le _ _
    _ = (Measure.addHaar : Measure E) (D \ s) := by rw [hDnull, add_zero]
    _ < ε := hsmeasure

theorem ApproximatesLinearOn.ae_norm_fderiv_sub_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    {s : Set E} {f : E → F} {A : E →L[ℝ] F} {δ : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s)
    (f' : E → E →L[ℝ] F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    ∀ᵐ x ∂mu.restrict s, ‖f' x - A‖₊ ≤ δ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div mu s, ae_restrict_mem hs]
  intro x hx xs
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  suffices H : ∀ ε, 0 < ε →
      ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have hlim : Tendsto
        (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at hlim
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin]
    exact H
  intro ε εpos
  have hnonempty : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one mu s x hx _ measurableSet_closedBall
      (measure_closedBall_pos mu z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
      ∃ ρ > 0, ball x ρ ∩ s ⊆
        {y : E | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  have hsubset : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
      ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (hnonempty.and (hsubset.and self_mem_nhdsWithin)).exists
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
          Pi.sub_apply, map_smul, smul_sub]
      _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ :=
        norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ :=
        add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
      congr 1
      simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I
        exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr
