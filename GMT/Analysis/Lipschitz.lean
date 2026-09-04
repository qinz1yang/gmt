import GMT.Measure.Lusin
import Mathlib.Analysis.Calculus.Rademacher

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal MeasureTheory NNReal

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
