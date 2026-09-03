import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open Function
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem integral_fderiv_eq_zero {f : E → F} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (v : E) :
    ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have hdf : Continuous fun x => fderiv ℝ f x v := by
    exact (hf.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hidf : Integrable (fun x => fderiv ℝ f x v) μ :=
    hdf.integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v)
  have hif : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hfc
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := μ) (f := fun _ : E => (1 : ℝ)) (g := f) (v := v)
    (by simp) (by simpa using hidf) (by simpa using hif)
    (fun _ _ => differentiableAt_const (c := (1 : ℝ)))
    (fun x _ => hf.differentiable one_ne_zero x)
  simpa using h

end MeasureTheory
