import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal MeasureTheory NNReal

namespace Area

theorem lipschitz_extension_real {X : Type*} [PseudoMetricSpace X] {s : Set X}
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : X → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  exact hf.extend_real

theorem lipschitz_image_hmeasure_le {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) (s : Set X) :
    μH[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μH[d] s := by
  exact hf.hausdorffMeasure_image_le hd s

theorem rademacher {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂(Measure.addHaar : Measure E), DifferentiableAt ℝ f x := by
  exact hf.ae_differentiableAt

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def jacobian (f : E → F) (x : E) : ℝ :=
  (fderiv ℝ f x).toLinearMap.normDet

def jacobianWithin (f : E → F) (s : Set E) (x : E) : ℝ :=
  (fderivWithin ℝ f s x).toLinearMap.normDet

theorem jacobian_nonneg (f : E → F) (x : E) : 0 ≤ jacobian f x := by
  exact LinearMap.normDet_nonneg _

theorem jacobian_of_hasFDerivAt {f : E → F} {L : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt f L x) : jacobian f x = L.toLinearMap.normDet := by
  simp [jacobian, h.fderiv]

theorem jacobian_of_hasFDerivWithinAt {f : E → F} {L : E →L[ℝ] F} {s : Set E} {x : E}
    (h : HasFDerivWithinAt f L s x) (hs : UniqueDiffWithinAt ℝ s x) :
    jacobianWithin f s x = L.toLinearMap.normDet := by
  rw [jacobianWithin, h.fderivWithin hs]

theorem jacobian_continuousLinearMap (L : E →L[ℝ] F) (x : E) :
    jacobian L x = L.toLinearMap.normDet := by
  exact jacobian_of_hasFDerivAt L.hasFDerivAt

theorem jacobian_linearMap (L : E →ₗ[ℝ] F) (x : E) :
    jacobian L x = L.normDet := by
  let L' : E →L[ℝ] F := L.toContinuousLinearMap
  simpa [L'] using jacobian_continuousLinearMap L' x

theorem linear_area_formula [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (L : E →ₗ[ℝ] F) (s : Set E) :
    μHE[Module.finrank ℝ E] (L '' s) =
      ENNReal.ofReal L.normDet * μHE[Module.finrank ℝ E] s := by
  exact L.euclideanHausdorffMeasure_image s

theorem linear_area_formula_eq_volume
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (L : E →ₗ[ℝ] F) (s : Set E) :
    μHE[Module.finrank ℝ E] (L '' s) = ENNReal.ofReal L.normDet * volume s := by
  exact L.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s

theorem jacobian_zero (x : E) : jacobian (0 : E → F) x = 0 ^ Module.finrank ℝ E := by
  rw [jacobian]
  simp [LinearMap.normDet_zero]

theorem jacobian_id (x : E) : jacobian (id : E → E) x = 1 := by
  rw [jacobian]
  simp

end Area
