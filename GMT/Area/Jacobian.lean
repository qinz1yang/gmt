import GMT.Linear.NormDet
import Mathlib.Analysis.Calculus.Rademacher
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

theorem lipschitz_dimension_lowering_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hEF : Module.finrank ℝ E < Module.finrank ℝ F) :
    μHE[Module.finrank ℝ F] (Set.range f) = 0 := by
  have hdim : (Module.finrank ℝ E : ℝ) < Module.finrank ℝ F := by
    exact_mod_cast hEF
  have hsource : μH[(Module.finrank ℝ F : ℝ)] (Set.univ : Set E) = 0 := by
    rw [Real.hausdorffMeasure_of_finrank_lt hdim]
    simp
  have himage : μH[(Module.finrank ℝ F : ℝ)] (Set.range f) ≤
      (K : ℝ≥0∞) ^ (Module.finrank ℝ F : ℝ) *
        μH[(Module.finrank ℝ F : ℝ)] (Set.univ : Set E) := by
    simpa only [Set.image_univ] using
      hf.hausdorffMeasure_image_le (show (0 : ℝ) ≤ Module.finrank ℝ F by positivity) Set.univ
  have hzero : μH[(Module.finrank ℝ F : ℝ)] (Set.range f) = 0 := by
    rw [hsource, mul_zero] at himage
    exact nonpos_iff_eq_zero.mp himage
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hzero, smul_zero]

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

theorem measurable_jacobian [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ F] (f : E → F) : Measurable (jacobian f) := by
  exact ContinuousLinearMap.continuous_normDet.measurable.comp
    (measurable_fderiv ℝ f)

section

variable [FiniteDimensional ℝ F]

def coareaJacobian (f : E → F) (x : E) : ℝ :=
  (fderiv ℝ f x).toLinearMap.adjoint.normDet

theorem coareaJacobian_nonneg (f : E → F) (x : E) : 0 ≤ coareaJacobian f x := by
  exact LinearMap.normDet_nonneg _

theorem coareaJacobian_of_hasFDerivAt {f : E → F} {L : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt f L x) : coareaJacobian f x = L.toLinearMap.adjoint.normDet := by
  simp [coareaJacobian, h.fderiv]

theorem coareaJacobian_continuousLinearMap (L : E →L[ℝ] F) (x : E) :
    coareaJacobian L x = L.toLinearMap.adjoint.normDet := by
  exact coareaJacobian_of_hasFDerivAt L.hasFDerivAt

theorem coareaJacobian_linearMap (L : E →ₗ[ℝ] F) (x : E) :
    coareaJacobian L x = L.adjoint.normDet := by
  let L' : E →L[ℝ] F := L.toContinuousLinearMap
  simpa [L'] using coareaJacobian_continuousLinearMap L' x

theorem coareaJacobian_eq_jacobian_of_finrank_eq
    (h : Module.finrank ℝ E = Module.finrank ℝ F) (f : E → F) (x : E) :
    coareaJacobian f x = jacobian f x := by
  exact LinearMap.normDet_adjoint_of_finrank_eq _ h

theorem coareaJacobian_eq_zero_of_not_surjective
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x)
    (hL : ¬ Function.Surjective L) : coareaJacobian f x = 0 := by
  rw [coareaJacobian_of_hasFDerivAt hf, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    ← LinearMap.orthogonal_range]
  intro h
  apply hL
  exact LinearMap.range_eq_top.mp (Submodule.orthogonal_eq_bot_iff.mp h)

theorem coareaJacobian_eq_zero_of_finrank_lt
    (h : Module.finrank ℝ E < Module.finrank ℝ F) (f : E → F) (x : E) :
    coareaJacobian f x = 0 := by
  rw [coareaJacobian, LinearMap.normDet_eq_zero_iff_ker_ne_bot]
  exact (fderiv ℝ f x).toLinearMap.adjoint.ker_ne_bot_of_finrank_lt h

theorem coareaJacobian_sq (f : E → F) (x : E) :
    coareaJacobian f x ^ 2 =
      ((fderiv ℝ f x).toLinearMap ∘ₗ (fderiv ℝ f x).toLinearMap.adjoint).det := by
  simpa [coareaJacobian] using
    LinearMap.normDet_sq (fderiv ℝ f x).toLinearMap.adjoint

theorem coareaJacobian_zero (x : E) :
    coareaJacobian (0 : E → F) x = 0 ^ Module.finrank ℝ F := by
  rw [coareaJacobian]
  simp [LinearMap.normDet_zero]

theorem coareaJacobian_id (x : E) : coareaJacobian (id : E → E) x = 1 := by
  rw [coareaJacobian]
  simp

theorem measurable_coareaJacobian [MeasurableSpace E] [BorelSpace E]
    (f : E → F) : Measurable (coareaJacobian f) := by
  exact ContinuousLinearMap.continuous_normDet.measurable.comp
    (ContinuousLinearMap.adjoint.continuous.measurable.comp (measurable_fderiv ℝ f))

end

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
