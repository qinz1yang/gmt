import GMT.Varifold.FirstVariation

open Function Metric Set TopologicalSpace
open scoped Distributions MeasureTheory Topology

noncomputable section

namespace Varifold

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

theorem IsStationaryOn.integral_squaredRadiusRadial_eq_zero
    {V : Varifold E n} {U : Opens E} (hV : V.IsStationaryOn U)
    {center : E} {profile : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall center R ⊆ U) (hprofile : ContDiff ℝ 1 profile)
    (hzero : ∀ t, R ^ 2 < t → profile t = 0) :
    ∫ z : E × Grassmannian E n,
        ((n : ℝ) * profile (‖z.1 - center‖ ^ 2) +
          2 * deriv profile (‖z.1 - center‖ ^ 2) *
            ‖z.2.projection (z.1 - center)‖ ^ 2) ∂V.toMeasure = 0 := by
  let K : Compacts E := ⟨closedBall center R, isCompact_closedBall center R⟩
  let X_K : ContDiffMapSupportedIn E E 1 K :=
    ⟨squaredRadiusRadialVectorField center profile,
      contDiff_squaredRadiusRadialVectorField hprofile center,
      by
        intro y hy
        change y ∉ closedBall center R at hy
        have hy' : R < dist y center := by
          simpa only [Metric.mem_closedBall, not_le] using hy
        have hsq : R ^ 2 < ‖y - center‖ ^ 2 := by
          rw [← dist_eq_norm]
          nlinarith [show 0 ≤ dist y center from dist_nonneg]
        simp only [squaredRadiusRadialVectorField, hzero _ hsq, zero_smul,
          Pi.zero_apply]⟩
  let X : TestFunction U E 1 := TestFunction.ofSupportedIn hball X_K
  have hstationary := hV.integral_tangentialDivergence_eq_zero X
  have hfield : (X : E → E) = squaredRadiusRadialVectorField center profile := by
    rfl
  rw [hfield] at hstationary
  calc
    ∫ z : E × Grassmannian E n,
        ((n : ℝ) * profile (‖z.1 - center‖ ^ 2) +
          2 * deriv profile (‖z.1 - center‖ ^ 2) *
            ‖z.2.projection (z.1 - center)‖ ^ 2) ∂V.toMeasure =
      ∫ z : E × Grassmannian E n,
        z.2.tangentialDivergence (squaredRadiusRadialVectorField center profile) z.1
          ∂V.toMeasure := by
            apply integral_congr_ae
            filter_upwards [] with z
            symm
            apply Grassmannian.tangentialDivergence_squaredRadiusRadialVectorField
            exact (hprofile.differentiable (by norm_num) _).hasDerivAt
    _ = 0 := hstationary

end Varifold
