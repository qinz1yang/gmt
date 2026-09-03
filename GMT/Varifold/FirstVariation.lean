import GMT.Analysis.Radial
import GMT.Varifold.Basic
import Mathlib.Analysis.Distribution.TestFunction

open Function Set TopologicalSpace
open scoped Distributions ENNReal MeasureTheory NNReal Topology

noncomputable section

namespace Grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

def tangentialDivergence (S : Grassmannian E n) (X : E → E) (x : E) : ℝ :=
  S.tangentialTrace (fderiv ℝ X x)

theorem tangentialDivergence_radialVectorField (S : Grassmannian E n)
    {profile : ℝ → ℝ} {profile' : ℝ} {center x : E}
    (hprofile : HasDerivAt profile profile' ‖x - center‖) (hx : x ≠ center) :
    S.tangentialDivergence (radialVectorField center profile) x =
      (n : ℝ) * profile ‖x - center‖ +
        (‖x - center‖⁻¹ * profile') * ‖S.projection (x - center)‖ ^ 2 :=
  S.tangentialTrace_fderiv_radialVectorField hprofile hx

theorem tangentialDivergence_radialVectorField_eq_perpendicularProjection
    (S : Grassmannian E n) {profile : ℝ → ℝ} {profile' : ℝ}
    {center x : E} (hprofile : HasDerivAt profile profile' ‖x - center‖)
    (hx : x ≠ center) :
    S.tangentialDivergence (radialVectorField center profile) x =
      (n : ℝ) * profile ‖x - center‖ + ‖x - center‖ * profile' -
        (‖x - center‖⁻¹ * profile') *
          ‖S.perpendicularProjection (x - center)‖ ^ 2 :=
  S.tangentialTrace_fderiv_radialVectorField_eq_perpendicularProjection hprofile hx

theorem tangentialDivergence_squaredRadiusRadialVectorField
    (S : Grassmannian E n) {profile : ℝ → ℝ} {profile' : ℝ}
    {center x : E} (hprofile : HasDerivAt profile profile' (‖x - center‖ ^ 2)) :
    S.tangentialDivergence (squaredRadiusRadialVectorField center profile) x =
      (n : ℝ) * profile (‖x - center‖ ^ 2) +
        2 * profile' * ‖S.projection (x - center)‖ ^ 2 :=
  S.tangentialTrace_fderiv_squaredRadiusRadialVectorField hprofile

theorem continuous_tangentialDivergence {U : Opens E} (X : TestFunction U E 1) :
    Continuous fun z : E × Grassmannian E n => z.2.tangentialDivergence X z.1 := by
  have hD : Continuous (fderiv ℝ (X : E → E)) :=
    (X.contDiff.fderiv_right (m := 0) (by norm_num)).continuous
  have h : Continuous fun z : E × Grassmannian E n =>
      (z.2, fderiv ℝ (X : E → E) z.1) := by
    fun_prop
  exact continuous_tangentialTrace_apply.comp h

theorem support_tangentialDivergence_subset {U : Opens E} (X : TestFunction U E 1) :
    support (fun z : E × Grassmannian E n => z.2.tangentialDivergence X z.1) ⊆
      tsupport X ×ˢ Set.univ := by
  intro z hz
  refine ⟨?_, Set.mem_univ _⟩
  apply tsupport_fderiv_subset ℝ
  apply subset_tsupport (fderiv ℝ (X : E → E))
  intro hD
  apply hz
  simp [tangentialDivergence, hD]

end Grassmannian

namespace Varifold

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

theorem integrable_tangentialDivergence (V : Varifold E n) {U : Opens E}
    (X : TestFunction U E 1) :
    Integrable (fun z : E × Grassmannian E n =>
      z.2.tangentialDivergence X z.1) V.toMeasure := by
  rw [← integrableOn_iff_integrable_of_support_subset
    (Grassmannian.support_tangentialDivergence_subset X)]
  exact (Grassmannian.continuous_tangentialDivergence X).continuousOn.integrableOn_compact
    (X.hasCompactSupport.prod isCompact_univ)

private theorem integrable_tangentialDivergence_supportedIn (V : Varifold E n)
    {K : Compacts E} (X : ContDiffMapSupportedIn E E 1 K) :
    Integrable (fun z : E × Grassmannian E n =>
      z.2.tangentialDivergence X z.1) V.toMeasure := by
  let X' : TestFunction (⊤ : Opens E) E 1 :=
    TestFunction.ofSupportedIn (by simp) X
  simpa only [X', TestFunction.coe_ofSupportedIn] using
    integrable_tangentialDivergence V X'

private def firstVariationOnCompact (V : Varifold E n) (K : Compacts E) :
    ContDiffMapSupportedIn E E 1 K →L[ℝ] ℝ :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ
    (fun X => ∫ z : E × Grassmannian E n,
      z.2.tangentialDivergence X z.1 ∂V.toMeasure)
    (fun X Y => by
      rw [← integral_add
        (integrable_tangentialDivergence_supportedIn V X)
        (integrable_tangentialDivergence_supportedIn V Y)]
      apply integral_congr_ae
      filter_upwards [] with z
      change z.2.tangentialTrace (fderiv ℝ (X + Y : E → E) z.1) =
        z.2.tangentialTrace (fderiv ℝ (X : E → E) z.1) +
          z.2.tangentialTrace (fderiv ℝ (Y : E → E) z.1)
      rw [fderiv_add
        (X.contDiff.differentiable (by norm_num)).differentiableAt
        (Y.contDiff.differentiable (by norm_num)).differentiableAt, map_add])
    (fun c X => by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with z
      change z.2.tangentialTrace (fderiv ℝ (c • (X : E → E)) z.1) =
        c • z.2.tangentialTrace (fderiv ℝ (X : E → E) z.1)
      rw [congrFun (fderiv_const_smul_field c) z.1, Pi.smul_apply, map_smul])
    ⟨{1}, ‖ContinuousLinearMap.trace ℝ E‖ *
        V.toMeasure.real ((K : Set E) ×ˢ (Set.univ : Set (Grassmannian E n))),
      by positivity, fun X => by
        have hzero : ∀ z : E × Grassmannian E n,
            z ∉ (K : Set E) ×ˢ (Set.univ : Set (Grassmannian E n)) →
              z.2.tangentialDivergence X z.1 = 0 := by
          intro z hz
          have hzK : z.1 ∉ (K : Set E) := by
            intro hzK
            exact hz ⟨hzK, Set.mem_univ _⟩
          have hD : fderiv ℝ (X : E → E) z.1 = 0 := by
            rw [← congrFun (ContDiffMapSupportedIn.fderivCLM_apply_of_le
              (n := 1) (k := 0) ℝ X (by norm_num)) z.1]
            exact (ContDiffMapSupportedIn.fderivCLM ℝ 1 0 X).zero_on_compl hzK
          simp [Grassmannian.tangentialDivergence, hD]
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
        calc
          ‖∫ z : E × Grassmannian E n in
              (K : Set E) ×ˢ (Set.univ : Set (Grassmannian E n)),
              z.2.tangentialDivergence X z.1 ∂V.toMeasure‖ ≤
              (‖ContinuousLinearMap.trace ℝ E‖ *
                ContDiffMapSupportedIn.seminorm ℝ E E 1 K 1 X) *
                V.toMeasure.real ((K : Set E) ×ˢ
                  (Set.univ : Set (Grassmannian E n))) := by
            apply norm_setIntegral_le_of_norm_le_const
              ((K.2.prod isCompact_univ).measure_lt_top)
            intro z hz
            apply (z.2.norm_tangentialTrace_le (fderiv ℝ (X : E → E) z.1)).trans
            gcongr
            rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (X : E → E)]
            exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ
              (by norm_num)
          _ = (‖ContinuousLinearMap.trace ℝ E‖ *
              V.toMeasure.real ((K : Set E) ×ˢ
                (Set.univ : Set (Grassmannian E n)))) *
              ContDiffMapSupportedIn.seminorm ℝ E E 1 K 1 X := by ring
          _ = (‖ContinuousLinearMap.trace ℝ E‖ *
              V.toMeasure.real ((K : Set E) ×ˢ
                (Set.univ : Set (Grassmannian E n)))) *
              (({1} : Finset ℕ).sup fun i =>
                ContDiffMapSupportedIn.seminorm ℝ E E 1 K i) X := by simp⟩

def firstVariation (V : Varifold E n) (U : Opens E) :
    TestFunction U E 1 →L[ℝ] ℝ :=
  TestFunction.limitCLM ℝ
    (fun X => ∫ z : E × Grassmannian E n,
      z.2.tangentialDivergence X z.1 ∂V.toMeasure)
    (fun K _ => firstVariationOnCompact V K)
    (fun K hKU X => by
      change (∫ z : E × Grassmannian E n,
        z.2.tangentialDivergence (TestFunction.ofSupportedIn hKU X) z.1 ∂V.toMeasure) =
        ∫ z : E × Grassmannian E n,
          z.2.tangentialDivergence X z.1 ∂V.toMeasure
      rw [TestFunction.coe_ofSupportedIn])

@[simp]
theorem firstVariation_apply (V : Varifold E n) (U : Opens E)
    (X : TestFunction U E 1) :
    V.firstVariation U X = ∫ z : E × Grassmannian E n,
      z.2.tangentialDivergence X z.1 ∂V.toMeasure :=
  by rw [firstVariation, TestFunction.limitCLM_apply]

@[simp]
theorem firstVariation_zero (U : Opens E) :
    (0 : Varifold E n).firstVariation U = 0 := by
  ext X
  simp

@[simp]
theorem firstVariation_add (V W : Varifold E n) (U : Opens E) :
    (V + W).firstVariation U = V.firstVariation U + W.firstVariation U := by
  ext X
  rw [firstVariation_apply, toMeasure_add,
    integral_add_measure (integrable_tangentialDivergence V X)
      (integrable_tangentialDivergence W X)]
  rfl

@[simp]
theorem firstVariation_smul (c : ℝ≥0) (V : Varifold E n) (U : Opens E) :
    (c • V).firstVariation U = (c : ℝ) • V.firstVariation U := by
  ext X
  rw [firstVariation_apply, toMeasure_smul, integral_smul_nnreal_measure]
  rfl

def IsStationaryOn (V : Varifold E n) (U : Opens E) : Prop :=
  V.firstVariation U = 0

@[simp]
theorem isStationaryOn_zero (U : Opens E) :
    (0 : Varifold E n).IsStationaryOn U := by
  simp [IsStationaryOn]

theorem IsStationaryOn.add {V W : Varifold E n} {U : Opens E}
    (hV : V.IsStationaryOn U) (hW : W.IsStationaryOn U) :
    (V + W).IsStationaryOn U := by
  rw [IsStationaryOn, firstVariation_add, hV, hW, add_zero]

theorem IsStationaryOn.smul {V : Varifold E n} {U : Opens E}
    (hV : V.IsStationaryOn U) (c : ℝ≥0) :
    (c • V).IsStationaryOn U := by
  rw [IsStationaryOn, firstVariation_smul, hV, smul_zero]

theorem IsStationaryOn.firstVariation_eq_zero {V : Varifold E n} {U : Opens E}
    (hV : V.IsStationaryOn U) (X : TestFunction U E 1) :
    V.firstVariation U X = 0 := by
  rw [hV]
  rfl

theorem IsStationaryOn.integral_tangentialDivergence_eq_zero
    {V : Varifold E n} {U : Opens E} (hV : V.IsStationaryOn U)
    (X : TestFunction U E 1) :
    ∫ z : E × Grassmannian E n,
      z.2.tangentialDivergence X z.1 ∂V.toMeasure = 0 := by
  simpa using hV.firstVariation_eq_zero X

end Varifold
