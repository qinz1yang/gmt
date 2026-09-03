import GMT.Measure.Density
import GMT.Varifold.FirstVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.Monotone

open Filter Function Metric Set TopologicalSpace
open scoped Distributions ENNReal Interval MeasureTheory Topology

noncomputable section

namespace Grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

-- Simon, Chapter 4, formulas (3.6) and (3.10), pp. 90-91: the radial tilt kernel.
def radialTilt (S : Grassmannian E n) (center x : E) : ℝ≥0∞ :=
  ENNReal.ofReal
    (‖S.perpendicularProjection (x - center)‖ ^ 2 / ‖x - center‖ ^ (n + 2))

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_radialTilt (center : E) :
    Measurable fun z : E × Grassmannian E n => z.2.radialTilt center z.1 := by
  apply Measurable.ennreal_ofReal
  apply Measurable.div
  · exact (continuous_perpendicularProjection_apply.comp
      (continuous_snd.prodMk (continuous_fst.sub continuous_const))).norm.pow 2 |>.measurable
  · exact (continuous_fst.sub continuous_const).norm.pow (n + 2) |>.measurable

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem radialTilt_zero_dim (S : Grassmannian E 0) {center x : E} (h : x ≠ center) :
    S.radialTilt center x = 1 := by
  have hsubspace : S.subspace = ⊥ :=
    Submodule.finrank_eq_zero.mp S.finrank_subspace
  have hperpendicular :
      S.perpendicularProjection = ContinuousLinearMap.id ℝ E := by
    rw [S.perpendicularProjection_eq]
    simp only [hsubspace, Submodule.bot_orthogonal_eq_top, Submodule.starProjection_top]
  have hnorm : ‖x - center‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  rw [radialTilt, hperpendicular, ContinuousLinearMap.id_apply]
  simp [hnorm]

end Grassmannian

namespace Varifold

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

-- Simon, Chapter 4, formula (3.3), p. 90: stationary radial test-field identity.
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

-- Simon, Chapter 4, formula (3.3), p. 90: perpendicular-projection form of the identity.
theorem IsStationaryOn.integral_squaredRadiusRadial_perpendicular_eq_zero
    {V : Varifold E n} {U : Opens E} (hV : V.IsStationaryOn U)
    {center : E} {profile : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall center R ⊆ U) (hprofile : ContDiff ℝ 1 profile)
    (hzero : ∀ t, R ^ 2 < t → profile t = 0) :
    ∫ z : E × Grassmannian E n,
        ((n : ℝ) * profile (‖z.1 - center‖ ^ 2) +
          2 * ‖z.1 - center‖ ^ 2 * deriv profile (‖z.1 - center‖ ^ 2) -
            2 * deriv profile (‖z.1 - center‖ ^ 2) *
              ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2) ∂V.toMeasure = 0 := by
  rw [← hV.integral_squaredRadiusRadial_eq_zero hR hball hprofile hzero]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [z.2.norm_sq_projection_add_norm_sq_perpendicularProjection (z.1 - center)]
  ring

private def smoothPositivePart (a t : ℝ) : ℝ :=
  a + Real.smoothTransition ((t - a) / a) * (t - a)

private theorem smoothPositivePart_pos {a : ℝ} (ha : 0 < a) (t : ℝ) :
    0 < smoothPositivePart a t := by
  unfold smoothPositivePart
  by_cases ht : t ≤ a
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ht) ha.le)]
    simpa using ha
  · have ht' : 0 ≤ t - a := sub_nonneg.mpr (le_of_not_ge ht)
    nlinarith [Real.smoothTransition.nonneg ((t - a) / a)]

private theorem smoothPositivePart_eq_self {a t : ℝ} (ha : 0 < a)
    (ht : 2 * a ≤ t) : smoothPositivePart a t = t := by
  unfold smoothPositivePart
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ ha]
    linarith

private theorem le_smoothPositivePart {a : ℝ} (ha : 0 < a) (t : ℝ) :
    a ≤ smoothPositivePart a t := by
  unfold smoothPositivePart
  by_cases ht : t ≤ a
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ht) ha.le)]
    simp
  · have ht' : 0 ≤ t - a := sub_nonneg.mpr (le_of_not_ge ht)
    exact le_add_of_nonneg_right (mul_nonneg (Real.smoothTransition.nonneg _) ht')

private theorem smoothPositivePart_contDiff (a : ℝ) :
    ContDiff ℝ 1 (smoothPositivePart a) := by
  unfold smoothPositivePart
  fun_prop

private def smoothPowerExtension (a p t : ℝ) : ℝ :=
  smoothPositivePart a t ^ p

private theorem smoothPowerExtension_contDiff {a p : ℝ} (ha : 0 < a) :
    ContDiff ℝ 1 (smoothPowerExtension a p) := by
  unfold smoothPowerExtension
  exact (smoothPositivePart_contDiff a).rpow_const_of_ne
    (fun t => (smoothPositivePart_pos ha t).ne')

private theorem smoothPowerExtension_eq_rpow {a p t : ℝ} (ha : 0 < a)
    (ht : 2 * a ≤ t) : smoothPowerExtension a p t = t ^ p := by
  rw [smoothPowerExtension, smoothPositivePart_eq_self ha ht]

private def smoothAnnularKernel (a b δ p t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a) / δ) *
    Real.smoothTransition ((b + δ - t) / δ) *
      smoothPowerExtension (a / 2) p t

private theorem smoothAnnularKernel_contDiff {a b δ p : ℝ} (ha : 0 < a) :
    ContDiff ℝ 1 (smoothAnnularKernel a b δ p) := by
  unfold smoothAnnularKernel
  exact ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
      (smoothPowerExtension_contDiff (half_pos ha))

private theorem smoothAnnularKernel_eq_zero_of_outer_le {a b δ p t : ℝ}
    (hδ : 0 < δ) (ht : b + δ ≤ t) :
    smoothAnnularKernel a b δ p t = 0 := by
  unfold smoothAnnularKernel
  rw [show Real.smoothTransition ((b + δ - t) / δ) = 0 by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le]
  ring

private theorem smoothAnnularKernel_nonneg {a b δ p t : ℝ} (ha : 0 < a) :
    0 ≤ smoothAnnularKernel a b δ p t := by
  unfold smoothAnnularKernel smoothPowerExtension
  exact mul_nonneg
    (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    (Real.rpow_nonneg (smoothPositivePart_pos (half_pos ha) t).le _)

private theorem smoothAnnularKernel_le {a b δ p t : ℝ} (ha : 0 < a)
    (hp : p ≤ 0) : smoothAnnularKernel a b δ p t ≤ (a / 2) ^ p := by
  calc
    smoothAnnularKernel a b δ p t ≤
        1 * Real.smoothTransition ((b + δ - t) / δ) *
          smoothPowerExtension (a / 2) p t := by
      unfold smoothAnnularKernel
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _)
      · unfold smoothPowerExtension
        exact Real.rpow_nonneg (smoothPositivePart_pos (half_pos ha) t).le _
    _ ≤ 1 * 1 * smoothPowerExtension (a / 2) p t := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) zero_le_one
      · unfold smoothPowerExtension
        exact Real.rpow_nonneg (smoothPositivePart_pos (half_pos ha) t).le _
    _ = smoothPositivePart (a / 2) t ^ p := by
      simp [smoothPowerExtension]
    _ ≤ (a / 2) ^ p :=
      Real.rpow_le_rpow_of_nonpos (half_pos ha)
        (le_smoothPositivePart (half_pos ha) t) hp

private def sharpAnnularKernel (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Ioc a b).indicator (fun s => s ^ (-((n : ℝ) + 2) / 2)) t

private def sharpAnnularProfile (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  -(1 / 2) * ∫ s in b..t, sharpAnnularKernel a b n s

private theorem integrable_sharpAnnularKernel {a b : ℝ} {n : ℕ} (ha : 0 < a) :
    Integrable (sharpAnnularKernel a b n) := by
  change Integrable ((Ioc a b).indicator fun s => s ^ (-((n : ℝ) + 2) / 2))
  rw [integrable_indicator_iff measurableSet_Ioc]
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact continuousOn_id.rpow_const fun t ht => Or.inl (ha.trans_le ht.1).ne'

private theorem integral_sharpAnnularKernel_outer {a b c t : ℝ} {n : ℕ}
    (ha : 0 < a) (hbc : b ≤ c) :
    (∫ s in c..t, sharpAnnularKernel a b n s) =
      ∫ s in b..t, sharpAnnularKernel a b n s := by
  have hint := integrable_sharpAnnularKernel (b := b) (n := n) ha
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint.intervalIntegrable (a := b) (b := c))
    (hint.intervalIntegrable (a := c) (b := t))
  have hzero : (∫ s in b..c, sharpAnnularKernel a b n s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with s hs
    rw [uIoc_of_le hbc] at hs
    rw [sharpAnnularKernel, indicator_of_notMem]
    exact fun h => (not_le_of_gt hs.1) h.2
  rw [hzero, zero_add] at hadd
  exact hadd

private theorem integral_sharpAnnularKernel_of_le {a b t : ℝ} {n : ℕ}
    (ht : t ≤ a) (hab : a ≤ b) :
    (∫ s in t..b, sharpAnnularKernel a b n s) =
      ∫ s in a..b, s ^ (-((n : ℝ) + 2) / 2) := by
  rw [intervalIntegral.integral_of_le (ht.trans hab),
    intervalIntegral.integral_of_le hab]
  simp only [sharpAnnularKernel]
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hinter : Ioc t b ∩ Ioc a b = Ioc a b := by
    ext s
    simp only [mem_inter_iff, mem_Ioc]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨ht.trans_lt h.1, h.2⟩, h⟩
  rw [inter_comm, hinter]

private theorem sharpAnnularProfile_of_mem {a b t : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n) (ht : t ∈ Ioc a b) :
    sharpAnnularProfile a b n t =
      (t ^ (-(n : ℝ) / 2) - b ^ (-(n : ℝ) / 2)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sharpAnnularProfile, intervalIntegral.integral_symm]
  have hkernel : (∫ s in t..b, sharpAnnularKernel a b n s) =
      ∫ s in t..b, s ^ (-((n : ℝ) + 2) / 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [sharpAnnularKernel, indicator_of_mem]
    rw [uIcc_of_le ht.2] at hs
    exact ⟨ht.1.trans_le hs.1, hs.2⟩
  rw [hkernel, integral_rpow]
  · field_simp [hn']
    ring_nf
  · right
    constructor
    · intro h
      apply hn'
      linarith
    · rw [uIcc_of_le ht.2]
      intro hzero
      linarith [hzero.1, ht.1]

private theorem sharpAnnularProfile_of_le {a b t : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n) (ht : t ≤ a) (hab : a ≤ b) :
    sharpAnnularProfile a b n t =
      (a ^ (-(n : ℝ) / 2) - b ^ (-(n : ℝ) / 2)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sharpAnnularProfile, intervalIntegral.integral_symm,
    integral_sharpAnnularKernel_of_le ht hab, integral_rpow]
  · field_simp [hn']
    ring_nf
  · right
    constructor
    · intro h
      apply hn'
      linarith
    · rw [uIcc_of_le hab]
      intro hzero
      linarith [hzero.1]

private theorem sharpAnnularProfile_of_outer_lt {a b t : ℝ} {n : ℕ}
    (ht : b < t) : sharpAnnularProfile a b n t = 0 := by
  unfold sharpAnnularProfile
  rw [intervalIntegral.integral_zero_ae]
  · ring
  · filter_upwards [] with s hs
    rw [uIoc_of_le ht.le] at hs
    rw [sharpAnnularKernel, indicator_of_notMem]
    exact fun h => (not_le_of_gt hs.1) h.2

private theorem mul_sharpAnnularKernel_of_mem {a b t : ℝ} {n : ℕ}
    (ha : 0 < a) (ht : t ∈ Ioc a b) :
    t * sharpAnnularKernel a b n t = t ^ (-(n : ℝ) / 2) := by
  rw [sharpAnnularKernel, indicator_of_mem ht]
  calc
    t * t ^ (-((n : ℝ) + 2) / 2) =
        t ^ (1 : ℝ) * t ^ (-((n : ℝ) + 2) / 2) := by rw [Real.rpow_one]
    _ = t ^ ((1 : ℝ) + (-((n : ℝ) + 2) / 2)) :=
      (Real.rpow_add (ha.trans ht.1) _ _).symm
    _ = t ^ (-(n : ℝ) / 2) := by congr 1; ring

private def sharpStationaryIntegrand (a b : ℝ) (n : ℕ) (t q : ℝ) : ℝ :=
  (n : ℝ) * sharpAnnularProfile a b n t - t * sharpAnnularKernel a b n t +
    sharpAnnularKernel a b n t * q

private theorem sharpStationaryIntegrand_eq {a b t q : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n) (hab : a < b) :
    sharpStationaryIntegrand a b n t q =
      if t ≤ a then a ^ (-(n : ℝ) / 2) - b ^ (-(n : ℝ) / 2)
      else if t ≤ b then -b ^ (-(n : ℝ) / 2) +
        t ^ (-((n : ℝ) + 2) / 2) * q
      else 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases hta : t ≤ a
  · rw [if_pos hta, sharpStationaryIntegrand,
      sharpAnnularProfile_of_le ha hn hta hab.le, sharpAnnularKernel,
      indicator_of_notMem]
    · field_simp [hn']
      ring
    · exact fun ht => (not_lt_of_ge hta) ht.1
  · have hat : a < t := lt_of_not_ge hta
    rw [if_neg hta]
    by_cases htb : t ≤ b
    · have ht : t ∈ Ioc a b := ⟨hat, htb⟩
      rw [if_pos htb, sharpStationaryIntegrand,
        sharpAnnularProfile_of_mem ha hn ht,
        mul_sharpAnnularKernel_of_mem ha ht,
        sharpAnnularKernel, indicator_of_mem ht]
      field_simp [hn']
      ring_nf
    · have hbt : b < t := lt_of_not_ge htb
      rw [if_neg htb, sharpStationaryIntegrand,
        sharpAnnularProfile_of_outer_lt hbt, sharpAnnularKernel,
        indicator_of_notMem]
      · ring
      · exact fun ht => (not_le_of_gt hbt) ht.2

private def smoothingWidth (b c : ℝ) (i : ℕ) : ℝ :=
  (c - b) / (i + 1 : ℝ)

private theorem smoothingWidth_pos {b c : ℝ} (hbc : b < c) (i : ℕ) :
    0 < smoothingWidth b c i := by
  unfold smoothingWidth
  positivity

private theorem smoothingWidth_le {b c : ℝ} (hbc : b ≤ c) (i : ℕ) :
    smoothingWidth b c i ≤ c - b := by
  unfold smoothingWidth
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i + 1 : ℝ))]
  have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)
  norm_num [Nat.cast_add, Nat.cast_one]
  nlinarith

private theorem tendsto_smoothingWidth (b c : ℝ) :
    Tendsto (smoothingWidth b c) atTop (𝓝 0) := by
  unfold smoothingWidth
  simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using
    tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem tendsto_smoothAnnularKernel {a b c t : ℝ} {n : ℕ}
    (ha : 0 < a) (hbc : b < c) :
    Tendsto (fun i => smoothAnnularKernel a b (smoothingWidth b c i)
      (-((n : ℝ) + 2) / 2) t) atTop
      (𝓝 (sharpAnnularKernel a b n t)) := by
  by_cases hta : t ≤ a
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with i
    rw [sharpAnnularKernel, indicator_of_notMem]
    · unfold smoothAnnularKernel
      rw [show Real.smoothTransition ((t - a) / smoothingWidth b c i) = 0 by
        apply Real.smoothTransition.zero_of_nonpos
        exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hta)
          (smoothingWidth_pos hbc i).le]
      ring
    · exact fun ht => (not_lt_of_ge hta) ht.1
  · have hat : a < t := lt_of_not_ge hta
    by_cases htb : t ≤ b
    · have ht : t ∈ Ioc a b := ⟨hat, htb⟩
      have hevent : ∀ᶠ i in atTop, smoothingWidth b c i < t - a :=
        (tendsto_smoothingWidth b c).eventually (Iio_mem_nhds (sub_pos.mpr hat))
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with i hi
      rw [sharpAnnularKernel, indicator_of_mem ht]
      unfold smoothAnnularKernel
      rw [show Real.smoothTransition ((t - a) / smoothingWidth b c i) = 1 by
        apply Real.smoothTransition.one_of_one_le
        rw [le_div_iff₀ (smoothingWidth_pos hbc i)]
        simpa using hi.le]
      rw [show Real.smoothTransition
          ((b + smoothingWidth b c i - t) / smoothingWidth b c i) = 1 by
        apply Real.smoothTransition.one_of_one_le
        rw [le_div_iff₀ (smoothingWidth_pos hbc i)]
        linarith]
      rw [smoothPowerExtension_eq_rpow (half_pos ha)]
      · ring
      · linarith
    · have hbt : b < t := lt_of_not_ge htb
      have hevent : ∀ᶠ i in atTop, smoothingWidth b c i < t - b :=
        (tendsto_smoothingWidth b c).eventually (Iio_mem_nhds (sub_pos.mpr hbt))
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with i hi
      rw [sharpAnnularKernel, indicator_of_notMem]
      · unfold smoothAnnularKernel
        rw [show Real.smoothTransition
            ((b + smoothingWidth b c i - t) / smoothingWidth b c i) = 0 by
          apply Real.smoothTransition.zero_of_nonpos
          apply div_nonpos_of_nonpos_of_nonneg
          · linarith
          · exact (smoothingWidth_pos hbc i).le]
        ring
      · exact fun ht => (not_le_of_gt hbt) ht.2

private def smoothAnnularProfile (a b c δ p t : ℝ) : ℝ :=
  -(1 / 2) * ∫ s in c..t, smoothAnnularKernel a b δ p s

private theorem hasDerivAt_smoothAnnularProfile {a b c δ p t : ℝ} (ha : 0 < a) :
    HasDerivAt (smoothAnnularProfile a b c δ p)
      (-(1 / 2) * smoothAnnularKernel a b δ p t) t := by
  unfold smoothAnnularProfile
  exact ((smoothAnnularKernel_contDiff (b := b) ha).continuous.integral_hasStrictDerivAt
    c t).hasDerivAt.const_mul _

private theorem smoothAnnularProfile_contDiff {a b c δ p : ℝ} (ha : 0 < a) :
    ContDiff ℝ 1 (smoothAnnularProfile a b c δ p) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_smoothAnnularProfile (b := b) ha).differentiableAt,
    ?_⟩
  have hderiv : deriv (smoothAnnularProfile a b c δ p) =
      fun t => -(1 / 2) * smoothAnnularKernel a b δ p t := by
    funext t
    exact (hasDerivAt_smoothAnnularProfile (b := b) ha).deriv
  rw [hderiv]
  exact continuous_const.mul (smoothAnnularKernel_contDiff (b := b) ha).continuous

private theorem smoothAnnularProfile_eq_zero_of_outer_le
    {a b c δ p t : ℝ} (hδ : 0 < δ) (hbc : b + δ ≤ c) (hct : c ≤ t) :
    smoothAnnularProfile a b c δ p t = 0 := by
  unfold smoothAnnularProfile
  rw [intervalIntegral.integral_of_le hct]
  have hzero : (fun s => smoothAnnularKernel a b δ p s) =ᵐ[
      volume.restrict (Ioc c t)] 0 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    exact smoothAnnularKernel_eq_zero_of_outer_le hδ (hbc.trans hs.1.le)
  rw [integral_eq_zero_of_ae hzero]
  ring

private theorem tendsto_smoothAnnularProfile {a b c t : ℝ} {n : ℕ}
    (ha : 0 < a) (hbc : b < c) :
    Tendsto (fun i => smoothAnnularProfile a b c (smoothingWidth b c i)
      (-((n : ℝ) + 2) / 2) t) atTop
      (𝓝 (sharpAnnularProfile a b n t)) := by
  let p : ℝ := -((n : ℝ) + 2) / 2
  have hp : p ≤ 0 := by
    dsimp [p]
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have htend := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := c) (b := t) (μ := volume)
    (fun _ => (a / 2) ^ p)
    (l := atTop)
    (F := fun i s => smoothAnnularKernel a b (smoothingWidth b c i) p s)
    (f := sharpAnnularKernel a b n)
    (Eventually.of_forall fun i =>
      (smoothAnnularKernel_contDiff (b := b) (δ := smoothingWidth b c i)
        (p := p) ha).continuous.aestronglyMeasurable)
    (Eventually.of_forall fun i => Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smoothAnnularKernel_nonneg ha)]
      exact smoothAnnularKernel_le ha hp)
    intervalIntegrable_const
    (Eventually.of_forall fun s _ => by
      simpa [p] using tendsto_smoothAnnularKernel (n := n) (t := s) ha hbc)
  have hmul : Tendsto
      (fun i => -(1 / 2) * ∫ s in c..t,
        smoothAnnularKernel a b (smoothingWidth b c i) p s) atTop
      (𝓝 (-(1 / 2) * ∫ s in c..t, sharpAnnularKernel a b n s)) :=
    tendsto_const_nhds.mul htend
  rw [integral_sharpAnnularKernel_outer ha hbc.le] at hmul
  simpa only [smoothAnnularProfile, sharpAnnularProfile, p] using hmul

private def smoothStationaryIntegrand
    (a b c δ : ℝ) (n : ℕ) (t q : ℝ) : ℝ :=
  (n : ℝ) * smoothAnnularProfile a b c δ (-((n : ℝ) + 2) / 2) t -
    t * smoothAnnularKernel a b δ (-((n : ℝ) + 2) / 2) t +
      smoothAnnularKernel a b δ (-((n : ℝ) + 2) / 2) t * q

private theorem tendsto_smoothStationaryIntegrand
    {a b c t q : ℝ} {n : ℕ} (ha : 0 < a) (hbc : b < c) :
    Tendsto (fun i => smoothStationaryIntegrand a b c (smoothingWidth b c i) n t q)
      atTop (𝓝 (sharpStationaryIntegrand a b n t q)) := by
  unfold smoothStationaryIntegrand sharpStationaryIntegrand
  exact ((tendsto_const_nhds.mul (tendsto_smoothAnnularProfile (n := n) (t := t) ha hbc)).sub
    (tendsto_const_nhds.mul (tendsto_smoothAnnularKernel (n := n) (t := t) ha hbc))).add
      ((tendsto_smoothAnnularKernel (n := n) (t := t) ha hbc).mul tendsto_const_nhds)

private theorem abs_smoothAnnularProfile_le {a b c δ p t : ℝ}
    (ha : 0 < a) (hp : p ≤ 0) (ht0 : 0 ≤ t) (htc : t ≤ c) :
    |smoothAnnularProfile a b c δ p t| ≤
      (1 / 2) * ((a / 2) ^ p * c) := by
  have hM : 0 ≤ (a / 2) ^ p := Real.rpow_nonneg (half_pos ha).le _
  have hint : ‖∫ s in c..t, smoothAnnularKernel a b δ p s‖ ≤
      (a / 2) ^ p * |t - c| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (smoothAnnularKernel_nonneg ha)]
    exact smoothAnnularKernel_le ha hp
  have habs : |t - c| ≤ c := by
    rw [abs_of_nonpos (sub_nonpos.mpr htc)]
    linarith
  unfold smoothAnnularProfile
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2) * |∫ s in c..t, smoothAnnularKernel a b δ p s| ≤
        (1 / 2) * ((a / 2) ^ p * |t - c|) := by
      gcongr
      simpa only [Real.norm_eq_abs] using hint
    _ ≤ (1 / 2) * ((a / 2) ^ p * c) := by
      gcongr

private theorem abs_smoothStationaryIntegrand_le
    {a b c t q : ℝ} {n i : ℕ} (ha : 0 < a) (ht0 : 0 ≤ t)
    (htc : t ≤ c) (hq0 : 0 ≤ q) (hqt : q ≤ t) :
    |smoothStationaryIntegrand a b c (smoothingWidth b c i) n t q| ≤
      (n : ℝ) * ((1 / 2) * ((a / 2) ^ (-((n : ℝ) + 2) / 2) * c)) +
        c * (a / 2) ^ (-((n : ℝ) + 2) / 2) +
          (a / 2) ^ (-((n : ℝ) + 2) / 2) * c := by
  let p : ℝ := -((n : ℝ) + 2) / 2
  have hp : p ≤ 0 := by
    dsimp [p]
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hk0 : 0 ≤ smoothAnnularKernel a b (smoothingWidth b c i) p t :=
    smoothAnnularKernel_nonneg ha
  have hk : smoothAnnularKernel a b (smoothingWidth b c i) p t ≤ (a / 2) ^ p :=
    smoothAnnularKernel_le ha hp
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have htri : |(n : ℝ) * smoothAnnularProfile a b c (smoothingWidth b c i) p t -
      t * smoothAnnularKernel a b (smoothingWidth b c i) p t +
        smoothAnnularKernel a b (smoothingWidth b c i) p t * q| ≤
      (n : ℝ) * |smoothAnnularProfile a b c (smoothingWidth b c i) p t| +
        t * smoothAnnularKernel a b (smoothingWidth b c i) p t +
          smoothAnnularKernel a b (smoothingWidth b c i) p t * q := by
    calc
      |(n : ℝ) * smoothAnnularProfile a b c (smoothingWidth b c i) p t -
          t * smoothAnnularKernel a b (smoothingWidth b c i) p t +
            smoothAnnularKernel a b (smoothingWidth b c i) p t * q| ≤
          |(n : ℝ) * smoothAnnularProfile a b c (smoothingWidth b c i) p t| +
            |t * smoothAnnularKernel a b (smoothingWidth b c i) p t| +
              |smoothAnnularKernel a b (smoothingWidth b c i) p t * q| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = (n : ℝ) * |smoothAnnularProfile a b c (smoothingWidth b c i) p t| +
          t * smoothAnnularKernel a b (smoothingWidth b c i) p t +
            smoothAnnularKernel a b (smoothingWidth b c i) p t * q := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hn0, abs_of_nonneg ht0,
          abs_of_nonneg hk0, abs_of_nonneg hq0]
  unfold smoothStationaryIntegrand
  change |(n : ℝ) * smoothAnnularProfile a b c (smoothingWidth b c i) p t -
      t * smoothAnnularKernel a b (smoothingWidth b c i) p t +
        smoothAnnularKernel a b (smoothingWidth b c i) p t * q| ≤ _
  apply htri.trans
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left (abs_smoothAnnularProfile_le ha hp ht0 htc) hn0
    · exact (mul_le_mul_of_nonneg_left hk ht0).trans
        (mul_le_mul_of_nonneg_right htc (Real.rpow_nonneg (half_pos ha).le _))
  · exact (mul_le_mul_of_nonneg_right hk hq0).trans
      ((mul_le_mul_of_nonneg_left hqt (Real.rpow_nonneg (half_pos ha).le _)).trans
        (mul_le_mul_of_nonneg_left htc (Real.rpow_nonneg (half_pos ha).le _)))

private theorem sq_rpow_neg_half_nat {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (r ^ 2) ^ (-(m : ℝ) / 2) = r⁻¹ ^ m := by
  calc
    (r ^ 2) ^ (-(m : ℝ) / 2) =
        (r ^ (2 : ℝ)) ^ (-(m : ℝ) / 2) :=
      congrArg (fun x : ℝ => x ^ (-(m : ℝ) / 2)) (Real.rpow_natCast r 2).symm
    _ = r ^ ((2 : ℝ) * (-(m : ℝ) / 2)) :=
      (Real.rpow_mul hr.le _ _).symm
    _ = r ^ (-(m : ℝ)) := by congr 1; ring
    _ = r⁻¹ ^ (m : ℝ) := Real.rpow_neg_eq_inv_rpow _ _
    _ = r⁻¹ ^ m := Real.rpow_natCast _ _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem mem_closedBall_sqrt_iff {center y : E} {r : ℝ} (hr : 0 ≤ r) :
    y ∈ closedBall center √r ↔ ‖y - center‖ ^ 2 ≤ r := by
  rw [mem_closedBall, dist_eq_norm]
  constructor
  · intro h
    simpa only [Real.sq_sqrt hr] using
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg r)).2 h
  · intro h
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg r)).1
    simpa only [Real.sq_sqrt hr] using h

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_outer_closedBall {U : TopologicalSpace.Opens E}
    {center : E} {r : ℝ} (hr : 0 ≤ r) (hball : closedBall center r ⊆ U) :
    ∃ R, r < R ∧ closedBall center R ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall center r).exists_thickening_subset_open U.2 hball
  refine ⟨r + δ / 2, by linarith, ?_⟩
  calc
    closedBall center (r + δ / 2) ⊆ ball center (δ + r) :=
      Metric.closedBall_subset_ball (by linarith)
    _ = Metric.thickening δ (closedBall center r) :=
      (thickening_closedBall hδ hr center).symm
    _ ⊆ U := hthick

private theorem IsStationaryOn.integral_smoothStationaryIntegrand_eq_zero
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {a b c : ℝ} (ha : 0 < a) (hbc : b < c) (hc : 0 ≤ c)
    (hball : closedBall center √c ⊆ U) (i : ℕ) :
    ∫ z : E × Grassmannian E n,
      smoothStationaryIntegrand a b c (smoothingWidth b c i) n
        (‖z.1 - center‖ ^ 2)
        (‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2) ∂V.toMeasure = 0 := by
  let δ := smoothingWidth b c i
  let p : ℝ := -((n : ℝ) + 2) / 2
  have hδ : 0 < δ := smoothingWidth_pos hbc i
  have hδc : b + δ ≤ c := by
    dsimp [δ]
    linarith [smoothingWidth_le hbc.le i]
  have hstationary := hV.integral_squaredRadiusRadial_perpendicular_eq_zero
    (center := center) (profile := smoothAnnularProfile a b c δ p)
    (R := √c) (Real.sqrt_nonneg c) hball
    (smoothAnnularProfile_contDiff (b := b) ha)
    (fun t ht => by
      rw [Real.sq_sqrt hc] at ht
      exact smoothAnnularProfile_eq_zero_of_outer_le hδ hδc ht.le)
  calc
    ∫ z : E × Grassmannian E n,
        smoothStationaryIntegrand a b c (smoothingWidth b c i) n
          (‖z.1 - center‖ ^ 2)
          (‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2) ∂V.toMeasure =
      ∫ z : E × Grassmannian E n,
        ((n : ℝ) * smoothAnnularProfile a b c δ p (‖z.1 - center‖ ^ 2) +
          2 * ‖z.1 - center‖ ^ 2 *
              deriv (smoothAnnularProfile a b c δ p) (‖z.1 - center‖ ^ 2) -
            2 * deriv (smoothAnnularProfile a b c δ p) (‖z.1 - center‖ ^ 2) *
              ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2) ∂V.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [(hasDerivAt_smoothAnnularProfile (b := b) ha).deriv]
      dsimp [smoothStationaryIntegrand, δ, p]
      ring
    _ = 0 := hstationary

private theorem IsStationaryOn.integral_sharpStationaryIntegrand_eq_zero
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {a b c : ℝ} (ha : 0 < a) (hbc : b < c) (hc : 0 ≤ c)
    (hball : closedBall center √c ⊆ U) :
    ∫ z : E × Grassmannian E n,
      sharpStationaryIntegrand a b n (‖z.1 - center‖ ^ 2)
        (‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2) ∂V.toMeasure = 0 := by
  let K : Set (E × Grassmannian E n) := closedBall center √c ×ˢ Set.univ
  have hKmeas : MeasurableSet K := measurableSet_closedBall.prod MeasurableSet.univ
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact IsCompact.prod (isCompact_closedBall center √c) isCompact_univ
  let μK := V.toMeasure.restrict K
  let _ : IsFiniteMeasure μK := ⟨by
    change (V.toMeasure.restrict K) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact hKcompact.measure_lt_top⟩
  let F : ℕ → E × Grassmannian E n → ℝ := fun i z =>
    smoothStationaryIntegrand a b c (smoothingWidth b c i) n
      (‖z.1 - center‖ ^ 2)
      (‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2)
  let f : E × Grassmannian E n → ℝ := fun z =>
    sharpStationaryIntegrand a b n (‖z.1 - center‖ ^ 2)
      (‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2)
  have hFcont (i : ℕ) : Continuous (F i) := by
    have ht : Continuous fun z : E × Grassmannian E n => ‖z.1 - center‖ ^ 2 := by
      fun_prop
    have hq : Continuous fun z : E × Grassmannian E n =>
        ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 := by
      exact (Grassmannian.continuous_perpendicularProjection_apply.comp
        (continuous_snd.prodMk (continuous_fst.sub continuous_const))).norm.pow 2
    have hprofile := (smoothAnnularProfile_contDiff (b := b) (c := c)
      (δ := smoothingWidth b c i) (p := -((n : ℝ) + 2) / 2) ha).continuous.comp ht
    have hkernel := (smoothAnnularKernel_contDiff (b := b)
      (δ := smoothingWidth b c i) (p := -((n : ℝ) + 2) / 2) ha).continuous.comp ht
    exact ((continuous_const.mul hprofile).sub (ht.mul hkernel)).add (hkernel.mul hq)
  have hbound : ∃ C, ∀ᶠ i in atTop, ∀ᵐ z ∂μK, ‖F i z‖ ≤ C := by
    refine ⟨(n : ℝ) *
        ((1 / 2) * ((a / 2) ^ (-((n : ℝ) + 2) / 2) * c)) +
      c * (a / 2) ^ (-((n : ℝ) + 2) / 2) +
        (a / 2) ^ (-((n : ℝ) + 2) / 2) * c,
      Eventually.of_forall fun i => ?_⟩
    change ∀ᵐ z ∂V.toMeasure.restrict K, ‖F i z‖ ≤ _
    rw [ae_restrict_iff' hKmeas]
    filter_upwards [] with z hz
    rcases hz with ⟨hz, _⟩
    have hdist : dist z.1 center ≤ √c := hz
    have ht0 : 0 ≤ ‖z.1 - center‖ ^ 2 := sq_nonneg _
    have htc : ‖z.1 - center‖ ^ 2 ≤ c := by
      rw [← dist_eq_norm, ← Real.sq_sqrt hc]
      exact pow_le_pow_left₀ dist_nonneg hdist 2
    have hdecomp :=
      z.2.norm_sq_projection_add_norm_sq_perpendicularProjection (z.1 - center)
    have hq0 : 0 ≤ ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 := sq_nonneg _
    have hqt : ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 ≤
        ‖z.1 - center‖ ^ 2 := by nlinarith [sq_nonneg ‖z.2.projection (z.1 - center)‖]
    simpa only [Real.norm_eq_abs, F] using
      abs_smoothStationaryIntegrand_le (n := n) (i := i) ha ht0 htc hq0 hqt
  have htend : Tendsto (fun i => ∫ z, F i z ∂μK) atTop (𝓝 (∫ z, f z ∂μK)) :=
    tendsto_integral_filter_of_norm_le_const
      (Eventually.of_forall fun i => (hFcont i).aestronglyMeasurable)
      hbound
      (Eventually.of_forall fun z => by
        exact tendsto_smoothStationaryIntegrand (n := n)
          (t := ‖z.1 - center‖ ^ 2)
          (q := ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2) ha hbc)
  have hzero (i : ℕ) : ∫ z, F i z ∂μK = 0 := by
    have hfull := hV.integral_smoothStationaryIntegrand_eq_zero ha hbc hc hball i
    have hsupp : ∀ z : E × Grassmannian E n, z ∉ K → F i z = 0 := by
      intro z hz
      have hzball : z.1 ∉ closedBall center √c := by
        intro hzball
        exact hz ⟨hzball, Set.mem_univ _⟩
      have hct : c < ‖z.1 - center‖ ^ 2 := by
        have hdist : √c < dist z.1 center := by
          simpa only [mem_closedBall, not_le] using hzball
        rw [← dist_eq_norm, ← Real.sq_sqrt hc]
        exact (sq_lt_sq₀ (Real.sqrt_nonneg c) dist_nonneg).2 hdist
      have hδ := smoothingWidth_pos hbc i
      have hδc : b + smoothingWidth b c i ≤ c := by
        linarith [smoothingWidth_le hbc.le i]
      simp only [F]
      rw [smoothStationaryIntegrand,
        smoothAnnularProfile_eq_zero_of_outer_le hδ hδc hct.le,
        smoothAnnularKernel_eq_zero_of_outer_le hδ (hδc.trans hct.le)]
      ring
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp] at hfull
    exact hfull
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hlimit : (∫ z, f z ∂μK) = 0 := by
    apply tendsto_nhds_unique htend
    simpa only [hzero] using hconst
  have hsupp : ∀ z : E × Grassmannian E n, z ∉ K → f z = 0 := by
    intro z hz
    have hzball : z.1 ∉ closedBall center √c := by
      intro hzball
      exact hz ⟨hzball, Set.mem_univ _⟩
    have hct : c < ‖z.1 - center‖ ^ 2 := by
      have hdist : √c < dist z.1 center := by
        simpa only [mem_closedBall, not_le] using hzball
      rw [← dist_eq_norm, ← Real.sq_sqrt hc]
      exact (sq_lt_sq₀ (Real.sqrt_nonneg c) dist_nonneg).2 hdist
    have hbt : b < ‖z.1 - center‖ ^ 2 := hbc.trans hct
    simp only [f]
    rw [sharpStationaryIntegrand, sharpAnnularProfile_of_outer_lt hbt,
      sharpAnnularKernel, indicator_of_notMem]
    · ring
    · exact fun h => (not_le_of_gt hbt) h.2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  exact hlimit

private theorem IsStationaryOn.real_squared_monotonicity_identity
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {a b c : ℝ} (hn : 0 < n) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hball : closedBall center √c ⊆ U) :
    a ^ (-(n : ℝ) / 2) *
          V.toMeasure.real (closedBall center √a ×ˢ (Set.univ : Set (Grassmannian E n))) +
        ∫ z : E × Grassmannian E n in
          (closedBall center √b ×ˢ (Set.univ : Set (Grassmannian E n))) \
            (closedBall center √a ×ˢ (Set.univ : Set (Grassmannian E n))),
          (‖z.1 - center‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) *
            ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 ∂V.toMeasure =
      b ^ (-(n : ℝ) / 2) *
        V.toMeasure.real (closedBall center √b ×ˢ (Set.univ : Set (Grassmannian E n))) := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 ≤ c := (hb.trans hbc).le
  let A : Set (E × Grassmannian E n) :=
    closedBall center √a ×ˢ Set.univ
  let B : Set (E × Grassmannian E n) :=
    closedBall center √b ×ˢ Set.univ
  let D : Set (E × Grassmannian E n) := B \ A
  let t : E × Grassmannian E n → ℝ := fun z => ‖z.1 - center‖ ^ 2
  let q : E × Grassmannian E n → ℝ := fun z =>
    ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2
  let k : E × Grassmannian E n → ℝ := fun z =>
    t z ^ (-((n : ℝ) + 2) / 2) * q z
  have hAmeas : MeasurableSet A := measurableSet_closedBall.prod MeasurableSet.univ
  have hBmeas : MeasurableSet B := measurableSet_closedBall.prod MeasurableSet.univ
  have hDmeas : MeasurableSet D := hBmeas.diff hAmeas
  have hAcompact : IsCompact A := by
    dsimp [A]
    exact IsCompact.prod (isCompact_closedBall center √a) isCompact_univ
  have hBcompact : IsCompact B := by
    dsimp [B]
    exact IsCompact.prod (isCompact_closedBall center √b) isCompact_univ
  have htcont : Continuous t := by
    dsimp [t]
    fun_prop
  have hqcont : Continuous q := by
    dsimp [q]
    exact (Grassmannian.continuous_perpendicularProjection_apply.comp
      (continuous_snd.prodMk (continuous_fst.sub continuous_const))).norm.pow 2
  have hkmeas : Measurable k := by
    dsimp [k]
    exact (htcont.measurable.pow_const _).mul hqcont.measurable
  have hkint : IntegrableOn k D V.toMeasure := by
    let _ : IsFiniteMeasure (V.toMeasure.restrict D) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono sdiff_subset).trans_lt hBcompact.measure_lt_top⟩
    apply Integrable.of_bound hkmeas.aestronglyMeasurable
      (a ^ (-((n : ℝ) + 2) / 2) * b)
    rw [ae_restrict_iff' hDmeas]
    filter_upwards [] with z hz
    have hzB : z ∈ B := hz.1
    have hzA : z ∉ A := hz.2
    have hta : a < t z := by
      have : ¬t z ≤ a := by
        intro h
        apply hzA
        simpa only [A, mem_prod, mem_univ, and_true,
          mem_closedBall_sqrt_iff ha.le] using h
      exact lt_of_not_ge this
    have htb : t z ≤ b := by
      simpa only [B, mem_prod, mem_univ, and_true,
        mem_closedBall_sqrt_iff hb.le] using hzB
    have hq0 : 0 ≤ q z := by
      dsimp [q]
      positivity
    have hqt : q z ≤ t z := by
      have hdecomp :=
        z.2.norm_sq_projection_add_norm_sq_perpendicularProjection (z.1 - center)
      dsimp [q, t]
      nlinarith [sq_nonneg ‖z.2.projection (z.1 - center)‖]
    have hp : -((n : ℝ) + 2) / 2 ≤ 0 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hpow : t z ^ (-((n : ℝ) + 2) / 2) ≤
        a ^ (-((n : ℝ) + 2) / 2) :=
      Real.rpow_le_rpow_of_nonpos ha hta.le hp
    have hpow0 : 0 ≤ t z ^ (-((n : ℝ) + 2) / 2) :=
      Real.rpow_nonneg (le_trans ha.le hta.le) _
    dsimp only [k]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpow0 hq0)]
    exact (mul_le_mul_of_nonneg_right hpow hq0).trans
      ((mul_le_mul_of_nonneg_left hqt (Real.rpow_nonneg ha.le _)).trans
        (mul_le_mul_of_nonneg_left htb (Real.rpow_nonneg ha.le _)))
  have hAint : Integrable (A.indicator fun _ => a ^ (-(n : ℝ) / 2)) V.toMeasure := by
    rw [integrable_indicator_iff hAmeas]
    exact integrableOn_const hAcompact.measure_ne_top
  have hBint : Integrable (B.indicator fun _ => b ^ (-(n : ℝ) / 2)) V.toMeasure := by
    rw [integrable_indicator_iff hBmeas]
    exact integrableOn_const hBcompact.measure_ne_top
  have hDint : Integrable (D.indicator k) V.toMeasure := by
    rw [integrable_indicator_iff hDmeas]
    exact hkint
  have hpoint (z : E × Grassmannian E n) :
      sharpStationaryIntegrand a b n (t z) (q z) =
        A.indicator (fun _ => a ^ (-(n : ℝ) / 2)) z -
          B.indicator (fun _ => b ^ (-(n : ℝ) / 2)) z + D.indicator k z := by
    rw [sharpStationaryIntegrand_eq ha hn hab]
    by_cases hta : t z ≤ a
    · have hzA : z ∈ A := by
        simpa only [A, mem_prod, mem_univ, and_true,
          mem_closedBall_sqrt_iff ha.le] using hta
      have hzB : z ∈ B := by
        simpa only [B, mem_prod, mem_univ, and_true,
          mem_closedBall_sqrt_iff hb.le] using hta.trans hab.le
      have hzD : z ∉ D := fun hz => hz.2 hzA
      rw [if_pos hta, indicator_of_mem hzA, indicator_of_mem hzB,
        indicator_of_notMem hzD]
      ring
    · have hat : a < t z := lt_of_not_ge hta
      rw [if_neg hta]
      by_cases htb : t z ≤ b
      · have hzA : z ∉ A := by
          simpa only [A, mem_prod, mem_univ, and_true,
            mem_closedBall_sqrt_iff ha.le, not_le]
        have hzB : z ∈ B := by
          simpa only [B, mem_prod, mem_univ, and_true,
            mem_closedBall_sqrt_iff hb.le] using htb
        have hzD : z ∈ D := ⟨hzB, hzA⟩
        rw [if_pos htb, indicator_of_notMem hzA, indicator_of_mem hzB,
          indicator_of_mem hzD]
        dsimp only [k]
        ring
      · have hbt : b < t z := lt_of_not_ge htb
        have hzA : z ∉ A := by
          simpa only [A, mem_prod, mem_univ, and_true,
            mem_closedBall_sqrt_iff ha.le, not_le] using hat
        have hzB : z ∉ B := by
          simpa only [B, mem_prod, mem_univ, and_true,
            mem_closedBall_sqrt_iff hb.le, not_le] using hbt
        have hzD : z ∉ D := fun hz => hzB hz.1
        rw [if_neg htb, indicator_of_notMem hzA, indicator_of_notMem hzB,
          indicator_of_notMem hzD]
        ring
  have hzero := hV.integral_sharpStationaryIntegrand_eq_zero ha hbc hc hball
  have hsplit :
      ∫ z, sharpStationaryIntegrand a b n (t z) (q z) ∂V.toMeasure =
        ∫ z, A.indicator (fun _ => a ^ (-(n : ℝ) / 2)) z ∂V.toMeasure -
          ∫ z, B.indicator (fun _ => b ^ (-(n : ℝ) / 2)) z ∂V.toMeasure +
            ∫ z, D.indicator k z ∂V.toMeasure := by
    calc
      ∫ z, sharpStationaryIntegrand a b n (t z) (q z) ∂V.toMeasure =
          ∫ z, (A.indicator (fun _ => a ^ (-(n : ℝ) / 2)) z -
            B.indicator (fun _ => b ^ (-(n : ℝ) / 2)) z) + D.indicator k z
              ∂V.toMeasure := integral_congr_ae (Eventually.of_forall hpoint)
      _ = ∫ z, A.indicator (fun _ => a ^ (-(n : ℝ) / 2)) z -
            B.indicator (fun _ => b ^ (-(n : ℝ) / 2)) z ∂V.toMeasure +
          ∫ z, D.indicator k z ∂V.toMeasure :=
        integral_add (hAint.sub hBint) hDint
      _ = ∫ z, A.indicator (fun _ => a ^ (-(n : ℝ) / 2)) z ∂V.toMeasure -
            ∫ z, B.indicator (fun _ => b ^ (-(n : ℝ) / 2)) z ∂V.toMeasure +
          ∫ z, D.indicator k z ∂V.toMeasure := by rw [integral_sub hAint hBint]
  rw [hsplit, integral_indicator hAmeas, integral_indicator hBmeas,
    integral_indicator hDmeas, setIntegral_const, setIntegral_const] at hzero
  dsimp only [A, B, D, t, q, k] at hzero ⊢
  simp only [smul_eq_mul] at hzero
  ring_nf at hzero ⊢
  linarith

private theorem IsStationaryOn.real_monotonicity_identity_of_lt
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {σ ρ : ℝ} (hn : 0 < n) (hσ : 0 < σ) (hσρ : σ < ρ)
    (hball : closedBall center ρ ⊆ U) :
    σ⁻¹ ^ n * V.weightMeasure.real (closedBall center σ) +
        ∫ z : E × Grassmannian E n in
          (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ,
          ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 /
            ‖z.1 - center‖ ^ (n + 2) ∂V.toMeasure =
      ρ⁻¹ ^ n * V.weightMeasure.real (closedBall center ρ) := by
  obtain ⟨R, hρR, hRball⟩ :=
    exists_outer_closedBall (hσ.trans hσρ).le hball
  have hρ : 0 < ρ := hσ.trans hσρ
  have hR : 0 < R := hρ.trans hρR
  have hsq_ab : σ ^ 2 < ρ ^ 2 := by nlinarith
  have hsq_bc : ρ ^ 2 < R ^ 2 := by nlinarith
  have hRball' : closedBall center √(R ^ 2) ⊆ U := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hR] using hRball
  have hidentity := hV.real_squared_monotonicity_identity hn (sq_pos_of_pos hσ)
    hsq_ab hsq_bc hRball'
  have hweight (r : ℝ) :
      V.toMeasure.real (closedBall center r ×ˢ (Set.univ : Set (Grassmannian E n))) =
        V.weightMeasure.real (closedBall center r) := by
    rw [Measure.real_def, Measure.real_def, V.weightMeasure_apply measurableSet_closedBall]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hσ, Real.sqrt_sq_eq_abs, abs_of_pos hρ,
    hweight σ, hweight ρ, sq_rpow_neg_half_nat hσ n,
    sq_rpow_neg_half_nat hρ n] at hidentity
  have hset :
      (closedBall center ρ ×ˢ (Set.univ : Set (Grassmannian E n))) \
          (closedBall center σ ×ˢ (Set.univ : Set (Grassmannian E n))) =
        (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ := by
    ext z
    simp only [Set.mem_sdiff, mem_prod, mem_univ, and_true]
  rw [hset] at hidentity
  have hkernel :
      (∫ z : E × Grassmannian E n in
          (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ,
          (‖z.1 - center‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) *
            ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 ∂V.toMeasure) =
        ∫ z : E × Grassmannian E n in
          (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ,
          ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 /
            ‖z.1 - center‖ ^ (n + 2) ∂V.toMeasure := by
    apply setIntegral_congr_fun
      (measurableSet_closedBall.diff measurableSet_closedBall |>.prod MeasurableSet.univ)
    intro z hz
    have hzσ : z.1 ∉ closedBall center σ := hz.1.2
    have hnorm : 0 < ‖z.1 - center‖ := by
      have hdist : σ < dist z.1 center := by
        simpa only [mem_closedBall, not_le] using hzσ
      rw [← dist_eq_norm]
      exact hσ.trans hdist
    have hexp : -((n : ℝ) + 2) / 2 = -((n + 2 : ℕ) : ℝ) / 2 := by
      norm_num [Nat.cast_add, Nat.cast_ofNat]
    change (‖z.1 - center‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) *
        ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 =
      ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 /
        ‖z.1 - center‖ ^ (n + 2)
    rw [hexp]
    rw [sq_rpow_neg_half_nat hnorm (n + 2), inv_pow]
    simp only [div_eq_mul_inv]
    ring
  rw [hkernel] at hidentity
  exact hidentity

private theorem integrableOn_radialTilt_real
    (V : Varifold E n) {center : E} {σ ρ : ℝ} (hσ : 0 < σ) :
    IntegrableOn
      (fun z : E × Grassmannian E n =>
        ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 /
          ‖z.1 - center‖ ^ (n + 2))
      ((closedBall center ρ \ closedBall center σ) ×ˢ Set.univ) V.toMeasure := by
  let K : Set (E × Grassmannian E n) :=
    (closedBall center ρ \ ball center (σ / 2)) ×ˢ Set.univ
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact ((isCompact_closedBall center ρ).diff (isOpen_ball : IsOpen (ball center (σ / 2)))).prod
      isCompact_univ
  have hcontinuous : ContinuousOn
      (fun z : E × Grassmannian E n =>
        ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 /
          ‖z.1 - center‖ ^ (n + 2)) K := by
    apply ContinuousOn.div
    · exact (Grassmannian.continuous_perpendicularProjection_apply.comp
        (continuous_snd.prodMk (continuous_fst.sub continuous_const))).norm.pow 2
          |>.continuousOn
    · exact (continuous_fst.sub continuous_const).norm.pow (n + 2) |>.continuousOn
    · intro z hz
      have hzball : z.1 ∉ ball center (σ / 2) := hz.1.2
      have hdist : σ / 2 ≤ dist z.1 center := by
        simpa only [mem_ball, not_lt] using hzball
      have hnorm : 0 < ‖z.1 - center‖ := by
        rw [← dist_eq_norm]
        linarith
      exact pow_ne_zero _ hnorm.ne'
  apply (hcontinuous.integrableOn_compact hKcompact).mono_set
  intro z hz
  refine ⟨⟨hz.1.1, ?_⟩, Set.mem_univ _⟩
  intro hzhalf
  apply hz.1.2
  have hdist : dist z.1 center < σ / 2 := hzhalf
  rw [mem_closedBall]
  linarith

private theorem IsStationaryOn.monotonicity_of_pos_of_lt
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {σ ρ : ℝ} (hn : 0 < n) (hσ : 0 < σ) (hσρ : σ < ρ)
    (hball : closedBall center ρ ⊆ U) :
    (ENNReal.ofReal σ)⁻¹ ^ n * V.weightMeasure (closedBall center σ) +
        ∫⁻ z : E × Grassmannian E n in
          (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ,
          z.2.radialTilt center z.1 ∂V.toMeasure =
      (ENNReal.ofReal ρ)⁻¹ ^ n * V.weightMeasure (closedBall center ρ) := by
  let D : Set (E × Grassmannian E n) :=
    (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ
  let g : E × Grassmannian E n → ℝ := fun z =>
    ‖z.2.perpendicularProjection (z.1 - center)‖ ^ 2 /
      ‖z.1 - center‖ ^ (n + 2)
  have hρ : 0 < ρ := hσ.trans hσρ
  have hint : IntegrableOn g D V.toMeasure := by
    exact integrableOn_radialTilt_real V hσ
  have hnonneg : 0 ≤ᵐ[V.toMeasure.restrict D] g := by
    filter_upwards [] with z
    dsimp only [g]
    positivity
  have hreal := hV.real_monotonicity_identity_of_lt hn hσ hσρ hball
  change σ⁻¹ ^ n * V.weightMeasure.real (closedBall center σ) +
      ∫ z in D, g z ∂V.toMeasure =
    ρ⁻¹ ^ n * V.weightMeasure.real (closedBall center ρ) at hreal
  have hσmass :
      ENNReal.ofReal (σ⁻¹ ^ n * V.weightMeasure.real (closedBall center σ)) =
        (ENNReal.ofReal σ)⁻¹ ^ n * V.weightMeasure (closedBall center σ) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hσ.le) n),
      ENNReal.ofReal_pow (inv_nonneg.mpr hσ.le), ENNReal.ofReal_inv_of_pos hσ,
      Measure.real_def,
      ENNReal.ofReal_toReal (isCompact_closedBall center σ).measure_ne_top]
  have hρmass :
      ENNReal.ofReal (ρ⁻¹ ^ n * V.weightMeasure.real (closedBall center ρ)) =
        (ENNReal.ofReal ρ)⁻¹ ^ n * V.weightMeasure (closedBall center ρ) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hρ.le) n),
      ENNReal.ofReal_pow (inv_nonneg.mpr hρ.le), ENNReal.ofReal_inv_of_pos hρ,
      Measure.real_def,
      ENNReal.ofReal_toReal (isCompact_closedBall center ρ).measure_ne_top]
  have hintegral :
      ENNReal.ofReal (∫ z in D, g z ∂V.toMeasure) =
        ∫⁻ z in D, z.2.radialTilt center z.1 ∂V.toMeasure := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    rfl
  have hconverted := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_add (mul_nonneg (pow_nonneg (inv_nonneg.mpr hσ.le) n)
      (by positivity)) (integral_nonneg_of_ae hnonneg),
    hσmass, hintegral, hρmass] at hconverted
  exact hconverted

private theorem monotonicity_zero_dim
    (V : Varifold E 0) {center : E} {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    (ENNReal.ofReal σ)⁻¹ ^ 0 * V.weightMeasure (closedBall center σ) +
        ∫⁻ z : E × Grassmannian E 0 in
          (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ,
          z.2.radialTilt center z.1 ∂V.toMeasure =
      (ENNReal.ofReal ρ)⁻¹ ^ 0 * V.weightMeasure (closedBall center ρ) := by
  simp only [pow_zero, one_mul]
  let D : Set (E × Grassmannian E 0) :=
    (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ
  have hbase : MeasurableSet (closedBall center ρ \ closedBall center σ) :=
    measurableSet_closedBall.diff measurableSet_closedBall
  have hDmeas : MeasurableSet D := hbase.prod MeasurableSet.univ
  have htilt :
      (∫⁻ z : E × Grassmannian E 0 in D, z.2.radialTilt center z.1 ∂V.toMeasure) =
        V.weightMeasure (closedBall center ρ \ closedBall center σ) := by
    calc
      (∫⁻ z : E × Grassmannian E 0 in D, z.2.radialTilt center z.1 ∂V.toMeasure) =
          ∫⁻ _z : E × Grassmannian E 0 in D, 1 ∂V.toMeasure := by
        apply setLIntegral_congr_fun hDmeas
        intro z hz
        apply Grassmannian.radialTilt_zero_dim
        intro hcenter
        apply hz.1.2
        rw [hcenter]
        exact mem_closedBall_self hσ.le
      _ = V.toMeasure D := setLIntegral_one D
      _ = V.weightMeasure (closedBall center ρ \ closedBall center σ) := by
        rw [V.weightMeasure_apply hbase]
  rw [htilt]
  simpa only [union_eq_right.mpr (closedBall_subset_closedBall hσρ)] using
    (measure_add_sdiff (μ := V.weightMeasure) (s := closedBall center σ)
      measurableSet_closedBall.nullMeasurableSet (closedBall center ρ))

-- Simon, Chapter 4, formula (3.6), p. 90: exact stationary monotonicity identity.
theorem IsStationaryOn.monotonicity
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hball : closedBall center ρ ⊆ U) :
    V.weightMeasure.massRatio n center σ +
        ∫⁻ z : E × Grassmannian E n in
          (closedBall center ρ \ closedBall center σ) ×ˢ Set.univ,
          z.2.radialTilt center z.1 ∂V.toMeasure =
      V.weightMeasure.massRatio n center ρ := by
  simp only [Measure.massRatio]
  obtain rfl | hσρ := hσρ.eq_or_lt
  · simp
  by_cases hn : n = 0
  · subst n
    exact monotonicity_zero_dim V hσ hσρ.le
  · exact hV.monotonicity_of_pos_of_lt (Nat.pos_of_ne_zero hn) hσ hσρ hball

-- Simon, Chapter 4, formula (3.8), p. 91: monotonicity of the mass ratio.
theorem IsStationaryOn.massRatio_monotoneOn
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {R : ℝ} (hball : closedBall center R ⊆ U) :
    MonotoneOn (V.weightMeasure.massRatio n center) (Ioc 0 R) := by
  intro σ hσ ρ hρ hσρ
  have hidentity := hV.monotonicity hσ.1 hσρ
    ((closedBall_subset_closedBall hρ.2).trans hball)
  rw [← hidentity]
  exact le_add_right le_rfl

-- Simon, Chapter 4, formulas (3.8)-(3.9), p. 91: normalized density-ratio monotonicity.
theorem IsStationaryOn.densityRatio_monotoneOn
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {R : ℝ} (hball : closedBall center R ⊆ U) :
    MonotoneOn (V.weightMeasure.densityRatio n center) (Ioc 0 R) := by
  intro σ hσ ρ hρ hσρ
  exact ENNReal.div_le_div
    (hV.massRatio_monotoneOn hball hσ hρ hσρ) le_rfl

-- Simon, Chapter 4, formula (3.9), p. 91: existence of the density limit.
theorem IsStationaryOn.tendsto_densityRatio
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {R : ℝ} (hR : 0 < R) (hball : closedBall center R ⊆ U) :
    Tendsto (V.weightMeasure.densityRatio n center) (𝓝[>] 0)
      (𝓝 (V.weightMeasure.lowerDensity n center)) := by
  let f := V.weightMeasure.densityRatio n center
  have hmono : MonotoneOn f (Ioo 0 R) :=
    (hV.densityRatio_monotoneOn hball).mono Ioo_subset_Ioc_self
  have hnonempty : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, by constructor <;> linarith⟩
  have htend : Tendsto f (𝓝[>] 0) (𝓝 (sInf (f '' Ioo 0 R))) :=
    hmono.tendsto_nhdsWithin_Ioo_right hnonempty (OrderBot.bddBelow _)
  have hlower : V.weightMeasure.lowerDensity n center = sInf (f '' Ioo 0 R) :=
    htend.liminf_eq
  rw [hlower]
  exact htend

-- Simon, Chapter 4, formula (3.9), p. 91: finiteness of the density.
theorem IsStationaryOn.lowerDensity_ne_top
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {R : ℝ} (hR : 0 < R) (hball : closedBall center R ⊆ U) :
    V.weightMeasure.lowerDensity n center ≠ ∞ := by
  let f := V.weightMeasure.densityRatio n center
  have hmono : MonotoneOn f (Ioo 0 R) :=
    (hV.densityRatio_monotoneOn hball).mono Ioo_subset_Ioc_self
  have hmid : R / 2 ∈ Ioo (0 : ℝ) R := by constructor <;> linarith
  have htend : Tendsto f (𝓝[>] 0) (𝓝 (sInf (f '' Ioo 0 R))) :=
    hmono.tendsto_nhdsWithin_Ioo_right ⟨R / 2, hmid⟩ (OrderBot.bddBelow _)
  have hlower : V.weightMeasure.lowerDensity n center = sInf (f '' Ioo 0 R) :=
    htend.liminf_eq
  rw [hlower]
  apply ne_top_of_le_ne_top _ (csInf_le (OrderBot.bddBelow _) (mem_image_of_mem f hmid))
  dsimp only [f, Measure.densityRatio, Measure.massRatio]
  apply ENNReal.div_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hmid.1))
    · exact (isCompact_closedBall center (R / 2)).measure_ne_top
  · exact euclideanUnitBallVolume_ne_zero n

-- Simon, Chapter 4, formula (3.9), p. 91: lower and upper density agree.
theorem IsStationaryOn.lowerDensity_eq_upperDensity
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {R : ℝ} (hR : 0 < R) (hball : closedBall center R ⊆ U) :
    V.weightMeasure.lowerDensity n center = V.weightMeasure.upperDensity n center := by
  have htend := hV.tendsto_densityRatio hR hball
  rw [Measure.lowerDensity, Measure.upperDensity, htend.liminf_eq, htend.limsup_eq]

-- Simon, Chapter 4, formula (3.9), p. 91: upper density is finite.
theorem IsStationaryOn.upperDensity_ne_top
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {R : ℝ} (hR : 0 < R) (hball : closedBall center R ⊆ U) :
    V.weightMeasure.upperDensity n center ≠ ∞ := by
  rw [← hV.lowerDensity_eq_upperDensity hR hball]
  exact hV.lowerDensity_ne_top hR hball

-- Simon, Chapter 4, formula (3.10), p. 91; Chapter 8, formula (3.4), p. 211.
theorem IsStationaryOn.density_excess
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U)
    {center : E} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall center ρ ⊆ U) :
    V.weightMeasure.lowerDensity n center +
        (∫⁻ z : E × Grassmannian E n in
          closedBall center ρ ×ˢ Set.univ,
          z.2.radialTilt center z.1 ∂V.toMeasure) / euclideanUnitBallVolume n =
      V.weightMeasure.densityRatio n center ρ := by
  let r : ℕ → ℝ := fun i => ρ / (i + 1 : ℝ)
  let D : ℕ → Set (E × Grassmannian E n) := fun i =>
    (closedBall center ρ \ closedBall center (r i)) ×ˢ Set.univ
  let tilt : E × Grassmannian E n → ℝ≥0∞ := fun z =>
    z.2.radialTilt center z.1
  let f : ℕ → E × Grassmannian E n → ℝ≥0∞ := fun i => (D i).indicator tilt
  let fLimit : E × Grassmannian E n → ℝ≥0∞ := fun z =>
    (closedBall center ρ ×ˢ Set.univ).indicator tilt z
  have hr_pos (i : ℕ) : 0 < r i := by
    dsimp only [r]
    positivity
  have hr_le (i : ℕ) : r i ≤ ρ := by
    dsimp only [r]
    apply div_le_self hρ.le
    norm_num
  have hr_antitone : Antitone r := by
    intro i j hij
    dsimp only [r]
    gcongr
  have hr_zero : Tendsto r atTop (𝓝 0) := by
    simpa only [r, div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr_tendsto : Tendsto r atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hr_zero, Eventually.of_forall fun i => hr_pos i⟩
  have hDmeas (i : ℕ) : MeasurableSet (D i) := by
    exact (measurableSet_closedBall.diff measurableSet_closedBall).prod MeasurableSet.univ
  have hDmono : Monotone D := by
    intro i j hij z hz
    refine ⟨⟨hz.1.1, ?_⟩, hz.2⟩
    intro hzj
    exact hz.1.2 (closedBall_subset_closedBall (hr_antitone hij) hzj)
  have hfmeas (i : ℕ) : Measurable (f i) := by
    exact (Grassmannian.measurable_radialTilt center).indicator (hDmeas i)
  have hfmono : ∀ᵐ z ∂V.toMeasure, Monotone fun i => f i z := by
    filter_upwards [] with z i j hij
    exact indicator_le_indicator_of_subset (hDmono hij)
      (show 0 ≤ tilt from fun _ => bot_le) z
  have hftend : ∀ᵐ z ∂V.toMeasure,
      Tendsto (fun i => f i z) atTop (𝓝 (fLimit z)) := by
    filter_upwards [] with z
    by_cases hzρ : z.1 ∈ closedBall center ρ
    · by_cases hzc : z.1 = center
      · apply tendsto_const_nhds.congr'
        filter_upwards [] with i
        simp [f, fLimit, D, tilt, hzc, Grassmannian.radialTilt,
          (hr_pos i).le]
      · have hdist : 0 < dist z.1 center := dist_pos.mpr hzc
        have hevent : ∀ᶠ i in atTop, r i < dist z.1 center :=
          hr_zero.eventually (Iio_mem_nhds hdist)
        apply tendsto_const_nhds.congr'
        filter_upwards [hevent] with i hi
        have hzinner : z.1 ∉ closedBall center (r i) := by
          simpa only [Metric.mem_closedBall, not_le] using hi
        simp [f, fLimit, D, hzρ, hzinner]
    · apply tendsto_const_nhds.congr'
      filter_upwards [] with i
      simp [f, fLimit, D, hzρ]
  have htendTilt : Tendsto
      (fun i => ∫⁻ z in D i, tilt z ∂V.toMeasure) atTop
      (𝓝 (∫⁻ z in closedBall center ρ ×ˢ Set.univ, tilt z ∂V.toMeasure)) := by
    have htend := lintegral_tendsto_of_tendsto_of_monotone
      (fun i => (hfmeas i).aemeasurable) hfmono hftend
    simpa only [f, fLimit, lintegral_indicator (hDmeas _),
      lintegral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)] using htend
  have hdensity : Tendsto
      (fun i => V.weightMeasure.densityRatio n center (r i)) atTop
      (𝓝 (V.weightMeasure.lowerDensity n center)) :=
    (hV.tendsto_densityRatio hρ hball).comp hr_tendsto
  have hidentity (i : ℕ) :
      V.weightMeasure.massRatio n center (r i) +
          ∫⁻ z in D i, tilt z ∂V.toMeasure =
        V.weightMeasure.massRatio n center ρ := by
    simpa only [D, tilt] using hV.monotonicity (hr_pos i) (hr_le i) hball
  have hnormalized (i : ℕ) :
      V.weightMeasure.densityRatio n center (r i) +
          (∫⁻ z in D i, tilt z ∂V.toMeasure) / euclideanUnitBallVolume n =
        V.weightMeasure.densityRatio n center ρ := by
    rw [Measure.densityRatio, Measure.densityRatio, ← ENNReal.add_div, hidentity]
  have htendTiltNormalized : Tendsto
      (fun i => (∫⁻ z in D i, tilt z ∂V.toMeasure) / euclideanUnitBallVolume n) atTop
      (𝓝 ((∫⁻ z in closedBall center ρ ×ˢ Set.univ,
        tilt z ∂V.toMeasure) / euclideanUnitBallVolume n)) :=
    ENNReal.Tendsto.div_const htendTilt (Or.inr (euclideanUnitBallVolume_ne_zero n))
  have hsum := hdensity.add htendTiltNormalized
  have hconst : Tendsto
      (fun _ : ℕ => V.weightMeasure.densityRatio n center ρ) atTop
      (𝓝 (V.weightMeasure.densityRatio n center ρ)) := tendsto_const_nhds
  have hconst' := hconst.congr' (Eventually.of_forall fun i => (hnormalized i).symm)
  exact tendsto_nhds_unique hsum hconst'

-- Simon, Chapter 4, formula (3.11), p. 91: upper semicontinuity of stationary density.
theorem IsStationaryOn.upperSemicontinuousOn_lowerDensity
    {V : Varifold E n} {U : TopologicalSpace.Opens E} (hV : V.IsStationaryOn U) :
    UpperSemicontinuousOn (fun x => V.weightMeasure.lowerDensity n x) U := by
  rw [upperSemicontinuousOn_iff]
  intro x hx a hxa
  obtain ⟨R, hR, hRball⟩ := (Metric.isOpen_iff.mp U.2) x hx
  let R' := R / 2
  have hR' : 0 < R' := by
    dsimp only [R']
    linarith
  have hclosed : closedBall x R' ⊆ U :=
    (closedBall_subset_ball (show R' < R by dsimp only [R']; linarith)).trans hRball
  have hratioRadii : ∀ᶠ r in 𝓝[>] 0,
      V.weightMeasure.densityRatio n x r < a :=
    (hV.tendsto_densityRatio hR' hclosed).eventually (Iio_mem_nhds hxa)
  have hsmall : ∀ᶠ r in 𝓝[>] 0, r < R' :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hR')
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, ⟨hratio, hr⟩, hrR⟩ :=
    ((hratioRadii.and hpos).and hsmall).exists
  have hratioNear : ∀ᶠ y in 𝓝 x,
      V.weightMeasure.densityRatio n y r < a :=
    (V.weightMeasure.upperSemicontinuous_densityRatio n hr) x a hratio
  have hratioNearWithin : ∀ᶠ y in 𝓝[U] x,
      V.weightMeasure.densityRatio n y r < a :=
    Filter.Eventually.filter_mono inf_le_left hratioNear
  have hballNearWithin : ∀ᶠ y in 𝓝[U] x, y ∈ ball x (R' - r) :=
    Filter.Eventually.filter_mono inf_le_left (ball_mem_nhds x (sub_pos.mpr hrR))
  filter_upwards [hratioNearWithin, hballNearWithin] with y hyratio hy
  have hsub : closedBall y r ⊆ closedBall x R' := by
    apply closedBall_subset_closedBall'
    rw [mem_ball] at hy
    linarith
  have hdensity := hV.density_excess hr (hsub.trans hclosed)
  exact (le_add_right le_rfl |>.trans_eq hdensity).trans_lt hyratio

end Varifold
