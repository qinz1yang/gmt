import GMT.Linear.Grassmannian.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open InnerProductSpace

-- Simon, Chapter 4, Section 3, pp. 89-90: the radial test field X(y) = gamma(r)(y - xi).
def radialVectorField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center : E) (profile : ℝ → ℝ) (x : E) : E :=
  profile ‖x - center‖ • (x - center)

-- Simon, Chapter 4, formulas (3.2)-(3.6), pp. 89-91: the smooth squared-radius proof engine.
def squaredRadiusRadialVectorField {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (center : E) (profile : ℝ → ℝ) (x : E) : E :=
  profile (‖x - center‖ ^ 2) • (x - center)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_squaredRadiusRadialVectorField
    {profile : ℝ → ℝ} {k : ℕ∞} (hprofile : ContDiff ℝ k profile)
    (center : E) :
    ContDiff ℝ k (squaredRadiusRadialVectorField center profile) := by
  unfold squaredRadiusRadialVectorField
  have hsub : ContDiff ℝ k (fun y : E => y - center) :=
    contDiff_id.sub contDiff_const
  exact (hprofile.comp (hsub.norm_sq ℝ)).smul hsub

-- Simon, Chapter 4, formula (3.2), p. 89: derivative of the radial test field.
theorem hasFDerivAt_radialVectorField
    {profile : ℝ → ℝ} {profile' : ℝ} {center x : E}
    (hprofile : HasDerivAt profile profile' ‖x - center‖)
    (hx : x ≠ center) :
    HasFDerivAt (radialVectorField center profile)
      (profile ‖x - center‖ • ContinuousLinearMap.id ℝ E +
        (‖x - center‖⁻¹ * profile') •
          rankOne ℝ (x - center) (x - center)) x := by
  have hx' : x - center ≠ 0 := sub_ne_zero.mpr hx
  have hnorm_ne : ‖x - center‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  have hnorm : HasFDerivAt (fun y : E => ‖y - center‖)
      (‖x - center‖⁻¹ • innerSL ℝ (x - center)) x := by
    have hsq := (hasFDerivAt_id x).sub_const center |>.norm_sq
    have hsqrt := Real.hasDerivAt_sqrt (pow_ne_zero 2 hnorm_ne)
    have h := hsqrt.comp_hasFDerivAt x hsq
    have heq : ((fun t : ℝ => √t) ∘ fun y : E => ‖id y - center‖ ^ 2) =
        fun y : E => ‖y - center‖ := by
      funext y
      exact Real.sqrt_sq (norm_nonneg (y - center))
    rw [heq] at h
    apply h.congr_fderiv
    ext v
    simp only [id_eq, Real.sqrt_sq (norm_nonneg (x - center)), smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, one_div, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring_nf
  have hscalar : HasFDerivAt (fun y : E => profile ‖y - center‖)
      (profile' • (‖x - center‖⁻¹ • innerSL ℝ (x - center))) x := by
    simpa only [Function.comp_def] using hprofile.comp_hasFDerivAt x hnorm
  have hvector : HasFDerivAt (fun y : E => y - center)
      (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const center
  have hderiv :
      profile ‖x - center‖ • ContinuousLinearMap.id ℝ E +
          (profile' • (‖x - center‖⁻¹ • innerSL ℝ (x - center))).smulRight
            (x - center) =
        profile ‖x - center‖ • ContinuousLinearMap.id ℝ E +
          (‖x - center‖⁻¹ * profile') •
            rankOne ℝ (x - center) (x - center) := by
    congr 1
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      innerSL_apply_apply, rankOne_apply, smul_smul, smul_eq_mul]
    ring_nf
  change HasFDerivAt (fun y : E => profile ‖y - center‖ • (y - center)) _ x
  exact (hscalar.smul hvector).congr_fderiv hderiv

-- Simon, Chapter 4, formulas (3.2)-(3.3), pp. 89-90: squared-radius reparameterization.
theorem hasFDerivAt_squaredRadiusRadialVectorField
    {profile : ℝ → ℝ} {profile' : ℝ} {center x : E}
    (hprofile : HasDerivAt profile profile' (‖x - center‖ ^ 2)) :
    HasFDerivAt (squaredRadiusRadialVectorField center profile)
      (profile (‖x - center‖ ^ 2) • ContinuousLinearMap.id ℝ E +
        (2 * profile') • rankOne ℝ (x - center) (x - center)) x := by
  have hradius : HasFDerivAt (fun y : E => ‖y - center‖ ^ 2)
      (2 • innerSL ℝ (x - center)) x :=
    (hasFDerivAt_id x).sub_const center |>.norm_sq
  have hscalar : HasFDerivAt (fun y : E => profile (‖y - center‖ ^ 2))
      (profile' • (2 • innerSL ℝ (x - center))) x := by
    simpa only [Function.comp_def] using hprofile.comp_hasFDerivAt x hradius
  have hvector : HasFDerivAt (fun y : E => y - center)
      (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const center
  have hderiv :
      profile (‖x - center‖ ^ 2) • ContinuousLinearMap.id ℝ E +
          (profile' • (2 • innerSL ℝ (x - center))).smulRight (x - center) =
        profile (‖x - center‖ ^ 2) • ContinuousLinearMap.id ℝ E +
          (2 * profile') • rankOne ℝ (x - center) (x - center) := by
    congr 1
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      innerSL_apply_apply, rankOne_apply, smul_smul, smul_eq_mul]
    ring_nf
  change HasFDerivAt
    (fun y : E => profile (‖y - center‖ ^ 2) • (y - center)) _ x
  exact (hscalar.smul hvector).congr_fderiv hderiv

namespace Grassmannian

variable [FiniteDimensional ℝ E] {n : ℕ}

-- Simon, Chapter 4, formula (3.2), p. 89: tangential divergence of the radial field.
theorem tangentialTrace_fderiv_radialVectorField (S : Grassmannian E n)
    {profile : ℝ → ℝ} {profile' : ℝ} {center x : E}
    (hprofile : HasDerivAt profile profile' ‖x - center‖) (hx : x ≠ center) :
    S.tangentialTrace (fderiv ℝ (radialVectorField center profile) x) =
      (n : ℝ) * profile ‖x - center‖ +
        (‖x - center‖⁻¹ * profile') * ‖S.projection (x - center)‖ ^ 2 := by
  rw [(hasFDerivAt_radialVectorField hprofile hx).fderiv, map_add,
    map_smul, map_smul, S.tangentialTrace_id,
    S.tangentialTrace_rankOne_self]
  ring

-- Simon, Chapter 4, formula (3.2), p. 90: rewrite using the perpendicular radial component.
theorem tangentialTrace_fderiv_radialVectorField_eq_perpendicularProjection
    (S : Grassmannian E n) {profile : ℝ → ℝ} {profile' : ℝ}
    {center x : E} (hprofile : HasDerivAt profile profile' ‖x - center‖)
    (hx : x ≠ center) :
    S.tangentialTrace (fderiv ℝ (radialVectorField center profile) x) =
      (n : ℝ) * profile ‖x - center‖ + ‖x - center‖ * profile' -
        (‖x - center‖⁻¹ * profile') *
          ‖S.perpendicularProjection (x - center)‖ ^ 2 := by
  rw [(hasFDerivAt_radialVectorField hprofile hx).fderiv, map_add,
    map_smul, map_smul, S.tangentialTrace_id,
    S.tangentialTrace_rankOne_self]
  rw [smul_eq_mul, smul_eq_mul, mul_comm (profile ‖x - center‖) (n : ℝ)]
  have hnorm : ‖x - center‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hdecomp := S.norm_sq_projection_add_norm_sq_perpendicularProjection (x - center)
  have hinv : ‖x - center‖⁻¹ * ‖x - center‖ ^ 2 = ‖x - center‖ := by
    rw [pow_two, inv_mul_cancel_left₀ hnorm]
  calc
    (n : ℝ) * profile ‖x - center‖ +
        (‖x - center‖⁻¹ * profile') * ‖S.projection (x - center)‖ ^ 2 =
      (n : ℝ) * profile ‖x - center‖ +
        (‖x - center‖⁻¹ * profile') *
          (‖x - center‖ ^ 2 - ‖S.perpendicularProjection (x - center)‖ ^ 2) := by
            congr 2
            nlinarith
    _ = (n : ℝ) * profile ‖x - center‖ + ‖x - center‖ * profile' -
        (‖x - center‖⁻¹ * profile') *
          ‖S.perpendicularProjection (x - center)‖ ^ 2 := by
            rw [mul_sub]
            rw [show (‖x - center‖⁻¹ * profile') * ‖x - center‖ ^ 2 =
                ‖x - center‖ * profile' by
              calc
                (‖x - center‖⁻¹ * profile') * ‖x - center‖ ^ 2 =
                    profile' * (‖x - center‖⁻¹ * ‖x - center‖ ^ 2) := by ring
                _ = profile' * ‖x - center‖ := by rw [hinv]
                _ = ‖x - center‖ * profile' := mul_comm _ _]
            ring

-- Simon, Chapter 4, formulas (3.2)-(3.3), pp. 89-90: squared-radius tangential divergence.
theorem tangentialTrace_fderiv_squaredRadiusRadialVectorField
    (S : Grassmannian E n) {profile : ℝ → ℝ} {profile' : ℝ}
    {center x : E} (hprofile : HasDerivAt profile profile' (‖x - center‖ ^ 2)) :
    S.tangentialTrace (fderiv ℝ (squaredRadiusRadialVectorField center profile) x) =
      (n : ℝ) * profile (‖x - center‖ ^ 2) +
        2 * profile' * ‖S.projection (x - center)‖ ^ 2 := by
  rw [(hasFDerivAt_squaredRadiusRadialVectorField hprofile).fderiv,
    map_add, map_smul, map_smul, S.tangentialTrace_id,
    S.tangentialTrace_rankOne_self]
  ring

end Grassmannian
