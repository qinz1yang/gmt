import GMT.Linear.Grassmannian.Defs
import GMT.Linear.Trace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section

open Module

namespace Grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

private theorem isClosed_set : IsClosed {p : E →L[ℝ] E |
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)} := by
  rw [show {p : E →L[ℝ] E | IsStarProjection p ∧
      LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)} =
    {p | p * p = p} ∩ {p | star p = p} ∩
      {p | LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)} by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, isStarProjection_iff,
        IsIdempotentElem, IsSelfAdjoint]]
  exact ((isClosed_eq (continuous_id.mul continuous_id) continuous_id).inter
      (isClosed_eq continuous_star continuous_id)).inter
    (isClosed_eq (ContinuousLinearMap.trace ℝ E).continuous continuous_const)

theorem norm_projection_le (S : Grassmannian E n) : ‖S.projection‖ ≤ 1 := by
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp S.property.1
  change ‖S.1‖ ≤ 1
  rw [h]
  exact Submodule.starProjection_norm_le _

private theorem isBounded_set : Bornology.IsBounded {p : E →L[ℝ] E |
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)} := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  exact ⟨1, fun p hp => by
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h := norm_projection_le (⟨p, hp⟩ : Grassmannian E n)
    change ‖p‖ ≤ 1 at h
    exact h⟩

instance : CompactSpace (Grassmannian E n) := by
  change CompactSpace {p : E →L[ℝ] E //
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)}
  exact isCompact_iff_compactSpace.mp <|
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_set, isBounded_set⟩

@[simp]
theorem finrank_subspace (S : Grassmannian E n) : finrank ℝ S.subspace = n := by
  have hp : IsIdempotentElem S.projection.toLinearMap :=
    ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr S.property.1.1
  have h := (LinearMap.IsIdempotentElem.isProj_range S.projection.toLinearMap hp).trace
  rw [S.trace_projection] at h
  exact_mod_cast h.symm

theorem projection_eq_starProjection (S : Grassmannian E n) :
    S.projection = S.subspace.starProjection := by
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp S.property.1
  exact h

def tangentialTrace (S : Grassmannian E n) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  (ContinuousLinearMap.trace ℝ E).comp
    (ContinuousLinearMap.compL ℝ E E E S.projection)

@[simp]
theorem tangentialTrace_apply (S : Grassmannian E n) (A : E →L[ℝ] E) :
    S.tangentialTrace A = LinearMap.trace ℝ E (S.projection.comp A).toLinearMap :=
  rfl

@[fun_prop]
theorem continuous_tangentialTrace_apply :
    Continuous fun z : Grassmannian E n × (E →L[ℝ] E) => z.1.tangentialTrace z.2 := by
  have h : Continuous fun z : Grassmannian E n × (E →L[ℝ] E) =>
      (z.1.projection, z.2) := by
    fun_prop
  exact (ContinuousLinearMap.trace ℝ E).continuous.comp
    ((ContinuousLinearMap.compL ℝ E E E).continuous₂.comp h)

theorem norm_tangentialTrace_le (S : Grassmannian E n) (A : E →L[ℝ] E) :
    ‖S.tangentialTrace A‖ ≤ ‖ContinuousLinearMap.trace ℝ E‖ * ‖A‖ := by
  calc
    ‖S.tangentialTrace A‖ ≤
        ‖ContinuousLinearMap.trace ℝ E‖ * ‖S.projection.comp A‖ :=
      by
        change ‖ContinuousLinearMap.trace ℝ E (S.projection.comp A)‖ ≤ _
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ContinuousLinearMap.trace ℝ E‖ * (‖S.projection‖ * ‖A‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg (ContinuousLinearMap.trace ℝ E))
    _ ≤ ‖ContinuousLinearMap.trace ℝ E‖ * (1 * ‖A‖) := by
      gcongr
      exact S.norm_projection_le
    _ = ‖ContinuousLinearMap.trace ℝ E‖ * ‖A‖ := by ring

theorem tangentialTrace_id (S : Grassmannian E n) :
    S.tangentialTrace (ContinuousLinearMap.id ℝ E) = (n : ℝ) := by
  rw [tangentialTrace_apply, ContinuousLinearMap.comp_id]
  exact S.trace_projection

theorem tangentialTrace_rankOne (S : Grassmannian E n) (x y : E) :
    S.tangentialTrace (InnerProductSpace.rankOne ℝ x y) =
      inner ℝ y (S.projection x) := by
  rw [tangentialTrace_apply, InnerProductSpace.comp_rankOne,
    InnerProductSpace.trace_rankOne]

@[simp]
theorem perpendicularProjection_eq (S : Grassmannian E n) :
    S.perpendicularProjection = S.subspaceᗮ.starProjection := by
  rw [Submodule.starProjection_orthogonal, perpendicularProjection,
    S.projection_eq_starProjection]

def ofSubmodule (S : Submodule ℝ E) (hS : finrank ℝ S = n) : Grassmannian E n :=
  ⟨S.starProjection, isStarProjection_starProjection, by
    have hp : IsIdempotentElem S.starProjection.toLinearMap :=
      ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
        S.isIdempotentElem_starProjection
    rw [(LinearMap.IsIdempotentElem.isProj_range S.starProjection.toLinearMap hp).trace,
      Submodule.range_starProjection, hS]⟩

@[simp]
theorem projection_ofSubmodule (S : Submodule ℝ E) (hS : finrank ℝ S = n) :
    (ofSubmodule S hS).projection = S.starProjection := rfl

@[simp]
theorem subspace_ofSubmodule (S : Submodule ℝ E) (hS : finrank ℝ S = n) :
    (ofSubmodule S hS).subspace = S :=
  Submodule.range_starProjection S

@[ext]
theorem ext {S T : Grassmannian E n} (h : S.subspace = T.subspace) : S = T := by
  apply ext_projection
  rw [S.projection_eq_starProjection, T.projection_eq_starProjection, h]

@[simp]
theorem projection_apply_mem (S : Grassmannian E n) (x : E) :
    S.projection x ∈ S.subspace :=
  LinearMap.mem_range_self S.projection.toLinearMap x

theorem perpendicularProjection_apply_mem (S : Grassmannian E n) (x : E) :
    S.perpendicularProjection x ∈ S.subspaceᗮ := by
  rw [S.perpendicularProjection_eq]
  exact Submodule.starProjection_apply_mem _ _

theorem projection_add_perpendicularProjection (S : Grassmannian E n) (x : E) :
    S.projection x + S.perpendicularProjection x = x := by
  simp [perpendicularProjection]

theorem inner_projection_perpendicularProjection (S : Grassmannian E n) (x y : E) :
    inner ℝ (S.projection x) (S.perpendicularProjection y) = 0 := by
  exact S.subspace.inner_right_of_mem_orthogonal
    (S.projection_apply_mem x) (S.perpendicularProjection_apply_mem y)

theorem norm_sq_projection_add_norm_sq_perpendicularProjection
    (S : Grassmannian E n) (x : E) :
    ‖x‖ ^ 2 = ‖S.projection x‖ ^ 2 + ‖S.perpendicularProjection x‖ ^ 2 := by
  rw [S.projection_eq_starProjection, S.perpendicularProjection_eq]
  exact S.subspace.norm_sq_eq_add_norm_sq_starProjection x

theorem inner_projection_self (S : Grassmannian E n) (x : E) :
    inner ℝ (S.projection x) x = ‖S.projection x‖ ^ 2 := by
  rw [S.projection_eq_starProjection]
  simpa using S.subspace.re_inner_starProjection_eq_normSq x

theorem tangentialTrace_rankOne_self (S : Grassmannian E n) (x : E) :
    S.tangentialTrace (InnerProductSpace.rankOne ℝ x x) =
      ‖S.projection x‖ ^ 2 := by
  rw [S.tangentialTrace_rankOne]
  simpa [real_inner_comm] using S.inner_projection_self x

theorem tangentialTrace_eq_sum_inner (S : Grassmannian E n)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ S.subspace)
    (A : E →L[ℝ] E) :
    S.tangentialTrace A = ∑ i, inner ℝ ((b i : S.subspace) : E) (A (b i : E)) := by
  let P : E →ₗ[ℝ] S.subspace :=
    S.projection.toLinearMap.codRestrict S.subspace fun x => S.projection_apply_mem x
  let I : S.subspace →ₗ[ℝ] E := S.subspace.subtype
  have hfactor : I ∘ₗ (P ∘ₗ A.toLinearMap) = (S.projection.comp A).toLinearMap := by
    ext x
    rfl
  rw [tangentialTrace_apply, ← hfactor, LinearMap.trace_comp_comm',
    LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ ((b i : S.subspace) : E) (S.projection (A (b i : E))) = _
  rw [S.projection_eq_starProjection]
  exact S.subspace.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) (A (b i : E))

end Grassmannian
