import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

noncomputable section

-- Simon, Chapter 8, Section 1, p. 205: the Grassmannian G(n + ell, n).
def Grassmannian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) :=
  {p : E →L[ℝ] E //
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)}

namespace Grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

instance : MetricSpace (Grassmannian E n) :=
  inferInstanceAs (MetricSpace {p : E →L[ℝ] E //
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)})

instance : MeasurableSpace (Grassmannian E n) :=
  inferInstanceAs (MeasurableSpace {p : E →L[ℝ] E //
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)})

instance : BorelSpace (Grassmannian E n) :=
  inferInstanceAs (BorelSpace {p : E →L[ℝ] E //
    IsStarProjection p ∧ LinearMap.trace ℝ E p.toLinearMap = (n : ℝ)})

-- Simon, Chapter 8, Section 1, p. 205: the orthogonal projection p_S.
def projection (S : Grassmannian E n) : E →L[ℝ] E := S.1

@[simp]
theorem isStarProjection_projection (S : Grassmannian E n) :
    IsStarProjection S.projection :=
  S.property.1

@[simp]
theorem trace_projection (S : Grassmannian E n) :
    LinearMap.trace ℝ E S.projection.toLinearMap = (n : ℝ) :=
  S.property.2

def subspace (S : Grassmannian E n) : Submodule ℝ E := S.projection.range

-- Simon, Chapter 4, Section 3, p. 90: the perpendicular projection D^perp r.
def perpendicularProjection (S : Grassmannian E n) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - S.projection

theorem isometry_projection :
    Isometry (projection : Grassmannian E n → E →L[ℝ] E) :=
  isometry_subtype_coe

@[fun_prop]
theorem continuous_projection :
    Continuous (projection : Grassmannian E n → E →L[ℝ] E) :=
  isometry_projection.continuous

theorem measurable_projection :
    Measurable (projection : Grassmannian E n → E →L[ℝ] E) :=
  continuous_projection.measurable

@[fun_prop]
theorem continuous_projection_apply :
    Continuous fun z : Grassmannian E n × E => z.1.projection z.2 := by
  fun_prop

@[fun_prop]
theorem continuous_perpendicularProjection_apply :
    Continuous fun z : Grassmannian E n × E => z.1.perpendicularProjection z.2 := by
  change Continuous (Prod.snd - fun z : Grassmannian E n × E => z.1.projection z.2)
  exact continuous_snd.sub continuous_projection_apply

theorem ext_projection {S T : Grassmannian E n} (h : S.projection = T.projection) : S = T :=
  Subtype.ext h

end Grassmannian
