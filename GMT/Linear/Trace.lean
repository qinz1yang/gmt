import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section

namespace ContinuousLinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (E : Type*)
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

def trace : (E →L[𝕜] E) →L[𝕜] 𝕜 :=
  ({ toFun := fun A : E →L[𝕜] E => LinearMap.trace 𝕜 E A.toLinearMap
     map_add' := fun A B => (LinearMap.trace 𝕜 E).map_add A.toLinearMap B.toLinearMap
     map_smul' := fun c A => (LinearMap.trace 𝕜 E).map_smul c A.toLinearMap } :
    (E →L[𝕜] E) →ₗ[𝕜] 𝕜).toContinuousLinearMap

@[simp]
theorem trace_apply (A : E →L[𝕜] E) :
    trace 𝕜 E A = LinearMap.trace 𝕜 E A.toLinearMap :=
  by simp [trace, LinearMap.coe_toContinuousLinearMap']

end ContinuousLinearMap
