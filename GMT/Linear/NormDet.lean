import Mathlib.Analysis.InnerProductSpace.NormDet

noncomputable section

namespace LinearMap

theorem normDet_adjoint_of_finrank_eq
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (L : U →ₗ[ℝ] V)
    (h : Module.finrank ℝ U = Module.finrank ℝ V) :
    L.adjoint.normDet = L.normDet := by
  let bU : OrthonormalBasis (Fin (Module.finrank ℝ U)) ℝ U :=
    stdOrthonormalBasis ℝ U
  let bV : OrthonormalBasis (Fin (Module.finrank ℝ U)) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr h.symm)
  rw [L.normDet_eq_norm_det_toMatrix bU bV]
  rw [L.adjoint.normDet_eq_norm_det_toMatrix bV bU]
  rw [LinearMap.toMatrix_adjoint]
  simp

end LinearMap

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem continuous_normDet :
    Continuous (fun L : E →L[ℝ] F => L.toLinearMap.normDet) := by
  have hgram : Continuous (fun L : E →L[ℝ] F => L.adjoint.comp L) :=
    ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
  have hdet : Continuous (fun L : E →L[ℝ] F => (L.adjoint.comp L).det) :=
    ContinuousLinearMap.continuous_det.comp hgram
  have hsqrt : Continuous (fun L : E →L[ℝ] F => √((L.adjoint.comp L).det)) :=
    Real.continuous_sqrt.comp hdet
  convert hsqrt using 1
  funext L
  rw [← L.normDet_sq]
  change L.toLinearMap.normDet = √(L.toLinearMap.normDet ^ 2)
  rw [Real.sqrt_sq (LinearMap.normDet_nonneg _)]

end ContinuousLinearMap
