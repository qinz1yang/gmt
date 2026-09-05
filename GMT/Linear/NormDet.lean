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

theorem normDet_le_norm_pow (L : E →L[ℝ] F) :
    L.toLinearMap.normDet ≤ ‖L‖ ^ Module.finrank ℝ E := by
  rw [LinearMap.normDet_eq_prod_singularValues]
  apply (Finset.prod_le_prod (fun i hi => L.toLinearMap.singularValues_nonneg i) ?_).trans
  · rw [Finset.prod_const, Finset.card_range]
  intro i hi
  have hi' : i < Module.finrank ℝ E := Finset.mem_range.mp hi
  let T : E →ₗ[ℝ] E := L.toLinearMap.adjoint ∘ₗ L.toLinearMap
  let hT : T.IsSymmetric := L.toLinearMap.isSymmetric_adjoint_comp_self
  let v : E := hT.eigenvectorBasis rfl ⟨i, hi'⟩
  have hv : ‖v‖ = 1 :=
    hT.eigenvectorBasis rfl |>.orthonormal.norm_eq_one ⟨i, hi'⟩
  have heigen : T v = hT.eigenvalues rfl ⟨i, hi'⟩ • v :=
    hT.apply_eigenvectorBasis rfl ⟨i, hi'⟩
  have hsq : L.toLinearMap.singularValues i ^ 2 ≤ ‖L‖ ^ 2 := by
    rw [L.toLinearMap.sq_singularValues_of_lt rfl hi']
    calc
      hT.eigenvalues rfl ⟨i, hi'⟩ =
          inner ℝ v (hT.eigenvalues rfl ⟨i, hi'⟩ • v) := by
        rw [inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
      _ = inner ℝ v (T v) :=
        congrArg (fun w : E => inner ℝ v w) heigen.symm
      _ = ‖L v‖ ^ 2 := by
        rw [show T v = L.adjoint (L v) from rfl, adjoint_inner_right,
          real_inner_self_eq_norm_sq]
      _ ≤ (‖L‖ * ‖v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (L.le_opNorm v)
      _ = ‖L‖ ^ 2 := by rw [hv, mul_one]
  exact (sq_le_sq₀ (L.toLinearMap.singularValues_nonneg i) (norm_nonneg L)).mp hsq

end ContinuousLinearMap
