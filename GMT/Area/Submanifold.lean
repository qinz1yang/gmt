import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Constructions

noncomputable section

open Set

def IsContDiffSubmanifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (s : Set E) : Prop :=
  ∀ x ∈ s, ∃ V : Submodule ℝ E,
    Module.finrank ℝ V = n ∧
      ∃ U : Set V, IsOpen U ∧
        ∃ φ : V → E,
          ContDiffOn ℝ 1 φ U ∧
            (∀ z ∈ U, Function.Injective (fderiv ℝ φ z)) ∧
              Topology.IsEmbedding (U.domRestrict φ) ∧
                ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ φ '' U = s ∩ W
