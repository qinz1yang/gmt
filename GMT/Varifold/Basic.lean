import GMT.Linear.Grassmannian.Basic
import GMT.Measure.Marginal
import GMT.Varifold.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open Set
open scoped ENNReal MeasureTheory NNReal

noncomputable section

namespace Varifold

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

instance (V : Varifold E n) : IsFiniteMeasureOnCompacts V.weightMeasure := by
  rw [weightMeasure]
  infer_instance

theorem weightMeasure_apply (V : Varifold E n) {s : Set E} (hs : MeasurableSet s) :
    V.weightMeasure s = V.toMeasure (s ×ˢ Set.univ) := by
  rw [weightMeasure, Measure.fst_apply hs, Set.prod_univ]

theorem lintegral_weightMeasure (V : Varifold E n) {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂V.weightMeasure = ∫⁻ z, f z.1 ∂V.toMeasure :=
  MeasureTheory.lintegral_map hf measurable_fst

@[simp]
theorem weightMeasure_zero : (0 : Varifold E n).weightMeasure = 0 := by
  simp [weightMeasure]

@[simp]
theorem weightMeasure_add (V W : Varifold E n) :
    (V + W).weightMeasure = V.weightMeasure + W.weightMeasure := by
  simp [weightMeasure]

@[simp]
theorem weightMeasure_smul (c : ℝ≥0) (V : Varifold E n) :
    (c • V).weightMeasure = c • V.weightMeasure := by
  simp [weightMeasure, Measure.fst, Measure.map_smul]

-- Simon, Chapter 8, Section 1, p. 206: restriction V |_ G_n(A).
def restrict (V : Varifold E n) (s : Set E) : Varifold E n :=
  ⟨V.toMeasure.restrict (s ×ˢ Set.univ), inferInstance⟩

@[simp]
theorem toMeasure_restrict (V : Varifold E n) (s : Set E) :
    (V.restrict s).toMeasure = V.toMeasure.restrict (s ×ˢ Set.univ) := rfl

theorem weightMeasure_restrict (V : Varifold E n) {s : Set E} (hs : MeasurableSet s) :
    (V.restrict s).weightMeasure = V.weightMeasure.restrict s := by
  rw [weightMeasure, toMeasure_restrict, weightMeasure, Measure.fst, Set.prod_univ]
  exact (Measure.restrict_map measurable_fst hs).symm

end Varifold
