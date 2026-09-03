import GMT.Linear.Grassmannian.Defs
import Mathlib.MeasureTheory.Measure.Prod

open scoped ENNReal MeasureTheory NNReal

noncomputable section

structure Varifold (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) where
  toMeasure : MeasureTheory.Measure (E × Grassmannian E n)
  protected isFiniteMeasureOnCompacts :
    MeasureTheory.IsFiniteMeasureOnCompacts toMeasure

namespace Varifold

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

instance (V : Varifold E n) : IsFiniteMeasureOnCompacts V.toMeasure :=
  V.isFiniteMeasureOnCompacts

instance : Coe (Varifold E n) (Measure (E × Grassmannian E n)) := ⟨toMeasure⟩

@[ext]
theorem ext {V W : Varifold E n} (h : V.toMeasure = W.toMeasure) : V = W := by
  cases V
  cases W
  simp_all

instance : Zero (Varifold E n) :=
  ⟨⟨0, inferInstance⟩⟩

instance : Add (Varifold E n) :=
  ⟨fun V W => ⟨V.toMeasure + W.toMeasure, by
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩⟩

instance : SMul ℝ≥0 (Varifold E n) :=
  ⟨fun c V => ⟨c • V.toMeasure, inferInstance⟩⟩

instance : AddCommMonoid (Varifold E n) where
  zero := 0
  add := (· + ·)
  add_assoc V W Z := by ext; exact add_assoc _ _ _
  zero_add V := by ext; exact zero_add _
  add_zero V := by ext; exact add_zero _
  add_comm V W := by ext; exact add_comm _ _
  nsmul := nsmulRec

@[simp]
theorem toMeasure_zero : (0 : Varifold E n).toMeasure = 0 := rfl

@[simp]
theorem toMeasure_add (V W : Varifold E n) :
    (V + W).toMeasure = V.toMeasure + W.toMeasure := rfl

@[simp]
theorem toMeasure_smul (c : ℝ≥0) (V : Varifold E n) :
    (c • V).toMeasure = c • V.toMeasure := rfl

def weightMeasure (V : Varifold E n) : Measure E := V.toMeasure.fst

def mass (V : Varifold E n) (s : Set E) : ℝ≥0∞ := V.weightMeasure s

end Varifold
