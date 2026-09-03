import Mathlib.MeasureTheory.Measure.Prod

open Set
open scoped MeasureTheory

namespace MeasureTheory.Measure

variable {α β : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α]
  [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [CompactSpace β]

instance fst.instIsFiniteMeasureOnCompacts {ρ : Measure (α × β)}
    [IsFiniteMeasureOnCompacts ρ] : IsFiniteMeasureOnCompacts ρ.fst where
  lt_top_of_isCompact K hK := by
    rw [fst_apply hK.measurableSet, ← prod_univ]
    exact (hK.prod isCompact_univ).measure_lt_top

end MeasureTheory.Measure
