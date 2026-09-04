import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.LocallyFinite

open Set
open MeasureTheory
open scoped ENNReal MeasureTheory Topology

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] {mu : Measure X} [Measure.WeaklyRegular mu]

private theorem simpleFunc_exists_isClosed_continuousOn
    [TopologicalSpace Y] (f : SimpleFunc X Y) {s : Set X}
    (hs : MeasurableSet s) (hmu : mu s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t ⊆ s, IsClosed t ∧ mu (s \ t) < ε ∧ ContinuousOn f t := by
  let _ : Fintype (Set.range f) := f.finite_range.fintype
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Set.range f)
  have hmeas (y : Set.range f) : MeasurableSet (s ∩ f ⁻¹' {y.1}) :=
    hs.inter (f.measurableSet_fiber y.1)
  have hfinite (y : Set.range f) : mu (s ∩ f ⁻¹' {y.1}) ≠ ∞ :=
    ne_top_of_le_ne_top hmu (measure_mono inter_subset_left)
  choose c hcsub hcclosed hcmeasure using fun y =>
    (hmeas y).exists_isClosed_sdiff_lt (hfinite y) (hδpos y).ne'
  let t : Set X := ⋃ y : Set.range f, c y
  have hts : t ⊆ s := by
    intro x hx
    obtain ⟨y, hxy⟩ := mem_iUnion.1 hx
    exact (hcsub y hxy).1
  have htclosed : IsClosed t := by
    exact isClosed_iUnion_of_finite hcclosed
  have htcontinuous : ContinuousOn f t := by
    apply (locallyFinite_of_finite c).continuousOn_iUnion hcclosed
    intro y
    exact (continuousOn_const : ContinuousOn (fun _ : X => y.1) (c y)).congr fun x hx =>
      (hcsub y hx).2
  refine ⟨t, hts, htclosed, ?_, htcontinuous⟩
  calc
    mu (s \ t) ≤ mu (⋃ y : Set.range f, (s ∩ f ⁻¹' {y.1}) \ c y) := by
      apply measure_mono
      intro x hx
      apply mem_iUnion.2
      let y : Set.range f := ⟨f x, ⟨x, rfl⟩⟩
      refine ⟨y, ⟨⟨hx.1, rfl⟩, ?_⟩⟩
      intro hxc
      exact hx.2 (mem_iUnion.2 ⟨y, hxc⟩)
    _ ≤ ∑' y : Set.range f, mu ((s ∩ f ⁻¹' {y.1}) \ c y) := measure_iUnion_le _
    _ ≤ ∑' y : Set.range f, δ y := ENNReal.tsum_le_tsum fun y => (hcmeasure y).le
    _ < ε := hδsum

theorem StronglyMeasurable.exists_isClosed_continuousOn
    [PseudoMetricSpace Y] {f : X → Y} (hf : StronglyMeasurable f) {s : Set X}
    (hs : MeasurableSet s) (hmu : mu s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t ⊆ s, IsClosed t ∧ mu (s \ t) < ε ∧ ContinuousOn f t := by
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hε (Option (Option ℕ))
  have hδtop (i : Option (Option ℕ)) : δ i ≠ ∞ := by
    exact ne_of_lt ((ENNReal.le_tsum i).trans_lt (hδsum.trans_le le_top))
  have hδreal : 0 < (δ none).toReal :=
    ENNReal.toReal_pos (hδpos none).ne' (hδtop none)
  obtain ⟨b, -, hbmeas, hbmeasure, huniform⟩ :=
    tendstoUniformlyOn_of_ae_tendsto (f := fun n => (hf.approx n : X → Y))
      (g := f) (s := s) (μ := mu)
      (fun n => (hf.approx n).stronglyMeasurable) hf hs hmu
      (Filter.Eventually.of_forall fun x _ => hf.tendsto_approx x) hδreal
  have hbmeasure' : mu b ≤ δ none := by
    simpa [ENNReal.ofReal_toReal (hδtop none)] using hbmeasure
  have hgoodmeas : MeasurableSet (s \ b) := hs.diff hbmeas
  have hgoodfinite : mu (s \ b) ≠ ∞ :=
    ne_top_of_le_ne_top hmu (measure_mono sdiff_subset)
  obtain ⟨c0, hc0sub, hc0closed, hc0measure⟩ :=
    hgoodmeas.exists_isClosed_sdiff_lt hgoodfinite (hδpos (some none)).ne'
  choose c hcsub hcclosed hcmeasure hccontinuous using fun n =>
    simpleFunc_exists_isClosed_continuousOn (hf.approx n) hs hmu
      (hδpos (some (some n))).ne'
  let t : Set X := c0 ∩ ⋂ n, c n
  have hts : t ⊆ s := fun x hx => (hc0sub hx.1).1
  have htclosed : IsClosed t := hc0closed.inter (isClosed_iInter hcclosed)
  have htgood : t ⊆ s \ b := fun _ hx => hc0sub hx.1
  have htcontinuous : ContinuousOn f t := by
    apply (huniform.mono htgood).continuousOn
    exact (Filter.Eventually.of_forall fun n =>
      (hccontinuous n).mono fun x hx => (mem_iInter.1 hx.2) n).frequently
  refine ⟨t, hts, htclosed, ?_, htcontinuous⟩
  have hsubset : s \ t ⊆ b ∪ ((s \ b) \ c0) ∪ ⋃ n, s \ c n := by
    intro x hx
    by_cases hxb : x ∈ b
    · exact Or.inl (Or.inl hxb)
    by_cases hxc0 : x ∈ c0
    · apply Or.inr
      have hxnot : x ∉ ⋂ n, c n := by
        intro hxi
        exact hx.2 ⟨hxc0, hxi⟩
      rw [mem_iInter] at hxnot
      obtain ⟨n, hxn⟩ := Classical.not_forall.mp hxnot
      exact mem_iUnion.2 ⟨n, ⟨hx.1, hxn⟩⟩
    · exact Or.inl (Or.inr ⟨⟨hx.1, hxb⟩, hxc0⟩)
  calc
    mu (s \ t) ≤ mu (b ∪ ((s \ b) \ c0) ∪ ⋃ n, s \ c n) := measure_mono hsubset
    _ ≤ mu b + mu ((s \ b) \ c0) + mu (⋃ n, s \ c n) := by
      calc
        mu (b ∪ ((s \ b) \ c0) ∪ ⋃ n, s \ c n) ≤
            mu (b ∪ ((s \ b) \ c0)) + mu (⋃ n, s \ c n) := measure_union_le _ _
        _ ≤ mu b + mu ((s \ b) \ c0) + mu (⋃ n, s \ c n) := by
          gcongr
          exact measure_union_le _ _
    _ ≤ δ none + δ (some none) + ∑' n, δ (some (some n)) := by
      apply add_le_add
      · exact add_le_add hbmeasure' hc0measure.le
      · exact (measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun n => (hcmeasure n).le)
    _ = ∑' i : Option (Option ℕ), δ i := by
      rw [← (Equiv.optionEquivSumPUnit.{0, 0} (Option ℕ)).symm.tsum_eq δ]
      rw [ENNReal.summable.tsum_sum ENNReal.summable]
      rw [← (Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm.tsum_eq
        (fun i => δ ((Equiv.optionEquivSumPUnit.{0, 0} (Option ℕ)).symm (Sum.inl i)))]
      rw [ENNReal.summable.tsum_sum ENNReal.summable]
      simp [Equiv.optionEquivSumPUnit, add_comm, add_assoc]
    _ < ε := hδsum

theorem StronglyMeasurable.exists_isClosed_continuousOn_of_isLocallyFiniteMeasure
    [SigmaCompactSpace X] [IsLocallyFiniteMeasure mu] [PseudoMetricSpace Y]
    {f : X → Y} (hf : StronglyMeasurable f) {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t ⊆ s, IsClosed t ∧ mu (s \ t) < ε ∧ ContinuousOn f t := by
  classical
  let U := mu.finiteSpanningSetsInOpen
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  choose c hcsub hcclosed hcmeasure hccontinuous using fun n : ℕ =>
    StronglyMeasurable.exists_isClosed_continuousOn hf
      (hs.inter (U.set_mem n).measurableSet)
      (ne_top_of_le_ne_top (U.finite n).ne (measure_mono inter_subset_right))
      (hδpos n).ne'
  let t : Set X := ⋂ n : ℕ, c n ∪ (U.set n)ᶜ
  have hcover (x : X) : ∃ n : ℕ, x ∈ U.set n := by
    have hx : x ∈ ⋃ n : ℕ, U.set n := by
      rw [U.spanning]
      exact mem_univ x
    exact mem_iUnion.1 hx
  have hts : t ⊆ s := by
    intro x hx
    obtain ⟨n, hxn⟩ := hcover x
    have hxterm := mem_iInter.1 hx n
    exact (hcsub n (hxterm.resolve_right fun h => h hxn)).1
  have htclosed : IsClosed t :=
    isClosed_iInter fun n => (hcclosed n).union (U.set_mem n).isClosed_compl
  have htcontinuous : ContinuousOn f t := by
    intro x hx
    obtain ⟨n, hxn⟩ := hcover x
    have hxc : x ∈ c n :=
      (mem_iInter.1 hx n).resolve_right fun h => h hxn
    apply (hccontinuous n x hxc).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset
      (inter_mem_nhdsWithin t ((U.set_mem n).mem_nhds hxn))
    intro y hy
    exact (mem_iInter.1 hy.1 n).resolve_right fun h => h hy.2
  refine ⟨t, hts, htclosed, ?_, htcontinuous⟩
  have hsubset : s \ t ⊆ ⋃ n : ℕ, (s ∩ U.set n) \ c n := by
    intro x hx
    have hxnot : ¬ ∀ n : ℕ, x ∈ c n ∪ (U.set n)ᶜ := by
      simpa only [t, mem_iInter] using hx.2
    obtain ⟨n, hn⟩ := Classical.not_forall.mp hxnot
    apply mem_iUnion.2
    refine ⟨n, ⟨⟨hx.1, ?_⟩, ?_⟩⟩
    · by_contra hxu
      exact hn (Or.inr hxu)
    · intro hxc
      exact hn (Or.inl hxc)
  calc
    mu (s \ t) ≤ mu (⋃ n : ℕ, (s ∩ U.set n) \ c n) := measure_mono hsubset
    _ ≤ ∑' n : ℕ, mu ((s ∩ U.set n) \ c n) := measure_iUnion_le _
    _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => (hcmeasure n).le
    _ < ε := hδsum
