import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.MetricSpace.Infsep

noncomputable section

open Set
open MeasureTheory
open Function Filter
open scoped ENNReal MeasureTheory NNReal Topology

theorem Measure.euclideanHausdorffMeasure_apply_eq_smul
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (d : ℕ) (s : Set X) :
    μHE[d] s =
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] *
        μH[d] s := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

private def openHausdorffContent
    {X : Type*} [PseudoMetricSpace X] (d : ℝ) (r : ℝ≥0∞) (a : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set X) (_ : ∀ n, IsOpen (t n)) (_ : ∀ n, Metric.ediam (t n) ≤ r)
      (_ : a ⊆ ⋃ n, t n),
    ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d

private def hausdorffContent
    {X : Type*} [PseudoMetricSpace X] (d : ℝ) (r : ℝ≥0∞) (a : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set X) (_ : a ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
    ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d

private theorem isOpen_fiber_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} {s u : Set X} (hs : IsCompact s) (hf : ContinuousOn f s)
    (hu : IsOpen u) : IsOpen {y | s ∩ f ⁻¹' {y} ⊆ u} := by
  have hc : IsClosed (f '' (s \ u)) :=
    ((hs.diff hu).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  rw [show {y | s ∩ f ⁻¹' {y} ⊆ u} = (f '' (s \ u))ᶜ by
    ext y
    constructor
    · intro h hy
      obtain ⟨x, ⟨hxs, hxu⟩, hxy⟩ := hy
      exact hxu (h ⟨hxs, by simp [hxy]⟩)
    · intro h x hx
      by_contra hxu
      exact h ⟨x, ⟨hx.1, hxu⟩, by simpa using hx.2⟩]
  exact hc.isOpen_compl

private theorem upperSemicontinuous_iInf_cover
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} {s : Set X} (hs : IsCompact s) (hf : ContinuousOn f s)
    (d : ℝ) (r : ℝ≥0∞) :
    UpperSemicontinuous (fun y => openHausdorffContent d r (s ∩ f ⁻¹' {y})) := by
  apply upperSemicontinuous_iInf
  intro t
  apply upperSemicontinuous_iInf
  intro htopen
  apply upperSemicontinuous_iInf
  intro htdiam
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  let cost : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d
  by_cases hcost : cost < c
  · convert isOpen_fiber_subset hs hf (isOpen_iUnion htopen) using 1
    ext y
    change (⨅ (_ : s ∩ f ⁻¹' {y} ⊆ ⋃ n, t n), cost) < c ↔
      s ∩ f ⁻¹' {y} ⊆ ⋃ n, t n
    constructor
    · intro h
      by_contra hy
      simp [hy] at h
    · intro hy
      exact (iInf_le_of_le hy le_rfl).trans_lt hcost
  · have heq : (fun y => ⨅ (_ : s ∩ f ⁻¹' {y} ⊆ ⋃ n, t n), cost) ⁻¹' Iio c = ∅ := by
      ext y
      by_cases hy : s ∩ f ⁻¹' {y} ⊆ ⋃ n, t n
      · simp [hy, hcost]
      · simp [hy]
    exact heq ▸ isOpen_empty

private theorem measurable_openHausdorffContent_fiber
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [T2Space Y] {f : X → Y} {s : Set X} (hs : IsCompact s)
    (hf : ContinuousOn f s) (d : ℝ) (r : ℝ≥0∞) :
    Measurable (fun y => openHausdorffContent d r (s ∩ f ⁻¹' {y})) :=
  (upperSemicontinuous_iInf_cover hs hf d r).measurable

private theorem exists_thickening_radius
    {d : ℝ} (hd : 0 < d) {a : ℝ≥0∞} {r r' : ℝ≥0} (ha : a ≤ r)
    (hrr' : r < r') {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ a + 2 * ε ≤ r' ∧ (a + 2 * ε) ^ d ≤ a ^ d + η := by
  let ε : ℕ → ℝ≥0 := fun j => (j + 1 : ℝ≥0)⁻¹
  have hε : Tendsto (fun j => (ε j : ℝ≥0∞)) atTop (𝓝 0) := by
    have hfun : (fun j => (ε j : ℝ≥0∞)) =
        (fun n : ℕ => (n : ℝ≥0∞)⁻¹) ∘ fun j => j + 1 := by
      funext j
      simp [ε, Function.comp_apply]
    rw [hfun]
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hadd : Tendsto (fun j => a + 2 * (ε j : ℝ≥0∞)) atTop (𝓝 a) := by
    simpa using (ENNReal.Tendsto.const_mul hε
      (Or.inr ENNReal.ofNat_ne_top)).const_add a
  have ha_top : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top ha
  have hpow_top : a ^ d ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hd.le ha_top).ne
  have hevent_r : ∀ᶠ j in atTop, a + 2 * (ε j : ℝ≥0∞) < r' :=
    hadd.eventually (Iio_mem_nhds (ha.trans_lt (ENNReal.coe_lt_coe.2 hrr')))
  have hevent_pow : ∀ᶠ j in atTop,
      (a + 2 * (ε j : ℝ≥0∞)) ^ d < a ^ d + η :=
    (ENNReal.continuous_rpow_const.tendsto a).comp hadd |>.eventually
      (Iio_mem_nhds (ENNReal.lt_add_right hpow_top hη))
  obtain ⟨j, hjr, hjpow⟩ := (hevent_r.and hevent_pow).exists
  refine ⟨ε j, ?_, hjr.le, hjpow.le⟩
  simp [ε]

private theorem hausdorffContent_le_openHausdorffContent
    {X : Type*} [PseudoMetricSpace X] (d : ℝ) (r : ℝ≥0∞) (a : Set X) :
    hausdorffContent d r a ≤ openHausdorffContent d r a := by
  unfold openHausdorffContent hausdorffContent
  refine le_iInf fun t => le_iInf fun htopen => le_iInf fun htdiam => le_iInf fun htcover => ?_
  exact iInf_le_of_le t (iInf_le_of_le htcover (iInf_le_of_le htdiam le_rfl))

private theorem openHausdorffContent_le_hausdorffContent
    {X : Type*} [PseudoMetricSpace X] {d : ℝ} (hd : 0 < d) {r r' : ℝ≥0}
    (hrr' : r < r') (a : Set X) :
    openHausdorffContent d r' a ≤ hausdorffContent d r a := by
  unfold hausdorffContent
  refine le_iInf fun t => le_iInf fun htcover => le_iInf fun htdiam => ?_
  let cost : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨η, hηpos, hηsum⟩ :=
    ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ
  have hradius : ∀ n, ∃ δ : ℝ≥0, 0 < δ ∧
      Metric.ediam (t n) + 2 * δ ≤ r' ∧
        (Metric.ediam (t n) + 2 * δ) ^ d ≤ Metric.ediam (t n) ^ d + η n := by
    intro n
    exact exists_thickening_radius hd (htdiam n) hrr'
      (ENNReal.coe_ne_zero.mpr (hηpos n).ne')
  choose δ hδpos hδdiam hδpow using hradius
  let u : ℕ → Set X := fun n => Metric.thickening (δ n) (t n)
  have huopen : ∀ n, IsOpen (u n) := fun n => Metric.isOpen_thickening
  have hucover : a ⊆ ⋃ n, u n := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (htcover hx)
    exact mem_iUnion.mpr ⟨n, Metric.self_subset_thickening (hδpos n) _ hxn⟩
  have hudiam : ∀ n, Metric.ediam (u n) ≤ (r' : ℝ≥0∞) := by
    intro n
    exact (Metric.ediam_thickening_le (δ n) (s := t n)).trans (hδdiam n)
  unfold openHausdorffContent
  refine (iInf₂_le_of_le u huopen
    (iInf₂_le_of_le hudiam hucover le_rfl)).trans ?_
  calc
    (∑' n, ⨆ _ : (u n).Nonempty, Metric.ediam (u n) ^ d) ≤
        ∑' n, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) + (η n : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      by_cases hn : (t n).Nonempty
      · have hun : (u n).Nonempty :=
          hn.mono (Metric.self_subset_thickening (hδpos n) (t n))
        simp only [iSup_pos hn, iSup_pos hun]
        exact (ENNReal.rpow_le_rpow
          (Metric.ediam_thickening_le (δ n) (s := t n)) hd.le).trans (hδpow n)
      · have htn : t n = ∅ := not_nonempty_iff_eq_empty.mp hn
        simp [u, htn]
    _ = cost + ∑' n, (η n : ℝ≥0∞) := by
      rw [ENNReal.tsum_add]
    _ ≤ cost + ε := add_le_add le_rfl hηsum.le

private def hausdorffScale (n : ℕ) : ℝ≥0 := (n + 1 : ℝ≥0)⁻¹

private theorem tendsto_hausdorffScale :
    Tendsto (fun n => (hausdorffScale n : ℝ≥0∞)) atTop (𝓝 0) := by
  have hfun : (fun n => (hausdorffScale n : ℝ≥0∞)) =
      (fun n : ℕ => (n : ℝ≥0∞)⁻¹) ∘ fun n => n + 1 := by
    funext n
    simp [hausdorffScale, Function.comp_apply]
  rw [hfun]
  exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

private theorem antitone_hausdorffContent
    {X : Type*} [PseudoMetricSpace X] (d : ℝ) (a : Set X) :
    Antitone (fun r => hausdorffContent d r a) := by
  intro r r' hrr'
  unfold hausdorffContent
  refine le_iInf fun t => le_iInf fun htcover => le_iInf fun htdiam => ?_
  exact iInf₂_le_of_le t htcover (iInf_le_of_le (fun n => (htdiam n).trans hrr') le_rfl)

private theorem antitone_openHausdorffContent
    {X : Type*} [PseudoMetricSpace X] (d : ℝ) (a : Set X) :
    Antitone (fun r => openHausdorffContent d r a) := by
  intro r r' hrr'
  unfold openHausdorffContent
  refine le_iInf fun t => le_iInf fun htopen => le_iInf fun htdiam => le_iInf fun htcover => ?_
  exact iInf₂_le_of_le t htopen
    (iInf₂_le_of_le (fun n => (htdiam n).trans hrr') htcover le_rfl)

private theorem hausdorffMeasure_eq_iSup_hausdorffContent
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (d : ℝ) (a : Set X) :
    μH[d] a = ⨆ n, hausdorffContent d (hausdorffScale n) a := by
  rw [Measure.hausdorffMeasure_apply]
  change (⨆ (r : ℝ≥0∞) (_ : 0 < r), hausdorffContent d r a) =
    ⨆ n, hausdorffContent d (hausdorffScale n) a
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => ?_
    obtain ⟨n, hn⟩ := (tendsto_hausdorffScale.eventually (Iio_mem_nhds hr)).exists
    exact (antitone_hausdorffContent d a hn.le).trans (le_iSup (fun n =>
      hausdorffContent d (hausdorffScale n) a) n)
  · refine iSup_le fun n => ?_
    exact le_iSup₂_of_le (hausdorffScale n) (by simp [hausdorffScale]) le_rfl

private theorem hausdorffMeasure_eq_iSup_openHausdorffContent
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} (hd : 0 < d) (a : Set X) :
    μH[d] a = ⨆ n, openHausdorffContent d (hausdorffScale n) a := by
  rw [hausdorffMeasure_eq_iSup_hausdorffContent]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact (hausdorffContent_le_openHausdorffContent d _ a).trans
      (le_iSup (fun j => openHausdorffContent d (hausdorffScale j) a) n)
  · refine iSup_le fun n => ?_
    have hscale : hausdorffScale (n + 1) < hausdorffScale n := by
      apply NNReal.inv_lt_inv
      · positivity
      · simp
    exact (openHausdorffContent_le_hausdorffContent hd hscale a).trans
      (le_iSup (fun j => hausdorffContent d (hausdorffScale j) a) (n + 1))

theorem ContinuousOn.measurable_hausdorffMeasure_fiber
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
    {f : X → Y} {s : Set X} (hf : ContinuousOn f s) (hs : IsCompact s)
    {d : ℝ} (hd : 0 < d) :
    Measurable (fun y => μH[d] (s ∩ f ⁻¹' {y})) := by
  simp_rw [hausdorffMeasure_eq_iSup_openHausdorffContent hd]
  exact Measurable.iSup fun n => measurable_openHausdorffContent_fiber hs hf d _

private theorem innerProductSpace_volume_le_ediam_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Set E) :
    volume s ≤ Metric.ediam s ^ Module.finrank ℝ E *
      volume (Metric.closedBall (0 : E) 1) := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp
  obtain ⟨x, hx⟩ := hs
  by_cases hdiam : Metric.ediam s = ∞
  · rw [hdiam]
    by_cases hdim : Module.finrank ℝ E = 0
    · have hsubsingleton : Subsingleton E := Module.finrank_zero_iff.mp hdim
      have hsuniv : s = univ := Set.eq_univ_iff_forall.2 fun y => by
        rw [hsubsingleton.elim y x]
        exact hx
      have hball : Metric.closedBall (0 : E) 1 = univ := by
        ext y
        simp [hsubsingleton.elim y 0]
      simp [hsuniv, hball, hdim]
    · simp [hdim, (Metric.measure_closedBall_pos volume (0 : E) zero_lt_one).ne']
  have hsub : s ⊆ Metric.closedBall x (Metric.ediam s).toReal := by
    intro y hy
    rw [Metric.mem_closedBall]
    exact Metric.dist_le_diam_of_mem' hdiam hy hx
  calc
    volume s ≤ volume (Metric.closedBall x (Metric.ediam s).toReal) :=
      measure_mono hsub
    _ = ENNReal.ofReal ((Metric.ediam s).toReal) ^ Module.finrank ℝ E *
        volume (Metric.closedBall (0 : E) 1) := by
      rw [Measure.addHaar_closedBall' volume x (ENNReal.toReal_nonneg)]
      rw [ENNReal.ofReal_pow (ENNReal.toReal_nonneg)]
    _ = Metric.ediam s ^ Module.finrank ℝ E *
        volume (Metric.closedBall (0 : E) 1) := by
      rw [ENNReal.ofReal_toReal hdiam]

private theorem lintegral_openHausdorffContent_fiber_le
    {E F : Type*} [MetricSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hK : K ≠ 0) {k : ℝ} (hk : 0 < k) (r : ℝ≥0∞)
    (hr : r ≠ ∞) :
    ∫⁻ y : F, openHausdorffContent k r (s ∩ f ⁻¹' {y})
        ∂μHE[Module.finrank ℝ F] ≤
      (K : ℝ≥0∞) ^ Module.finrank ℝ F *
        volume (Metric.closedBall (0 : F) 1) *
          openHausdorffContent (k + Module.finrank ℝ F) r s := by
  classical
  let C : ℝ≥0∞ := (K : ℝ≥0∞) ^ Module.finrank ℝ F *
    volume (Metric.closedBall (0 : F) 1)
  have hC0 : C ≠ 0 := by
    simp [C, hK, (Metric.measure_closedBall_pos volume (0 : F) zero_lt_one).ne']
  have hCtop : C ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    · exact measure_closedBall_lt_top.ne
  change (∫⁻ y : F, openHausdorffContent k r (s ∩ f ⁻¹' {y})
      ∂μHE[Module.finrank ℝ F]) ≤ C * openHausdorffContent
        (k + Module.finrank ℝ F) r s
  unfold openHausdorffContent
  simp only [ENNReal.mul_iInf_of_ne hC0 hCtop]
  refine le_iInf fun t => le_iInf fun htopen => le_iInf fun htdiam => le_iInf fun htcover => ?_
  let a : ℕ → Set F := fun j => closure (f '' (s ∩ t j))
  have hameas : ∀ j, MeasurableSet (a j) := fun _ => isClosed_closure.measurableSet
  let q : F → ℝ≥0∞ := fun y =>
    ∑' j, (a j).indicator (fun _ => Metric.ediam (t j) ^ k) y
  have hqmeas : Measurable q := Measurable.tsum fun j =>
    measurable_const.indicator (hameas j)
  have hpoint : ∀ y : F,
      openHausdorffContent k r (s ∩ f ⁻¹' {y}) ≤ q y := by
    intro y
    let u : ℕ → Set E := fun j => if y ∈ a j then t j else ∅
    have huopen : ∀ j, IsOpen (u j) := by
      intro j
      by_cases hj : y ∈ a j <;> simp [u, hj, htopen j]
    have hudiam : ∀ j, Metric.ediam (u j) ≤ r := by
      intro j
      by_cases hj : y ∈ a j
      · simpa [u, hj] using htdiam j
      · simp [u, hj]
    have hucover : s ∩ f ⁻¹' {y} ⊆ ⋃ j, u j := by
      intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.1 (htcover hx.1)
      apply mem_iUnion.2
      refine ⟨j, ?_⟩
      have hyj : y ∈ a j := by
        apply subset_closure
        exact ⟨x, ⟨hx.1, hxj⟩, by simpa using hx.2⟩
      simpa [u, hyj] using hxj
    refine (iInf₂_le_of_le u huopen
      (iInf₂_le_of_le hudiam hucover le_rfl)).trans ?_
    apply ENNReal.tsum_le_tsum
    intro j
    by_cases hj : y ∈ a j
    · have htjne : (t j).Nonempty := by
        have himage : (f '' (s ∩ t j)).Nonempty :=
          Set.Nonempty.of_closure ⟨y, hj⟩
        obtain ⟨z, hz⟩ := himage
        obtain ⟨x, hx, -⟩ := hz
        exact ⟨x, hx.2⟩
      simp [u, hj, htjne]
    · simp [u, hj]
  calc
    (∫⁻ y : F, openHausdorffContent k r (s ∩ f ⁻¹' {y})
        ∂μHE[Module.finrank ℝ F]) ≤ ∫⁻ y : F, q y
          ∂μHE[Module.finrank ℝ F] := lintegral_mono hpoint
    _ = ∑' j, μHE[Module.finrank ℝ F] (a j) * Metric.ediam (t j) ^ k := by
      rw [show q = fun y => ∑' j,
          (a j).indicator (fun _ => Metric.ediam (t j) ^ k) y from rfl]
      rw [MeasureTheory.lintegral_tsum fun j =>
        (measurable_const.indicator (hameas j)).aemeasurable]
      apply tsum_congr
      intro j
      rw [MeasureTheory.lintegral_indicator (hameas j)]
      simp [mul_comm]
    _ ≤ ∑' j, C * Metric.ediam (t j) ^ (k + Module.finrank ℝ F) := by
      apply ENNReal.tsum_le_tsum
      intro j
      have himage : Metric.ediam (a j) ≤
          (K : ℝ≥0∞) * Metric.ediam (t j) := by
        calc
          Metric.ediam (a j) = Metric.ediam (f '' (s ∩ t j)) :=
            by exact Metric.ediam_closure (s := f '' (s ∩ t j))
          _ ≤ (K : ℝ≥0∞) * Metric.ediam (s ∩ t j) :=
            by simpa using hf.holderOnWith.ediam_image_le_of_subset inter_subset_left
          _ ≤ (K : ℝ≥0∞) * Metric.ediam (t j) := by
            exact mul_right_mono (Metric.ediam_mono inter_subset_right)
      calc
        μHE[Module.finrank ℝ F] (a j) * Metric.ediam (t j) ^ k =
            volume (a j) * Metric.ediam (t j) ^ k := by
          rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
        _ ≤ (Metric.ediam (a j) ^ Module.finrank ℝ F *
              volume (Metric.closedBall (0 : F) 1)) * Metric.ediam (t j) ^ k := by
          gcongr
          exact innerProductSpace_volume_le_ediam_pow (a j)
        _ ≤ (((K : ℝ≥0∞) * Metric.ediam (t j)) ^ Module.finrank ℝ F *
              volume (Metric.closedBall (0 : F) 1)) * Metric.ediam (t j) ^ k := by
          gcongr
        _ = C * Metric.ediam (t j) ^ (k + Module.finrank ℝ F) := by
          by_cases hd0 : Metric.ediam (t j) = 0
          · rw [hd0, ENNReal.zero_rpow_of_pos hk, mul_zero,
              ENNReal.zero_rpow_of_pos
                (show 0 < k + (Module.finrank ℝ F : ℝ) by positivity), mul_zero]
          · have hdtop : Metric.ediam (t j) ≠ ∞ :=
              ne_top_of_le_ne_top hr (htdiam j)
            rw [mul_pow, ENNReal.rpow_add _ _ hd0 hdtop, ENNReal.rpow_natCast]
            simp only [C]
            ac_rfl
    _ = C * ∑' j, ⨆ _ : (t j).Nonempty,
          Metric.ediam (t j) ^ (k + Module.finrank ℝ F) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro j
      by_cases hj : (t j).Nonempty
      · simp [hj]
      · have htj : t j = ∅ := not_nonempty_iff_eq_empty.mp hj
        rw [htj, Metric.ediam_empty, ENNReal.zero_rpow_of_pos
          (show 0 < k + (Module.finrank ℝ F : ℝ) by positivity)]
        simp

private theorem lipschitzOnWith_lintegral_hausdorffMeasure_fiber_le_compact
    {E F : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : IsCompact s) (hK : K ≠ 0) {k : ℝ} (hk : 0 < k) :
    ∫⁻ y : F, μH[k] (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F] ≤
      (K : ℝ≥0∞) ^ Module.finrank ℝ F *
        volume (Metric.closedBall (0 : F) 1) *
          μH[k + Module.finrank ℝ F] s := by
  let C : ℝ≥0∞ := (K : ℝ≥0∞) ^ Module.finrank ℝ F *
    volume (Metric.closedBall (0 : F) 1)
  have hscale : Antitone (fun n : ℕ => (hausdorffScale n : ℝ≥0∞)) := by
    intro n m hnm
    dsimp only [hausdorffScale]
    exact_mod_cast inv_anti₀ (show 0 < ((n + 1 : ℕ) : ℝ≥0) by positivity)
      (show ((n + 1 : ℕ) : ℝ≥0) ≤ (m + 1 : ℕ) by
        exact_mod_cast Nat.add_le_add_right hnm 1)
  have hmeas : ∀ n, Measurable (fun y : F =>
      openHausdorffContent k (hausdorffScale n) (s ∩ f ⁻¹' {y})) := fun n =>
    measurable_openHausdorffContent_fiber hs hf.continuousOn k _
  have hmono : Monotone (fun n => fun y : F =>
      openHausdorffContent k (hausdorffScale n) (s ∩ f ⁻¹' {y})) := by
    intro n m hnm y
    exact antitone_openHausdorffContent k (s ∩ f ⁻¹' {y}) (hscale hnm)
  calc
    (∫⁻ y : F, μH[k] (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F]) =
        ∫⁻ y : F, ⨆ n, openHausdorffContent k (hausdorffScale n)
          (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F] := by
      apply lintegral_congr
      intro y
      exact hausdorffMeasure_eq_iSup_openHausdorffContent hk _
    _ = ⨆ n, ∫⁻ y : F, openHausdorffContent k (hausdorffScale n)
          (s ∩ f ⁻¹' {y}) ∂μHE[Module.finrank ℝ F] :=
      MeasureTheory.lintegral_iSup hmeas hmono
    _ ≤ C * μH[k + Module.finrank ℝ F] s := by
      refine iSup_le fun n => ?_
      exact (lintegral_openHausdorffContent_fiber_le hf hK hk
        (hausdorffScale n) (by simp [hausdorffScale])).trans
          (mul_right_mono ((le_iSup (fun j =>
            openHausdorffContent (k + Module.finrank ℝ F) (hausdorffScale j) s) n).trans_eq
              (hausdorffMeasure_eq_iSup_openHausdorffContent
                (show 0 < k + (Module.finrank ℝ F : ℝ) by positivity) s).symm))
    _ = (K : ℝ≥0∞) ^ Module.finrank ℝ F *
        volume (Metric.closedBall (0 : F) 1) *
          μH[k + Module.finrank ℝ F] s := rfl

private theorem exists_open_cover_ediam_cost_lt
    {X : Type*} [PseudoMetricSpace X] (d : ℝ) (r : ℝ≥0∞) (s : Set X)
    {c : ℝ≥0∞} (h : openHausdorffContent d r s < c) :
    ∃ t : ℕ → Set X, (∀ j, IsOpen (t j)) ∧
      (∀ j, Metric.ediam (t j) ≤ r) ∧ s ⊆ ⋃ j, t j ∧
        ∑' j, ⨆ _ : (t j).Nonempty, Metric.ediam (t j) ^ d < c := by
  unfold openHausdorffContent at h
  simpa only [iInf_lt_iff, exists_prop] using h

theorem LipschitzOnWith.exists_measurable_hausdorffMeasure_fiber_majorant
    {E F : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    {k : ℝ} (hk : 0 < k)
    (hfin : μH[k + Module.finrank ℝ F] s ≠ ∞) :
    ∃ q : F → ℝ≥0∞, Measurable q ∧
      (∀ y, μH[k] (s ∩ f ⁻¹' {y}) ≤ q y) ∧
        ∫⁻ y : F, q y ∂μHE[Module.finrank ℝ F] ≤
          (K : ℝ≥0∞) ^ Module.finrank ℝ F *
            volume (Metric.closedBall (0 : F) 1) *
              μH[k + Module.finrank ℝ F] s := by
  classical
  let d : ℝ := k + Module.finrank ℝ F
  let C : ℝ≥0∞ := (K : ℝ≥0∞) ^ Module.finrank ℝ F *
    volume (Metric.closedBall (0 : F) 1)
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hcontent : ∀ n,
      openHausdorffContent d (hausdorffScale n) s ≤ μH[d] s := by
    intro n
    exact (le_iSup (fun j => openHausdorffContent d (hausdorffScale j) s) n).trans_eq
      (hausdorffMeasure_eq_iSup_openHausdorffContent hd s).symm
  have hcover : ∀ n, ∃ t : ℕ → Set E, (∀ j, IsOpen (t j)) ∧
      (∀ j, Metric.ediam (t j) ≤ hausdorffScale n) ∧ s ⊆ ⋃ j, t j ∧
        ∑' j, ⨆ _ : (t j).Nonempty, Metric.ediam (t j) ^ d <
          μH[d] s + hausdorffScale n := by
    intro n
    apply exists_open_cover_ediam_cost_lt d (hausdorffScale n) s
    exact (hcontent n).trans_lt (ENNReal.lt_add_right hfin (by simp [hausdorffScale]))
  choose t htopen htdiam htcover htcost using hcover
  let a : ℕ → ℕ → Set F := fun n j => closure (f '' (s ∩ t n j))
  let q : ℕ → F → ℝ≥0∞ := fun n y =>
    ∑' j, (a n j).indicator (fun _ => Metric.ediam (t n j) ^ k) y
  have hameas : ∀ n j, MeasurableSet (a n j) := fun _ _ => isClosed_closure.measurableSet
  have hqmeas : ∀ n, Measurable (q n) := by
    intro n
    exact Measurable.tsum fun j => measurable_const.indicator (hameas n j)
  have hpoint : ∀ y : F,
      μH[k] (s ∩ f ⁻¹' {y}) ≤ liminf (fun n => q n y) atTop := by
    intro y
    let u : ℕ → ℕ → Set E := fun n j => if y ∈ a n j then t n j else ∅
    have hudiam : ∀ n j, Metric.ediam (u n j) ≤ hausdorffScale n := by
      intro n j
      by_cases hj : y ∈ a n j
      · simpa [u, hj] using htdiam n j
      · simp [u, hj]
    have hucover : ∀ n, s ∩ f ⁻¹' {y} ⊆ ⋃ j, u n j := by
      intro n x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.1 (htcover n hx.1)
      apply mem_iUnion.2
      refine ⟨j, ?_⟩
      have hyj : y ∈ a n j := by
        apply subset_closure
        exact ⟨x, ⟨hx.1, hxj⟩, by simpa using hx.2⟩
      simpa [u, hyj] using hxj
    have hmain := Measure.hausdorffMeasure_le_liminf_tsum k
      (s ∩ f ⁻¹' {y}) (fun n => (hausdorffScale n : ℝ≥0∞))
      tendsto_hausdorffScale u (Eventually.of_forall hudiam)
      (Eventually.of_forall hucover)
    refine hmain.trans_eq ?_
    congr 1
    funext n
    apply tsum_congr
    intro j
    by_cases hj : y ∈ a n j
    · simp [u, hj]
    · simp [u, hj, hk]
  have hqintegral : ∀ n, ∫⁻ y : F, q n y ∂μHE[Module.finrank ℝ F] ≤
      C * (μH[d] s + hausdorffScale n) := by
    intro n
    calc
      (∫⁻ y : F, q n y ∂μHE[Module.finrank ℝ F]) =
          ∑' j, μHE[Module.finrank ℝ F] (a n j) * Metric.ediam (t n j) ^ k := by
        rw [show q n = fun y => ∑' j,
            (a n j).indicator (fun _ => Metric.ediam (t n j) ^ k) y from rfl]
        rw [MeasureTheory.lintegral_tsum fun j =>
          (measurable_const.indicator (hameas n j)).aemeasurable]
        apply tsum_congr
        intro j
        rw [MeasureTheory.lintegral_indicator (hameas n j)]
        simp [mul_comm]
      _ ≤ ∑' j, C * Metric.ediam (t n j) ^ d := by
        apply ENNReal.tsum_le_tsum
        intro j
        have himage : Metric.ediam (a n j) ≤
            (K : ℝ≥0∞) * Metric.ediam (t n j) := by
          calc
            Metric.ediam (a n j) = Metric.ediam (f '' (s ∩ t n j)) :=
              by exact Metric.ediam_closure (s := f '' (s ∩ t n j))
            _ ≤ (K : ℝ≥0∞) * Metric.ediam (s ∩ t n j) :=
              by simpa using hf.holderOnWith.ediam_image_le_of_subset inter_subset_left
            _ ≤ (K : ℝ≥0∞) * Metric.ediam (t n j) :=
              mul_right_mono (Metric.ediam_mono inter_subset_right)
        calc
          μHE[Module.finrank ℝ F] (a n j) * Metric.ediam (t n j) ^ k =
              volume (a n j) * Metric.ediam (t n j) ^ k := by
            rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
          _ ≤ (Metric.ediam (a n j) ^ Module.finrank ℝ F *
                volume (Metric.closedBall (0 : F) 1)) * Metric.ediam (t n j) ^ k := by
            gcongr
            exact innerProductSpace_volume_le_ediam_pow (a n j)
          _ ≤ (((K : ℝ≥0∞) * Metric.ediam (t n j)) ^ Module.finrank ℝ F *
                volume (Metric.closedBall (0 : F) 1)) * Metric.ediam (t n j) ^ k := by
            gcongr
          _ = C * Metric.ediam (t n j) ^ d := by
            by_cases hd0 : Metric.ediam (t n j) = 0
            · rw [hd0, ENNReal.zero_rpow_of_pos hk, mul_zero,
                ENNReal.zero_rpow_of_pos hd, mul_zero]
            · have hdtop : Metric.ediam (t n j) ≠ ∞ :=
                ne_top_of_le_ne_top (by simp [hausdorffScale]) (htdiam n j)
              rw [mul_pow, show d = k + Module.finrank ℝ F from rfl,
                ENNReal.rpow_add _ _ hd0 hdtop, ENNReal.rpow_natCast]
              simp only [C]
              ac_rfl
      _ ≤ C * ∑' j, ⨆ _ : (t n j).Nonempty, Metric.ediam (t n j) ^ d := by
        rw [ENNReal.tsum_mul_left]
        gcongr with j
        by_cases hj : (t n j).Nonempty
        · simp [hj]
        · have htj : t n j = ∅ := not_nonempty_iff_eq_empty.mp hj
          simp [htj, hd]
      _ ≤ C * (μH[d] s + hausdorffScale n) := by
        gcongr
        exact (htcost n).le
  let Q : F → ℝ≥0∞ := fun y => liminf (fun n => q n y) atTop
  refine ⟨Q, Measurable.liminf hqmeas, hpoint, ?_⟩
  calc
    (∫⁻ y : F, Q y ∂μHE[Module.finrank ℝ F]) ≤
        liminf (fun n => ∫⁻ y : F, q n y ∂μHE[Module.finrank ℝ F]) atTop :=
      MeasureTheory.lintegral_liminf_le' fun n => (hqmeas n).aemeasurable
    _ ≤ liminf (fun n => C * (μH[d] s + hausdorffScale n)) atTop :=
      Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hqintegral)
    _ = C * μH[d] s := by
      have hadd : Tendsto (fun n => μH[d] s + (hausdorffScale n : ℝ≥0∞))
          atTop (𝓝 (μH[d] s)) := by
        simpa using tendsto_hausdorffScale.const_add (μH[d] s)
      have hCtop : C ≠ ∞ := by
        apply ENNReal.mul_ne_top
        · simp
        · exact measure_closedBall_lt_top.ne
      apply Filter.Tendsto.liminf_eq
      exact ENNReal.Tendsto.const_mul hadd (Or.inr hCtop)
    _ = (K : ℝ≥0∞) ^ Module.finrank ℝ F *
        volume (Metric.closedBall (0 : F) 1) *
          μH[k + Module.finrank ℝ F] s := rfl

private theorem nullMeasurableSet_image_hausdorffMeasure_of_measurableSet
    {X Y : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {s : Set X}
    {K : ℝ≥0} {d : ℝ} (hf : LipschitzOnWith K f s) (hd : 0 ≤ d)
    (hs : MeasurableSet s) (hfin : μH[d] s ≠ ∞) :
    NullMeasurableSet (f '' s) μH[d] := by
  let μ : Measure X := μH[d]
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hfin
  have hclosed : ∀ n : ℕ, ∃ c : Set X, c ⊆ s ∧ IsClosed c ∧
      (μ.restrict s) (s \ c) < (n : ℝ≥0∞)⁻¹ := by
    intro n
    exact hs.exists_isClosed_sdiff_lt (μ := μ.restrict s)
      (measure_ne_top (μ.restrict s) s) (ENNReal.inv_ne_zero.mpr (by simp))
  choose c hcsub hcclosed hclt using hclosed
  let u : Set X := ⋃ n, c n
  have husub : u ⊆ s := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact hcsub n hxn
  have hsdu : μ (s \ u) = 0 := by
    apply le_antisymm
    · apply ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero
      intro n
      calc
        μ (s \ u) ≤ (μ.restrict s) (s \ c n) := by
          rw [Measure.restrict_apply (hs.diff (hcclosed n).measurableSet)]
          apply measure_mono
          intro x hx
          exact ⟨⟨hx.1, fun hxc => hx.2 (mem_iUnion.mpr ⟨n, hxc⟩)⟩, hx.1⟩
        _ ≤ (n : ℝ≥0∞)⁻¹ := (hclt n).le
    · exact bot_le
  let v : Set Y := ⋃ n, ⋃ j, f '' (c n ∩ compactCovering X j)
  have hvmeas : MeasurableSet v := by
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro j
    have hcomp : IsCompact (c n ∩ compactCovering X j) :=
      (isCompact_compactCovering X j).inter_left (hcclosed n)
    exact (hcomp.image_of_continuousOn
      (hf.continuousOn.mono fun x hx => hcsub n hx.1)).measurableSet
  have hv : v = f '' u := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hy⟩ := mem_iUnion.mp hy
      obtain ⟨j, x, hxc, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, mem_iUnion.mpr ⟨n, hxc.1⟩, rfl⟩
    · rintro ⟨x, hxu, rfl⟩
      obtain ⟨n, hxc⟩ := mem_iUnion.mp hxu
      obtain ⟨j, hxj⟩ := exists_mem_compactCovering x
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨j, ⟨x, ⟨hxc, hxj⟩, rfl⟩⟩⟩
  have hnull : μH[d] (f '' (s \ u)) = 0 := by
    apply le_antisymm
    · calc
        μH[d] (f '' (s \ u)) ≤ (K : ℝ≥0∞) ^ d * μH[d] (s \ u) :=
          (hf.mono sdiff_subset).hausdorffMeasure_image_le hd
        _ = 0 := by rw [show μH[d] (s \ u) = 0 by simpa [μ] using hsdu, mul_zero]
    · exact bot_le
  have himage : f '' s = f '' u ∪ f '' (s \ u) := by
    rw [← image_union]
    congr 1
    rw [union_comm, sdiff_union_of_subset husub]
  rw [himage, ← hv]
  exact hvmeas.nullMeasurableSet.union_null hnull

theorem LipschitzOnWith.nullMeasurableSet_image_hausdorffMeasure
    {X Y : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {s : Set X}
    {K : ℝ≥0} {d : ℝ} (hf : LipschitzOnWith K f s) (hd : 0 ≤ d)
    (hs : NullMeasurableSet s μH[d]) (hfin : μH[d] s ≠ ∞) :
    NullMeasurableSet (f '' s) μH[d] := by
  obtain ⟨t, hts, ht, hts_ae⟩ := hs.exists_measurable_subset_ae_eq
  have htfin : μH[d] t ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hts)
  have htimage : NullMeasurableSet (f '' t) μH[d] :=
    nullMeasurableSet_image_hausdorffMeasure_of_measurableSet
      (hf.mono hts) hd ht htfin
  have hsdt : μH[d] (s \ t) = 0 := (ae_eq_set.mp hts_ae).2
  have himagenull : μH[d] (f '' (s \ t)) = 0 := by
    apply le_antisymm
    · calc
        μH[d] (f '' (s \ t)) ≤ (K : ℝ≥0∞) ^ d * μH[d] (s \ t) :=
          (hf.mono sdiff_subset).hausdorffMeasure_image_le hd
        _ = 0 := by rw [hsdt, mul_zero]
    · exact bot_le
  have himage : f '' s = f '' t ∪ f '' (s \ t) := by
    rw [← image_union, union_comm, sdiff_union_of_subset hts]
  rw [himage]
  exact htimage.union_null himagenull

private lemma partition_hits_liminf
    {X : Type*} [MetricSpace X] (p : ℕ → ℕ → Set X)
    (hpbounded : ∀ n j, Bornology.IsBounded (p n j))
    (hpdiam : ∀ n j, Metric.diam (p n j) ≤ 1 / (n + 1 : ℝ))
    (hpcover : ∀ n, ⋃ j, p n j = univ)
    (hpdisj : ∀ n, Pairwise (Disjoint on p n)) (a : Set X) :
    (a.encard : ℝ≥0∞) =
      liminf (fun n => (({j | (a ∩ p n j).Nonempty}.encard : ℕ∞) : ℝ≥0∞)) atTop := by
  let hit : ℕ → Set ℕ := fun n => {j | (a ∩ p n j).Nonempty}
  have hindex_exists : ∀ n x, ∃ j, x ∈ p n j := by
    intro n x
    apply mem_iUnion.mp
    rw [hpcover n]
    exact mem_univ x
  let index : ℕ → X → ℕ := fun n x => (hindex_exists n x).choose
  have hindex : ∀ n x, x ∈ p n (index n x) := fun n x => (hindex_exists n x).choose_spec
  have hupper : ∀ n, (hit n).encard ≤ a.encard := by
    intro n
    let pick : hit n → X := fun j => j.2.choose
    have hpick : ∀ j : hit n, pick j ∈ a ∩ p n j := fun j => j.2.choose_spec
    let toA : hit n → a := fun j => ⟨pick j, (hpick j).1⟩
    have hinj : Injective toA := by
      intro i j hij
      apply Subtype.ext
      by_contra hne
      have hvalue : pick i = pick j := congrArg Subtype.val hij
      exact Set.disjoint_left.mp (hpdisj n hne) (hpick i).2 (by
        rw [hvalue]
        exact (hpick j).2)
    change ENat.card (hit n) ≤ ENat.card a
    exact ENat.card_le_card_of_injective hinj
  have hfinite_lower : ∀ (t : Set X), t.Finite → t ⊆ a →
      ∀ᶠ n in atTop, (t.encard : ℝ≥0∞) ≤ (hit n).encard := by
    intro t htfin hta
    have hcard_lower : ∀ n, (∀ x ∈ t, ∀ y ∈ t, x ≠ y →
        Metric.diam (p n (index n x)) < dist x y) → t.encard ≤ (hit n).encard := by
      intro n hsep
      let toHit : t → hit n := fun x =>
        ⟨index n x, ⟨x, hta x.2, hindex n x⟩⟩
      have hinj : Injective toHit := by
        intro x y hxy
        apply Subtype.ext
        by_contra hne
        have hindexeq : index n x = index n y := congrArg Subtype.val hxy
        have hymem : y.1 ∈ p n (index n x) := by
          rw [hindexeq]
          exact hindex n y
        have hdxy : dist x y ≤ Metric.diam (p n (index n x)) :=
          Metric.dist_le_diam_of_mem (hpbounded n (index n x)) (hindex n x) hymem
        exact (not_lt_of_ge hdxy) (hsep x x.2 y y.2 hne)
      change ENat.card t ≤ ENat.card (hit n)
      exact ENat.card_le_card_of_injective hinj
    by_cases ht : t.Nontrivial
    · have htpos : 0 < t.infsep := htfin.infsep_pos_iff_nontrivial.mpr ht
      have hevent : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < t.infsep :=
        (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 _ htpos
      filter_upwards [hevent] with n hn
      apply ENat.toENNReal_mono
      apply hcard_lower n
      intro x hx y hy hxy
      exact (hpdiam n (index n x)).trans_lt
        (hn.trans_le (Set.infsep_le_dist_of_mem hx hy hxy))
    · have htsub : t.Subsingleton := not_nontrivial_iff.mp ht
      apply Eventually.of_forall
      intro n
      apply ENat.toENNReal_mono
      apply hcard_lower n
      intro x hx y hy hxy
      exact (hxy (htsub hx hy)).elim
  have heventually_le_liminf : ∀ {c : ℝ≥0∞},
      (∀ᶠ n in atTop, c ≤ (hit n).encard) →
        c ≤ liminf (fun n => ((hit n).encard : ℝ≥0∞)) atTop := by
    intro c hc
    rw [liminf_eq_iSup_iInf_of_nat]
    obtain ⟨N, hN⟩ := eventually_atTop.mp hc
    refine le_iSup_of_le N ?_
    exact le_iInf fun i => le_iInf fun hi => hN i hi
  have hlower : (a.encard : ℝ≥0∞) ≤
      liminf (fun n => ((hit n).encard : ℝ≥0∞)) atTop := by
    obtain hafin | hainf := a.finite_or_infinite
    · exact heventually_le_liminf (hfinite_lower a hafin Subset.rfl)
    · have hacard : a.encard = ⊤ := Set.encard_eq_top hainf
      rw [hacard, ENat.toENNReal_top, top_le_iff]
      apply ENNReal.eq_top_of_forall_nnreal_le
      intro r
      obtain ⟨n, hrn⟩ := exists_nat_ge r
      obtain ⟨t, hta, htcard⟩ := Set.exists_subset_encard_eq
        (show (n : ℕ∞) ≤ a.encard by rw [hacard]; exact le_top)
      have htfin : t.Finite := Set.finite_of_encard_eq_coe htcard
      calc
        (r : ℝ≥0∞) ≤ n := by exact_mod_cast hrn
        _ = (t.encard : ℝ≥0∞) := by rw [htcard]; simp
        _ ≤ liminf (fun n => ((hit n).encard : ℝ≥0∞)) atTop :=
          heventually_le_liminf (hfinite_lower t htfin hta)
  have hlimupper : liminf (fun n => ((hit n).encard : ℝ≥0∞)) atTop ≤
      (a.encard : ℝ≥0∞) := by
    apply liminf_le_of_frequently_le'
    exact (Eventually.of_forall fun n => ENat.toENNReal_mono (hupper n)).frequently
  change (a.encard : ℝ≥0∞) = liminf (fun n => ((hit n).encard : ℝ≥0∞)) atTop
  exact le_antisymm hlower hlimupper

private theorem lipschitzOnWith_encard_fiber
    {X Y : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {s : Set X}
    {K : ℝ≥0} {d : ℝ} (hf : LipschitzOnWith K f s) (hd : 0 ≤ d)
    (hs : NullMeasurableSet s μH[d]) (hfin : μH[d] s ≠ ∞) :
    AEMeasurable (fun y => ((s ∩ f ⁻¹' {y}).encard : ℕ∞) : Y → ℝ≥0∞) μH[d] ∧
      ∫⁻ y : Y, ((s ∩ f ⁻¹' {y}).encard : ℕ∞) ∂μH[d] ≤
        (K : ℝ≥0∞) ^ d * μH[d] s := by
  classical
  have hpartition : ∀ n : ℕ, ∃ p : ℕ → Set X,
      (∀ j, MeasurableSet (p j)) ∧
      (∀ j, Bornology.IsBounded (p j)) ∧
      (∀ j, Metric.diam (p j) ≤ 1 / (n + 1 : ℝ)) ∧
      (⋃ j, p j = univ) ∧ Pairwise (Disjoint on p) := by
    intro n
    exact SeparableSpace.exists_measurable_partition_diam_le X (by positivity)
  choose p hpmeas hpbounded hpdiam hpcover hpdisj using hpartition
  let fiber : Y → Set X := fun y => s ∩ f ⁻¹' {y}
  let hit : ℕ → Y → Set ℕ := fun n y => {j | (fiber y ∩ p n j).Nonempty}
  let q : ℕ → Y → ℝ≥0∞ := fun n y => ((hit n y).encard : ℕ∞)
  let piece : ℕ → ℕ → Set X := fun n j => s ∩ p n j
  have hpiece : ∀ n j, NullMeasurableSet (piece n j) μH[d] := by
    intro n j
    exact hs.inter (hpmeas n j).nullMeasurableSet
  have himage : ∀ n j, NullMeasurableSet (f '' piece n j) μH[d] := by
    intro n j
    apply (hf.mono inter_subset_left).nullMeasurableSet_image_hausdorffMeasure hd
    · exact hpiece n j
    · exact ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have hhit_image : ∀ n y j, j ∈ hit n y ↔ y ∈ f '' piece n j := by
    intro n y j
    constructor
    · rintro ⟨x, ⟨⟨hxs, hxy⟩, hxj⟩⟩
      exact ⟨x, ⟨hxs, hxj⟩, by simpa using hxy⟩
    · rintro ⟨x, ⟨hxs, hxj⟩, hxy⟩
      exact ⟨x, ⟨⟨hxs, by simp [hxy]⟩, hxj⟩⟩
  have hqsum : ∀ n y, q n y =
      ∑' j, (f '' piece n j).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro n y
    calc
      q n y = ∑' _ : hit n y, (1 : ℝ≥0∞) :=
        (ENNReal.tsum_set_one (hit n y)).symm
      _ = ∑' j, (hit n y).indicator (fun _ => (1 : ℝ≥0∞)) j :=
        tsum_subtype (hit n y) (fun _ => (1 : ℝ≥0∞))
      _ = ∑' j, (f '' piece n j).indicator (fun _ => (1 : ℝ≥0∞)) y := by
        apply tsum_congr
        intro j
        change (if j ∈ hit n y then 1 else 0) =
          (if y ∈ f '' piece n j then 1 else 0)
        rw [if_congr (hhit_image n y j) rfl rfl]
  have hqmeas : ∀ n, AEMeasurable (q n) μH[d] := by
    intro n
    rw [show q n = fun y => ∑' j,
        (f '' piece n j).indicator (fun _ => (1 : ℝ≥0∞)) y by
      funext y
      exact hqsum n y]
    exact AEMeasurable.tsum fun j => aemeasurable_const.indicator₀ (himage n j)
  have hlimit : ∀ y, ((fiber y).encard : ℕ∞) = liminf (fun n => q n y) atTop := by
    intro y
    exact partition_hits_liminf p hpbounded hpdiam hpcover hpdisj (fiber y)
  have hfibermeas : AEMeasurable (fun y => ((fiber y).encard : ℕ∞) : Y → ℝ≥0∞) μH[d] := by
    have hlimmeas : AEMeasurable (fun y => liminf (fun n => q n y) atTop) μH[d] := by
      rw [show (fun y => liminf (fun n => q n y) atTop) =
          fun y => ⨆ N : ℕ, ⨅ i : ℕ, ⨅ (_ : N ≤ i), q i y by
        funext y
        rw [liminf_eq_iSup_iInf_of_nat]]
      exact AEMeasurable.iSup fun _ =>
        AEMeasurable.iInf fun i => AEMeasurable.iInf fun _ => hqmeas i
    exact hlimmeas.congr (Eventually.of_forall fun y => (hlimit y).symm)
  have hqintegral : ∀ n, ∫⁻ y : Y, q n y ∂μH[d] ≤
      (K : ℝ≥0∞) ^ d * μH[d] s := by
    intro n
    have hpart : ⋃ j, piece n j = s := by
      simp only [piece, ← inter_iUnion, hpcover n, inter_univ]
    have hdisj : Pairwise (AEDisjoint μH[d] on piece n) := by
      intro i j hij
      exact ((hpdisj n hij).mono inter_subset_right inter_subset_right).aedisjoint
    calc
      (∫⁻ y : Y, q n y ∂μH[d]) =
          ∫⁻ y : Y, ∑' j,
            (f '' piece n j).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μH[d] :=
        lintegral_congr (hqsum n)
      _ = ∑' j, ∫⁻ y : Y,
            (f '' piece n j).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μH[d] :=
        MeasureTheory.lintegral_tsum fun j =>
          aemeasurable_const.indicator₀ (himage n j)
      _ = ∑' j, μH[d] (f '' piece n j) := by
        apply tsum_congr
        intro j
        exact MeasureTheory.lintegral_indicator_one₀ (himage n j)
      _ ≤ ∑' j, (K : ℝ≥0∞) ^ d * μH[d] (piece n j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        exact (hf.mono inter_subset_left).hausdorffMeasure_image_le hd
      _ = (K : ℝ≥0∞) ^ d * ∑' j, μH[d] (piece n j) :=
        ENNReal.tsum_mul_left
      _ = (K : ℝ≥0∞) ^ d * μH[d] s := by
        rw [← MeasureTheory.measure_iUnion₀ hdisj (hpiece n), hpart]
  refine ⟨?_, ?_⟩
  · simpa only [fiber] using hfibermeas
  calc
    (∫⁻ y : Y, ((s ∩ f ⁻¹' {y}).encard : ℕ∞) ∂μH[d]) =
        ∫⁻ y : Y, liminf (fun n => q n y) atTop ∂μH[d] :=
      lintegral_congr fun y => hlimit y
    _ ≤ liminf (fun n => ∫⁻ y : Y, q n y ∂μH[d]) atTop :=
      MeasureTheory.lintegral_liminf_le' hqmeas
    _ ≤ (K : ℝ≥0∞) ^ d * μH[d] s := by
      simpa only [liminf_const] using
        Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hqintegral)

theorem LipschitzOnWith.aemeasurable_encard_fiber
    {X Y : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {s : Set X}
    {K : ℝ≥0} {d : ℝ} (hf : LipschitzOnWith K f s) (hd : 0 ≤ d)
    (hs : NullMeasurableSet s μH[d]) (hfin : μH[d] s ≠ ∞) :
    AEMeasurable (fun y => ((s ∩ f ⁻¹' {y}).encard : ℕ∞) : Y → ℝ≥0∞) μH[d] := by
  exact (lipschitzOnWith_encard_fiber hf hd hs hfin).1

theorem LipschitzOnWith.lintegral_encard_fiber_le
    {X Y : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {s : Set X}
    {K : ℝ≥0} {d : ℝ} (hf : LipschitzOnWith K f s) (hd : 0 ≤ d)
    (hs : NullMeasurableSet s μH[d]) (hfin : μH[d] s ≠ ∞) :
    ∫⁻ y : Y, ((s ∩ f ⁻¹' {y}).encard : ℕ∞) ∂μH[d] ≤
      (K : ℝ≥0∞) ^ d * μH[d] s := by
  exact (lipschitzOnWith_encard_fiber hf hd hs hfin).2
