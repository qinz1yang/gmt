import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Euclidean.Volume.Measure
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
