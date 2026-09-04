import GMT.Analysis.Lipschitz
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Data.Set.Card.Arithmetic

open Asymptotics Filter MeasureTheory Metric Set

open scoped ENNReal NNReal Topology

noncomputable section

universe u

def HasStrictFDerivWithinAt
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) : Prop :=
  HasFDerivAtFilter f f' (𝓝[insert x s ×ˢ insert x s] (x, x))

def IsWhitneyOneJetOn
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (f' : E → E →L[𝕜] F) (s : Set E) : Prop :=
  ContinuousOn f' s ∧ ∀ x ∈ s, HasStrictFDerivWithinAt f (f' x) s x

private def IsWhitneyFDerivCompatibleOn
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (f' : E → E →L[𝕜] F) (s : Set E) : Prop :=
  ContinuousOn f s ∧ ContinuousOn f' s ∧
    ∀ K : Set E, IsCompact K → K ⊆ s → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ s, dist y x < δ →
        ‖f y - f x - f' x (y - x)‖ ≤ ε * ‖y - x‖

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]

private theorem exists_closed_measure_sdiff_lt_isWhitneyFDerivCompatibleOn
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [ProperSpace E]
    (f : E → F) (s : Set E) (hs : IsClosed s)
    (f' : E → E →L[ℝ] F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'cont : ContinuousOn f' s)
    {ε : ℝ≥0∞} (εpos : 0 < ε) :
    ∃ K ⊆ s, IsClosed K ∧ μ (s \ K) < ε ∧ IsWhitneyFDerivCompatibleOn f f' K := by
  have hfcont : ContinuousOn f s := fun x hx => (hf' x hx).continuousWithinAt
  have hfcont' : Continuous (s.domRestrict f) := hfcont.domRestrict
  have hf'cont' : Continuous (s.domRestrict f') := hf'cont.domRestrict
  let G : ℕ → ℕ → Set s := fun k n =>
    {x | ∀ y : s,
      1 / (n + 1 : ℝ) ≤ dist x y ∨
        ‖f y - f x - f' x (y - x)‖ ≤ (1 / (k + 1 : ℝ)) * ‖(y : E) - x‖}
  have hGclosed : ∀ k n, IsClosed (G k n) := by
    intro k n
    rw [show G k n = ⋂ y : s,
        {x | 1 / (n + 1 : ℝ) ≤ dist x y ∨
          ‖f y - f x - f' x (y - x)‖ ≤
            (1 / (k + 1 : ℝ)) * ‖(y : E) - x‖} by ext x; simp [G]]
    apply isClosed_iInter
    intro y
    rw [show {x : s | 1 / (n + 1 : ℝ) ≤ dist x y ∨
          ‖f y - f x - f' x (y - x)‖ ≤ (1 / (k + 1 : ℝ)) * ‖(y : E) - x‖} =
        {x | 1 / (n + 1 : ℝ) ≤ dist x y} ∪
          {x | ‖f y - f x - f' x (y - x)‖ ≤
            (1 / (k + 1 : ℝ)) * ‖(y : E) - x‖} by ext; simp]
    apply (isClosed_le continuous_const (continuous_id.dist continuous_const)).union
    apply isClosed_le
    · exact ((continuous_const.sub hfcont').sub
        (hf'cont'.clm_apply (continuous_const.sub continuous_subtype_val))).norm
    · exact continuous_const.mul (continuous_const.sub continuous_subtype_val).norm
  let H : ℕ → ℕ → Set E := fun k n => ((↑) : s → E) '' G k n
  have hHclosed : ∀ k n, IsClosed (H k n) := by
    intro k n
    exact hs.isClosedMap_subtype_val _ (hGclosed k n)
  have hHsub : ∀ k n, H k n ⊆ s := by
    rintro k n x ⟨x', _, rfl⟩
    exact x'.property
  have hHcover : ∀ k, s ⊆ ⋃ n, H k n := by
    intro k x hxs
    have hkpos : 0 < (1 / (k + 1 : ℝ)) := by positivity
    obtain ⟨δ, δpos, hδ⟩ :
        ∃ δ : ℝ, 0 < δ ∧ ball x δ ∩ s ⊆
          {y | ‖f y - f x - f' x (y - x)‖ ≤
            (1 / (k + 1 : ℝ)) * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 ((hf' x hxs).isLittleO.def hkpos)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt δpos
    apply mem_iUnion.2
    refine ⟨n, ⟨⟨x, hxs⟩, ?_, rfl⟩⟩
    intro y
    by_cases hxy : 1 / (n + 1 : ℝ) ≤ dist (⟨x, hxs⟩ : s) y
    · exact Or.inl hxy
    · right
      apply hδ
      refine ⟨?_, y.property⟩
      rw [mem_ball, dist_comm]
      exact (lt_of_not_ge hxy).trans hn
  let U : ℕ → ℕ → Set E := fun k n => ⋃ m ∈ Finset.range n, H k m
  have hUclosed : ∀ k n, IsClosed (U k n) := by
    intro k n
    exact isClosed_biUnion_finset fun m _ => hHclosed k m
  have hUsub : ∀ k n, U k n ⊆ s := by
    intro k n
    exact iUnion_subset fun m => iUnion_subset fun _ => hHsub k m
  have hUmono : ∀ k, Monotone (U k) := by
    intro k n m hnm x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨hin, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨Finset.range_mono hnm hin, hxi⟩⟩
  have hUunion : ∀ k, ⋃ n, U k n = s := by
    intro k
    apply Subset.antisymm
    · exact iUnion_subset fun n => hUsub k n
    · intro x hxs
      obtain ⟨m, hxm⟩ := mem_iUnion.mp (hHcover k hxs)
      refine mem_iUnion.2 ⟨m + 1, ?_⟩
      exact mem_iUnion.2 ⟨m, mem_iUnion.2
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self m), hxm⟩⟩
  let D : ℕ → Set E := fun j => s ∩ closedBall 0 j
  have hDclosed : ∀ j, IsClosed (D j) := fun j => hs.inter isClosed_closedBall
  have hDfinite : ∀ j, μ (D j) ≠ ∞ := by
    intro j
    have hb : μ (closedBall 0 (j : ℝ)) ≠ ∞ :=
      (IsCompact.measure_lt_top (isCompact_closedBall (0 : E) (j : ℝ))).ne
    exact ne_top_of_le_ne_top hb (measure_mono inter_subset_right)
  have hDUunion : ∀ k j, ⋃ n, D j ∩ U k n = D j := by
    intro k j
    rw [← inter_iUnion, hUunion k]
    exact inter_eq_self_of_subset_left inter_subset_left
  have hDUmono : ∀ k j, Monotone (fun n => D j ∩ U k n) := by
    intro k j n m hnm
    exact inter_subset_inter_right _ (hUmono k hnm)
  have hUapprox : ∀ k j (a : ℝ≥0∞), 0 < a → ∃ n, μ (D j \ U k n) < a := by
    intro k j a hapos
    have hlim : Tendsto (fun n => μ (D j ∩ U k n)) atTop (𝓝 (μ (D j))) := by
      have hlim' := tendsto_measure_iUnion_atTop (μ := μ) (hDUmono k j)
      rw [hDUunion k j] at hlim'
      exact hlim'
    obtain ⟨n, hn⟩ : ∃ n, μ (D j) < μ (D j ∩ U k n) + a :=
      ((hlim.add tendsto_const_nhds).eventually
        (Ioi_mem_nhds (ENNReal.lt_add_right (hDfinite j) hapos.ne'))).exists
    have hclosed : IsClosed (D j ∩ U k n) := (hDclosed j).inter (hUclosed k n)
    have hsub : D j ∩ U k n ⊆ D j := inter_subset_left
    have hdiff : D j \ (D j ∩ U k n) = D j \ U k n := by ext; simp
    refine ⟨n, ?_⟩
    rw [← hdiff]
    exact measure_sdiff_lt_of_lt_add hclosed.nullMeasurableSet hsub
      (measure_ne_top_of_subset hsub (hDfinite j)) hn
  obtain ⟨a, hapos, hasum⟩ :=
    ENNReal.exists_pos_sum_of_countable' εpos.ne' (ℕ × ℕ)
  choose n hn using fun p : ℕ × ℕ => hUapprox p.1 p.2 (a p) (hapos p)
  let V : ℕ × ℕ → Set E := fun p =>
    U p.1 (n p) ∪ (ball 0 (p.2 : ℝ))ᶜ
  have hVclosed : ∀ p, IsClosed (V p) := by
    intro p
    exact (hUclosed p.1 (n p)).union isOpen_ball.isClosed_compl
  have hVloss : ∀ p, μ (s \ V p) < a p := by
    intro p
    apply lt_of_le_of_lt (measure_mono ?_) (hn p)
    intro x hx
    refine ⟨⟨hx.1, mem_closedBall.2 ?_⟩, ?_⟩
    · have hxball : x ∈ ball 0 (p.2 : ℝ) := by
        by_contra hxball
        exact hx.2 (Or.inr hxball)
      exact (mem_ball.mp hxball).le
    · intro hxU
      exact hx.2 (Or.inl hxU)
  let K : Set E := s ∩ ⋂ p : ℕ × ℕ, V p
  have hKsub : K ⊆ s := inter_subset_left
  have hKclosed : IsClosed K := hs.inter (isClosed_iInter hVclosed)
  have hKmeasure : μ (s \ K) < ε := by
    calc
      μ (s \ K) = μ (⋃ p : ℕ × ℕ, s \ V p) := by
        rw [show s \ K = s \ ⋂ p : ℕ × ℕ, V p by ext; simp [K], sdiff_iInter]
      _ ≤ ∑' p : ℕ × ℕ, μ (s \ V p) := measure_iUnion_le _
      _ ≤ ∑' p : ℕ × ℕ, a p := ENNReal.tsum_le_tsum fun p => (hVloss p).le
      _ < ε := hasum
  refine ⟨K, hKsub, hKclosed, hKmeasure, ?_⟩
  refine ⟨hfcont.mono hKsub, hf'cont.mono hKsub, ?_⟩
  intro C hC hCK η ηpos
  obtain ⟨r, hrpos, hCr⟩ := hC.isBounded.subset_ball_lt 0 0
  obtain ⟨j, hrj⟩ := exists_nat_gt r
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt ηpos
  refine ⟨1 / (n (k, j) + 1 : ℝ), by positivity, ?_⟩
  intro x hxC y hyK hxy
  have hxK := hCK hxC
  have hxV : x ∈ V (k, j) := mem_iInter.mp hxK.2 (k, j)
  have hxballj : x ∈ ball 0 (j : ℝ) :=
    ball_subset_ball hrj.le (hCr hxC)
  have hxU : x ∈ U k (n (k, j)) := by
    rcases hxV with hxU | hxout
    · exact hxU
    · exact False.elim (hxout hxballj)
  obtain ⟨m, hm⟩ := mem_iUnion.mp hxU
  obtain ⟨hmn, hxm⟩ := mem_iUnion.mp hm
  obtain ⟨x', hxG, hxeq⟩ := hxm
  have hyS : y ∈ s := hKsub hyK
  let y' : s := ⟨y, hyS⟩
  subst x
  have hnm : (m + 1 : ℝ) ≤ n (k, j) + 1 := by
    exact_mod_cast Nat.add_le_add_right (Finset.mem_range.mp hmn).le 1
  have hradius : 1 / (n (k, j) + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
    gcongr
  have hrem := hxG y'
  rcases hrem with hfar | hrem
  · have hnear : dist x' y' < 1 / (m + 1 : ℝ) := by
      simpa only [y', Subtype.dist_eq, dist_comm] using hxy.trans_le hradius
    exact False.elim (not_le_of_gt hnear hfar)
  · exact hrem.trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem IsWhitneyFDerivCompatibleOn.isWhitneyOneJetOn [ProperSpace E]
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
    (h : IsWhitneyFDerivCompatibleOn f f' s) (hs : IsClosed s) :
    IsWhitneyOneJetOn f f' s := by
  refine ⟨h.2.1, ?_⟩
  intro x hx
  rw [HasStrictFDerivWithinAt, insert_eq_of_mem hx, nhdsWithin_prod_eq]
  apply HasFDerivAtFilter.of_isLittleO
  apply isLittleO_iff.2
  intro c hc
  let C : Set E := s ∩ closedBall x 1
  have hCcompact : IsCompact C :=
    IsCompact.inter_left (isCompact_closedBall x 1) hs
  obtain ⟨δ, hδ, hrem⟩ := h.2.2 C hCcompact inter_subset_left (c / 2) (half_pos hc)
  have hdist : {p : E × E | dist p.1 p.2 < δ} ∈ 𝓝 (x, x) := by
    exact (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).mem_nhds
      (by simpa using hδ)
  have hderiv : ∀ᶠ y in 𝓝[s] x, ‖f' y - f' x‖ < c / 2 := by
    have hball := (h.2.1 x hx) (Metric.ball_mem_nhds (f' x) (half_pos hc))
    change ∀ᶠ y in 𝓝[s] x, y ∈ f' ⁻¹' ball (f' x) (c / 2) at hball
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using hball
  have hclosedBall : ∀ᶠ y in 𝓝[s] x, y ∈ closedBall x 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (closedBall_mem_nhds x zero_lt_one)
  have hC : ∀ᶠ y in 𝓝[s] x, y ∈ C := by
    filter_upwards [eventually_mem_nhdsWithin, hclosedBall] with y hys hyball
    exact ⟨hys, hyball⟩
  have hdist' : {p : E × E | dist p.1 p.2 < δ} ∈ 𝓝[s] x ×ˢ 𝓝[s] x := by
    rw [nhds_prod_eq] at hdist
    exact (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds) hdist
  filter_upwards [hdist',
    tendsto_snd.eventually hderiv,
    tendsto_snd.eventually hC,
    tendsto_fst.eventually eventually_mem_nhdsWithin] with p hpdist hpderiv hp2 hp1
  have hfirst := hrem p.2 hp2 p.1 hp1 hpdist
  calc
    ‖f p.1 - f p.2 - f' x (p.1 - p.2)‖ =
        ‖(f p.1 - f p.2 - f' p.2 (p.1 - p.2)) +
          (f' p.2 - f' x) (p.1 - p.2)‖ := by
            congr 1
            simp only [sub_apply]
            abel
    _ ≤ ‖f p.1 - f p.2 - f' p.2 (p.1 - p.2)‖ +
        ‖(f' p.2 - f' x) (p.1 - p.2)‖ := norm_add_le _ _
    _ ≤ (c / 2) * ‖p.1 - p.2‖ + (c / 2) * ‖p.1 - p.2‖ := by
      apply add_le_add hfirst
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hpderiv.le (norm_nonneg _))
    _ = c * ‖p.1 - p.2‖ := by ring

theorem exists_closed_measure_sdiff_lt_isWhitneyOneJetOn
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [ProperSpace E]
    (f : E → F) (s : Set E) (hs : IsClosed s)
    (f' : E → E →L[ℝ] F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'cont : ContinuousOn f' s)
    {ε : ℝ≥0∞} (εpos : 0 < ε) :
    ∃ K ⊆ s, IsClosed K ∧ μ (s \ K) < ε ∧ IsWhitneyOneJetOn f f' K := by
  obtain ⟨K, hKs, hKclosed, hKmeasure, hK⟩ :=
    exists_closed_measure_sdiff_lt_isWhitneyFDerivCompatibleOn
      μ f s hs f' hf' hf'cont εpos
  exact ⟨K, hKs, hKclosed, hKmeasure, hK.isWhitneyOneJetOn hKclosed⟩

theorem LipschitzWith.exists_isClosed_isWhitneyOneJetOn
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set E, IsClosed s ∧ (Measure.addHaar : Measure E) sᶜ < ε ∧
      IsWhitneyOneJetOn f (fderiv ℝ f) s := by
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε
  obtain ⟨s, hsclosed, hsmeasure, hsderiv, hscontinuous⟩ :=
    hf.exists_isClosed_differentiableAt_continuousOn_fderiv hhalf.ne'
  obtain ⟨t, hts, htclosed, htmeasure, htjet⟩ :=
    exists_closed_measure_sdiff_lt_isWhitneyOneJetOn
      (Measure.addHaar : Measure E) f s hsclosed (fderiv ℝ f)
      (fun x hx => (hsderiv x hx).hasFDerivAt.hasFDerivWithinAt)
      hscontinuous hhalf
  refine ⟨t, htclosed, ?_, htjet⟩
  have htcompl : tᶜ = sᶜ ∪ (s \ t) := by
    ext x
    constructor
    · intro hxt
      by_cases hxs : x ∈ s
      · exact Or.inr ⟨hxs, hxt⟩
      · exact Or.inl hxs
    · rintro (hxs | ⟨hxs, hxt⟩) hxt'
      · exact hxs (hts hxt')
      · exact hxt hxt'
  rw [htcompl]
  calc
    (Measure.addHaar : Measure E) (sᶜ ∪ (s \ t)) ≤
        (Measure.addHaar : Measure E) sᶜ +
          (Measure.addHaar : Measure E) (s \ t) := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hsmeasure htmeasure
    _ = ε := ENNReal.add_halves ε

private def whitneyRadius {E : Type*} [PseudoMetricSpace E] (s : Set E) (x : E) : ℝ :=
  min 1 (infDist x s) / 32

private def whitneyScale {E : Type*} [PseudoMetricSpace E] (s : Set E) (x : E) : ℝ :=
  min 1 (infDist x s)

private theorem whitneyScale_nonneg
    {E : Type*} [PseudoMetricSpace E] (s : Set E) (x : E) :
    0 ≤ whitneyScale s x := by
  exact le_min zero_le_one infDist_nonneg

private theorem whitneyScale_le_add_dist
    {E : Type*} [PseudoMetricSpace E] (s : Set E) (x y : E) :
    whitneyScale s x ≤ whitneyScale s y + dist x y := by
  change min 1 (infDist x s) ≤ min 1 (infDist y s) + dist x y
  by_cases hy : infDist y s ≤ 1
  · rw [min_eq_right hy]
    exact (min_le_right _ _).trans infDist_le_infDist_add_dist
  · rw [min_eq_left (le_of_not_ge hy)]
    exact (min_le_left _ _).trans
      (le_add_of_nonneg_right (dist_nonneg : 0 ≤ dist x y))

private structure WhitneyBallCover (E : Type u) [MetricSpace E] (s : Set E) where
  ι : Type u
  colorCount : ℕ
  center : ι → E
  radius : ι → ℝ
  color : ι → Fin colorCount
  center_mem : ∀ i, center i ∈ sᶜ
  radius_eq : ∀ i, radius i = whitneyRadius s (center i)
  radius_pos : ∀ i, 0 < radius i
  cover : sᶜ ⊆ ⋃ i, ball (center i) (radius i)
  disjoint : ∀ i j, color i = color j → i ≠ j →
    Disjoint (closedBall (center i) (radius i)) (closedBall (center j) (radius j))

private theorem exists_whitneyBallCover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsClosed s) (hne : s.Nonempty) :
    Nonempty (WhitneyBallCover E s) := by
  let β := {x : E // x ∈ sᶜ}
  let q : Besicovitch.BallPackage β E :=
    { c := fun x => x
      r := fun x => whitneyRadius s x
      rpos := fun x => by
        apply div_pos
        · exact lt_min zero_lt_one ((hs.notMem_iff_infDist_pos hne).mp x.property)
        · norm_num
      r_bound := 1 / 32
      r_le := fun x => by
        dsimp [whitneyRadius]
        gcongr
        exact min_le_left _ _ }
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := E)
  obtain ⟨a, ha_disjoint, ha_cover⟩ :=
    Besicovitch.exist_disjoint_covering_families hτ hN q
  let ι := Σ j : Fin N, a j
  refine ⟨{
    ι := ι
    colorCount := N
    center := fun i => q.c i.2
    radius := fun i => q.r i.2
    color := fun i => i.1
    center_mem := fun i => i.2.1.property
    radius_eq := fun _ => rfl
    radius_pos := fun i => q.rpos i.2
    cover := ?_
    disjoint := ?_ }⟩
  · intro x hx
    have hxrange : x ∈ range q.c := ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨j, b, hb, hxb⟩ := by
      simpa only [mem_iUnion, exists_prop] using ha_cover hxrange
    exact mem_iUnion.2 ⟨⟨j, b, hb⟩, hxb⟩
  · intro i j hij hneij
    rcases i with ⟨ci, i, hi⟩
    rcases j with ⟨cj, j, hj⟩
    dsimp only at hij ⊢
    subst cj
    apply ha_disjoint ci hi hj
    intro heq
    subst j
    exact hneij rfl

private theorem WhitneyBallCover.radius_eq_scale_div
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) :
    C.radius i = whitneyScale s (C.center i) / 32 := by
  exact C.radius_eq i

private theorem WhitneyBallCover.scale_center_pos
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) :
    0 < whitneyScale s (C.center i) := by
  have hrpos := C.radius_pos i
  rw [C.radius_eq_scale_div i] at hrpos
  linarith

private theorem WhitneyBallCover.scale_comparable_of_mem_outer
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) {i : C.ι} {x : E}
    (hx : dist x (C.center i) ≤ 3 * C.radius i) :
    32 * whitneyScale s x ≤ 35 * whitneyScale s (C.center i) ∧
      29 * whitneyScale s (C.center i) ≤ 32 * whitneyScale s x := by
  have hxc := whitneyScale_le_add_dist s x (C.center i)
  have hcx := whitneyScale_le_add_dist s (C.center i) x
  have hr := C.radius_eq_scale_div i
  rw [dist_comm] at hcx
  rw [hr] at hx
  constructor <;> linarith

private theorem finite_of_norm_le_two_of_one_le_norm_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {t : Set E} (ht : ∀ x ∈ t, ‖x‖ ≤ 2)
    (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 1 ≤ ‖x - y‖) : t.Finite := by
  obtain ⟨u, -, hufin, hucover⟩ :=
    (isCompact_closedBall (0 : E) 2).finite_cover_balls
      (by norm_num : 0 < (1 / 3 : ℝ))
  have hmem : ∀ x : t, ∃ y ∈ u, dist (x : E) (y : E) < 1 / 3 := by
    intro x
    have hxball : (x : E) ∈ closedBall 0 2 := by
      simpa only [mem_closedBall, dist_zero_right] using ht x x.property
    simpa only [mem_iUnion, exists_prop, mem_ball] using hucover hxball
  choose a ha hadist using hmem
  let A : t → u := fun x => ⟨a x, ha x⟩
  have hAinj : Function.Injective A := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hlarge := hsep x x.property y y.property hne
    have hsmall : dist (x : E) y < 2 / 3 := by
      calc
        dist (x : E) y ≤ dist (x : E) (a x) + dist (a x) y := dist_triangle _ _ _
        _ = dist (x : E) (a x) + dist (a y) y := by rw [show a x = a y from congrArg Subtype.val hxy]
        _ < 1 / 3 + 1 / 3 := add_lt_add (hadist x) (by simpa [dist_comm] using hadist y)
        _ = 2 / 3 := by ring
    rw [← dist_eq_norm] at hlarge
    linarith
  rw [← finite_coe_iff]
  exact @Finite.of_injective t u (finite_coe_iff.mpr hufin) A hAinj

private def WhitneyBallCover.outerActive
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) : Set C.ι :=
  {i | dist x (C.center i) ≤ 3 * C.radius i}

private def WhitneyBallCover.outerActiveColor
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) (a : Fin C.colorCount) : Set C.ι :=
  C.outerActive x ∩ {i | C.color i = a}

private def WhitneyBallCover.normalizedCenter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) (i : C.ι) : E :=
  (35 / (2 * whitneyScale s x)) • (C.center i - x)

private theorem WhitneyBallCover.scale_pos_of_mem_outerActive
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) {x : E} {i : C.ι}
    (hi : i ∈ C.outerActive x) : 0 < whitneyScale s x := by
  have hc := C.scale_center_pos i
  have hcomp := C.scale_comparable_of_mem_outer hi
  linarith

private theorem WhitneyBallCover.norm_normalizedCenter_le_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) {x : E} {i : C.ι}
    (hi : i ∈ C.outerActive x) : ‖C.normalizedCenter x i‖ ≤ 2 := by
  have hxpos := C.scale_pos_of_mem_outerActive hi
  have hcomp := C.scale_comparable_of_mem_outer hi
  have hdist : dist x (C.center i) ≤ 3 * whitneyScale s x / 29 := by
    change dist x (C.center i) ≤ 3 * C.radius i at hi
    rw [C.radius_eq_scale_div] at hi
    linarith
  rw [WhitneyBallCover.normalizedCenter, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) (mul_pos (by norm_num) hxpos)),
    ← dist_eq_norm, dist_comm]
  calc
    35 / (2 * whitneyScale s x) * dist x (C.center i) ≤
        35 / (2 * whitneyScale s x) * (3 * whitneyScale s x / 29) := by
      gcongr
    _ = 105 / 58 := by field_simp; norm_num
    _ ≤ 2 := by norm_num

private theorem WhitneyBallCover.one_le_norm_normalizedCenter_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) {x : E} {i j : C.ι}
    (hi : i ∈ C.outerActive x) (hj : j ∈ C.outerActive x)
    (hcolor : C.color i = C.color j) (hij : i ≠ j) :
    1 ≤ ‖C.normalizedCenter x i - C.normalizedCenter x j‖ := by
  have hxpos := C.scale_pos_of_mem_outerActive hi
  have hci := (C.scale_comparable_of_mem_outer hi).1
  have hcj := (C.scale_comparable_of_mem_outer hj).1
  have hdisj := C.disjoint i j hcolor hij
  have hripos := (C.radius_pos i).le
  have hrjpos := (C.radius_pos j).le
  have hdist := (disjoint_closedBall_closedBall_iff hripos hrjpos).mp hdisj
  rw [C.radius_eq_scale_div, C.radius_eq_scale_div] at hdist
  have hdist' : 2 * whitneyScale s x / 35 < dist (C.center i) (C.center j) := by
    linarith
  have hnorm :
      ‖C.normalizedCenter x i - C.normalizedCenter x j‖ =
        35 / (2 * whitneyScale s x) * dist (C.center i) (C.center j) := by
    rw [WhitneyBallCover.normalizedCenter, WhitneyBallCover.normalizedCenter]
    have heq :
        (35 / (2 * whitneyScale s x)) • (C.center i - x) -
            (35 / (2 * whitneyScale s x)) • (C.center j - x) =
          (35 / (2 * whitneyScale s x)) • (C.center i - C.center j) := by module
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) (mul_pos (by norm_num) hxpos)), ← dist_eq_norm]
  rw [hnorm]
  calc
    1 = 35 / (2 * whitneyScale s x) * (2 * whitneyScale s x / 35) := by field_simp
    _ ≤ 35 / (2 * whitneyScale s x) * dist (C.center i) (C.center j) := by gcongr

private theorem WhitneyBallCover.outerActiveColor_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) (a : Fin C.colorCount) :
    (C.outerActiveColor x a).Finite := by
  by_cases hA : C.outerActiveColor x a = ∅
  · exact hA ▸ finite_empty
  have hAnonempty : (C.outerActiveColor x a).Nonempty := nonempty_iff_ne_empty.mpr hA
  obtain ⟨i, hi⟩ := hAnonempty
  have hiouter : i ∈ C.outerActive x := hi.1
  let z : C.ι → E := C.normalizedCenter x
  have hzfinite : (z '' C.outerActiveColor x a).Finite :=
    finite_of_norm_le_two_of_one_le_norm_sub
      (fun y hy => by
        obtain ⟨j, hj, rfl⟩ := hy
        exact C.norm_normalizedCenter_le_two hj.1)
      (fun y hy z' hz' hyz => by
        obtain ⟨j, hj, rfl⟩ := hy
        obtain ⟨k, hk, rfl⟩ := hz'
        have hjk : j ≠ k := by
          intro hjk
          subst k
          exact hyz rfl
        exact C.one_le_norm_normalizedCenter_sub hj.1 hk.1 (hj.2.trans hk.2.symm) hjk)
  apply hzfinite.of_finite_image
  intro j hj k hk hjk
  by_contra hjkne
  have hsep := C.one_le_norm_normalizedCenter_sub hj.1 hk.1
    (hj.2.trans hk.2.symm) hjkne
  rw [show z j - z k = 0 by rw [hjk, sub_self], norm_zero] at hsep
  norm_num at hsep

private theorem WhitneyBallCover.outerActiveColor_ncard_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) (a : Fin C.colorCount) :
    (C.outerActiveColor x a).ncard ≤ 5 ^ Module.finrank ℝ E := by
  let A := C.outerActiveColor x a
  let z : C.ι → E := C.normalizedCenter x
  have hAfinite : A.Finite := C.outerActiveColor_finite x a
  have hzinj : Set.InjOn z A := by
    intro i hi j hj hij
    by_contra hne
    have hsep := C.one_le_norm_normalizedCenter_sub hi.1 hj.1
      (hi.2.trans hj.2.symm) hne
    rw [show z i - z j = 0 by rw [hij, sub_self], norm_zero] at hsep
    norm_num at hsep
  rw [← hzinj.ncard_image, Set.ncard_eq_toFinset_card _ (hAfinite.image z)]
  apply Besicovitch.card_le_of_separated
  · intro y hy
    have hy' : y ∈ z '' A := by simpa using hy
    obtain ⟨i, hi, rfl⟩ := hy'
    exact C.norm_normalizedCenter_le_two hi.1
  · intro y hy z' hz' hyz
    have hy' : y ∈ z '' A := by simpa using hy
    have hz'' : z' ∈ z '' A := by simpa using hz'
    obtain ⟨i, hi, rfl⟩ := hy'
    obtain ⟨j, hj, rfl⟩ := hz''
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hyz rfl
    exact C.one_le_norm_normalizedCenter_sub hi.1 hj.1
      (hi.2.trans hj.2.symm) hij

private theorem WhitneyBallCover.outerActive_eq_iUnion
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) :
    C.outerActive x = ⋃ a : Fin C.colorCount, C.outerActiveColor x a := by
  ext i
  simp only [WhitneyBallCover.outerActiveColor, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  constructor
  · exact fun hi => ⟨C.color i, hi, rfl⟩
  · rintro ⟨_, hi, _⟩
    exact hi

private theorem WhitneyBallCover.outerActive_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) : (C.outerActive x).Finite := by
  rw [C.outerActive_eq_iUnion x]
  exact Set.Finite.iUnion finite_univ
    (fun a _ => C.outerActiveColor_finite x a) (by simp)

private theorem WhitneyBallCover.outerActive_ncard_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) :
    (C.outerActive x).ncard ≤ C.colorCount * 5 ^ Module.finrank ℝ E := by
  rw [C.outerActive_eq_iUnion x]
  calc
    (⋃ a : Fin C.colorCount, C.outerActiveColor x a).ncard ≤
        ∑ a : Fin C.colorCount, (C.outerActiveColor x a).ncard :=
      ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _a : Fin C.colorCount, 5 ^ Module.finrank ℝ E := by
      gcongr with a
      exact C.outerActiveColor_ncard_le x a
    _ = C.colorCount * 5 ^ Module.finrank ℝ E := by simp

private def WhitneyBallCover.bump
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) : ContDiffBump (C.center i) where
  rIn := C.radius i
  rOut := 2 * C.radius i
  rIn_pos := C.radius_pos i
  rIn_lt_rOut := by linarith [C.radius_pos i]

private theorem WhitneyBallCover.support_bump
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) :
    Function.support (C.bump i : E → ℝ) = ball (C.center i) (2 * C.radius i) := by
  exact (C.bump i).support_eq

private theorem WhitneyBallCover.exists_nhds_support_subset_outerActive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    {x : E} (hx : x ∈ sᶜ) :
    ∃ t ∈ 𝓝 x, ∀ i, ((Function.support (C.bump i : E → ℝ) ∩ t).Nonempty →
      i ∈ C.outerActive x) := by
  have hxscale : 0 < whitneyScale s x := by
    have hxinf : 0 < infDist x s := (hs.notMem_iff_infDist_pos hne).mp hx
    exact lt_min zero_lt_one hxinf
  refine ⟨ball x (whitneyScale s x / 100), ball_mem_nhds x (by positivity), ?_⟩
  intro i hi
  obtain ⟨y, hybump, hyball⟩ := hi
  rw [C.support_bump i] at hybump
  have hxy : dist x y < whitneyScale s x / 100 := by
    simpa only [mem_ball, dist_comm] using hyball
  have hyc : dist y (C.center i) < 2 * C.radius i := by
    simpa only [mem_ball] using hybump
  have hscale_xy := whitneyScale_le_add_dist s x y
  have hscale_yc := whitneyScale_le_add_dist s y (C.center i)
  have hr := C.radius_eq_scale_div i
  have hrle : whitneyScale s x / 100 ≤ C.radius i := by
    rw [hr]
    rw [hr] at hyc
    linarith
  change dist x (C.center i) ≤ 3 * C.radius i
  calc
    dist x (C.center i) ≤ dist x y + dist y (C.center i) := dist_triangle _ _ _
    _ ≤ C.radius i + 2 * C.radius i := by
      exact add_le_add (hxy.le.trans hrle) hyc.le
    _ = 3 * C.radius i := by ring

private theorem WhitneyBallCover.eventuallyEq_finsum_bump_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (g : C.ι → E → F) {x : E} (hx : x ∈ sᶜ) :
    (fun y => ∑ᶠ i, C.bump i y • g i y) =ᶠ[𝓝 x]
      fun y => ∑ i ∈ (C.outerActive_finite x).toFinset, C.bump i y • g i y := by
  obtain ⟨t, ht, hsub⟩ := C.exists_nhds_support_subset_outerActive hs hne hx
  filter_upwards [ht] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  have hbump : C.bump i y ≠ 0 := by
    intro hbump
    apply hi
    simp [hbump]
  apply (C.outerActive_finite x).mem_toFinset.mpr
  exact hsub i ⟨y, hbump, hy⟩

private theorem WhitneyBallCover.contDiffAt_finsum_bump_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (g : C.ι → E → F) (hg : ∀ i, ContDiff ℝ 1 (g i)) {x : E} (hx : x ∈ sᶜ) :
    ContDiffAt ℝ 1 (fun y => ∑ᶠ i, C.bump i y • g i y) x := by
  apply (ContDiffAt.sum fun i _ =>
    ((C.bump i).contDiff.smul (hg i)).contDiffAt).congr_of_eventuallyEq
      (C.eventuallyEq_finsum_bump_smul hs hne g hx)

private def whitneyBaseBump
    (E : Type*) [NormedAddCommGroup E] : ContDiffBump (0 : E) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

private def whitneyBumpLipschitzConstant
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ℝ≥0 :=
  Classical.choose ((whitneyBaseBump E).contDiff.lipschitzWith_of_hasCompactSupport
    (whitneyBaseBump E).hasCompactSupport (by exact one_ne_zero)) + 1

private theorem whitneyBumpLipschitzConstant_pos
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
  0 < whitneyBumpLipschitzConstant E := by
  have hK : 0 ≤ Classical.choose
      ((whitneyBaseBump E).contDiff.lipschitzWith_of_hasCompactSupport
        (whitneyBaseBump E).hasCompactSupport (by exact one_ne_zero)) := zero_le
  simp [whitneyBumpLipschitzConstant, add_pos_of_nonneg_of_pos hK zero_lt_one]

private theorem whitneyBaseBump_lipschitz
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    LipschitzWith (whitneyBumpLipschitzConstant E) (whitneyBaseBump E : E → ℝ) := by
  let K := Classical.choose ((whitneyBaseBump E).contDiff.lipschitzWith_of_hasCompactSupport
    (whitneyBaseBump E).hasCompactSupport (by exact one_ne_zero))
  have hK := Classical.choose_spec
    ((whitneyBaseBump E).contDiff.lipschitzWith_of_hasCompactSupport
      (whitneyBaseBump E).hasCompactSupport (by exact one_ne_zero))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hK.dist_le_mul x y).trans (by
    gcongr
    simp [whitneyBumpLipschitzConstant])

private theorem WhitneyBallCover.bump_eq_base_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) :
    (C.bump i : E → ℝ) =
      (whitneyBaseBump E : E → ℝ) ∘ fun x => (C.radius i)⁻¹ • (x - C.center i) := by
  ext x
  rw [(C.bump i).apply]
  change _ = (whitneyBaseBump E) ((C.radius i)⁻¹ • (x - C.center i))
  rw [(whitneyBaseBump E).apply]
  dsimp only [WhitneyBallCover.bump, whitneyBaseBump]
  rw [show 2 * C.radius i / C.radius i = 2 by
    field_simp [C.radius_pos i |>.ne']]
  simp

private theorem WhitneyBallCover.bump_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) :
    LipschitzWith (whitneyBumpLipschitzConstant E / ⟨C.radius i, (C.radius_pos i).le⟩)
      (C.bump i : E → ℝ) := by
  rw [C.bump_eq_base_comp i]
  let r : ℝ≥0 := ⟨C.radius i, (C.radius_pos i).le⟩
  have hinner : LipschitzWith r⁻¹
      (fun x => (C.radius i)⁻¹ • (x - C.center i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((C.radius i)⁻¹ • (x - C.center i))
      ((C.radius i)⁻¹ • (y - C.center i)) ≤ (r : ℝ)⁻¹ * dist x y
    rw [dist_eq_norm]
    rw [← smul_sub]
    have heq : (x - C.center i) - (y - C.center i) = x - y := by module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (C.radius_pos i)]
    rw [dist_eq_norm]
    rfl
  convert (whitneyBaseBump_lipschitz E).comp hinner using 1
  · dsimp only [r]
    apply NNReal.eq
    change (whitneyBumpLipschitzConstant E : ℝ) / C.radius i =
      (whitneyBumpLipschitzConstant E : ℝ) * (C.radius i)⁻¹
    exact div_eq_mul_inv _ _

private theorem WhitneyBallCover.norm_fderiv_bump_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (i : C.ι) (x : E) :
    ‖fderiv ℝ (C.bump i : E → ℝ) x‖ ≤ whitneyBumpLipschitzConstant E / C.radius i := by
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (C.bump_lipschitz i)
  change ‖fderiv ℝ (C.bump i : E → ℝ) x‖ ≤
    (whitneyBumpLipschitzConstant E : ℝ) / C.radius i at h
  exact h

private theorem WhitneyBallCover.exists_mem_closedSet_nearest
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty) (i : C.ι) :
    ∃ a ∈ s, infDist (C.center i) s = dist (C.center i) a := by
  obtain ⟨a, ha, hdist⟩ := hs.exists_infDist_eq_dist hne (C.center i)
  exact ⟨a, ha, hdist⟩

private noncomputable def WhitneyBallCover.nearest
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty) (i : C.ι) : E :=
  Classical.choose (C.exists_mem_closedSet_nearest hs hne i)

private theorem WhitneyBallCover.nearest_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty) (i : C.ι) :
    C.nearest hs hne i ∈ s :=
  (Classical.choose_spec (C.exists_mem_closedSet_nearest hs hne i)).1

private theorem WhitneyBallCover.infDist_eq_dist_center_nearest
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty) (i : C.ι) :
    infDist (C.center i) s = dist (C.center i) (C.nearest hs hne i) :=
  (Classical.choose_spec (C.exists_mem_closedSet_nearest hs hne i)).2

private theorem whitneyScale_le_dist_of_mem
    {E : Type*} [PseudoMetricSpace E] {s : Set E} {x y : E} (hx : x ∈ s) :
    whitneyScale s y ≤ dist y x := by
  exact (min_le_right _ _).trans (infDist_le_dist_of_mem hx)

private theorem WhitneyBallCover.scale_le_mul_radius_of_mem_outer
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) {i : C.ι} {x : E}
    (hi : i ∈ C.outerActive x) : whitneyScale s x ≤ 35 * C.radius i := by
  have h := (C.scale_comparable_of_mem_outer hi).1
  rw [C.radius_eq_scale_div]
  linarith

private theorem WhitneyBallCover.radius_le_scale_div_of_mem_outer
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s) {i : C.ι} {x : E}
    (hi : i ∈ C.outerActive x) : C.radius i ≤ whitneyScale s x / 29 := by
  have h := (C.scale_comparable_of_mem_outer hi).2
  rw [C.radius_eq_scale_div]
  linarith

private theorem WhitneyBallCover.infDist_center_eq_scale_of_mem_outer_of_dist_lt
    {E : Type*} [NormedAddCommGroup E]
    {s : Set E} (C : WhitneyBallCover E s)
    {i : C.ι} {x y : E} (hx : x ∈ s) (hi : i ∈ C.outerActive y)
    (hy : dist y x < 29 / 32) :
    infDist (C.center i) s = whitneyScale s (C.center i) := by
  have hscale_y : whitneyScale s y ≤ dist y x := whitneyScale_le_dist_of_mem hx
  have hcomp := (C.scale_comparable_of_mem_outer hi).2
  have hscale_center : whitneyScale s (C.center i) < 1 := by
    linarith
  have hinf : infDist (C.center i) s < 1 := by
    simpa only [whitneyScale, min_lt_iff, lt_self_iff_false, false_or] using hscale_center
  exact (min_eq_right hinf.le).symm

private theorem WhitneyBallCover.dist_nearest_le_scale_of_mem_outer_of_dist_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    {i : C.ι} {x y : E} (hx : x ∈ s) (hi : i ∈ C.outerActive y)
    (hy : dist y x < 29 / 32) :
    dist y (C.nearest hs hne i) ≤ 35 / 29 * whitneyScale s y := by
  have hcenter : dist y (C.center i) ≤ 3 * C.radius i := hi
  have hnearest : dist (C.center i) (C.nearest hs hne i) =
      whitneyScale s (C.center i) := by
    rw [← C.infDist_eq_dist_center_nearest hs hne]
    exact C.infDist_center_eq_scale_of_mem_outer_of_dist_lt hx hi hy
  have hcomp := (C.scale_comparable_of_mem_outer hi).2
  have hr := C.radius_eq_scale_div i
  calc
    dist y (C.nearest hs hne i) ≤
        dist y (C.center i) + dist (C.center i) (C.nearest hs hne i) :=
      dist_triangle _ _ _
    _ ≤ 3 * C.radius i + whitneyScale s (C.center i) :=
      add_le_add hcenter hnearest.le
    _ ≤ 35 / 29 * whitneyScale s y := by rw [hr]; linarith

private theorem WhitneyBallCover.dist_nearest_base_le_of_mem_outer_of_dist_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    {i : C.ι} {x y : E} (hx : x ∈ s) (hi : i ∈ C.outerActive y)
    (hy : dist y x < 29 / 32) :
    dist (C.nearest hs hne i) x ≤ 64 / 29 * dist y x := by
  have hscale : whitneyScale s y ≤ dist y x := whitneyScale_le_dist_of_mem hx
  have hnear := C.dist_nearest_le_scale_of_mem_outer_of_dist_lt hs hne hx hi hy
  calc
    dist (C.nearest hs hne i) x ≤ dist (C.nearest hs hne i) y + dist y x :=
      dist_triangle _ _ _
    _ ≤ 35 / 29 * whitneyScale s y + dist y x := by
      gcongr
      simpa only [dist_comm] using hnear
    _ ≤ 64 / 29 * dist y x := by linarith

private theorem WhitneyBallCover.dist_nearest_nearest_le_of_mem_outer_of_dist_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    {i j : C.ι} {x y : E} (hx : x ∈ s)
    (hi : i ∈ C.outerActive y) (hj : j ∈ C.outerActive y)
    (hy : dist y x < 29 / 32) :
    dist (C.nearest hs hne i) (C.nearest hs hne j) ≤
      70 / 29 * whitneyScale s y := by
  have hi' := C.dist_nearest_le_scale_of_mem_outer_of_dist_lt hs hne hx hi hy
  have hj' := C.dist_nearest_le_scale_of_mem_outer_of_dist_lt hs hne hx hj hy
  calc
    dist (C.nearest hs hne i) (C.nearest hs hne j) ≤
        dist (C.nearest hs hne i) y + dist y (C.nearest hs hne j) :=
      dist_triangle _ _ _
    _ ≤ 35 / 29 * whitneyScale s y + 35 / 29 * whitneyScale s y := by
      gcongr
      simpa only [dist_comm] using hi'
    _ = 70 / 29 * whitneyScale s y := by ring

private def WhitneyBallCover.affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (i : C.ι) (x : E) : F :=
  f (C.nearest hs hne i) + f' (C.nearest hs hne i) (x - C.nearest hs hne i)

private theorem WhitneyBallCover.contDiff_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (i : C.ι) :
    ContDiff ℝ ⊤ (C.affine hs hne f f' i) := by
  exact contDiff_const.add
    ((f' (C.nearest hs hne i)).contDiff.comp (contDiff_id.sub contDiff_const))

private theorem WhitneyBallCover.hasFDerivAt_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (i : C.ι) (x : E) :
    HasFDerivAt (C.affine hs hne f f' i) (f' (C.nearest hs hne i)) x := by
  convert (hasFDerivAt_const (f (C.nearest hs hne i)) x).add
      ((f' (C.nearest hs hne i)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const (C.nearest hs hne i) x))) using 1
  · ext z
    simp [WhitneyBallCover.affine]
  · ext z
    simp

private def WhitneyBallCover.denominator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) : ℝ :=
  ∑ᶠ i, C.bump i x

private def WhitneyBallCover.numerator
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (x : E) : F :=
  ∑ᶠ i, C.bump i x • C.affine hs hne f f' i x

private theorem WhitneyBallCover.hasFDerivAt_denominator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    {x : E} (hx : x ∈ sᶜ) :
    HasFDerivAt C.denominator
      (∑ i ∈ (C.outerActive_finite x).toFinset, fderiv ℝ (C.bump i : E → ℝ) x) x := by
  change HasFDerivAt (fun y => ∑ᶠ i, C.bump i y)
    (∑ i ∈ (C.outerActive_finite x).toFinset, fderiv ℝ (C.bump i : E → ℝ) x) x
  have hterm (i : C.ι) : HasFDerivAt (C.bump i : E → ℝ)
      (fderiv ℝ (C.bump i : E → ℝ) x) x :=
    ((C.bump i).contDiff (n := 1)).differentiable_one x |>.hasFDerivAt
  apply (HasFDerivAt.fun_sum (u := (C.outerActive_finite x).toFinset)
    fun i _ => hterm i).congr_of_eventuallyEq
  simpa only [smul_eq_mul, mul_one] using
    C.eventuallyEq_finsum_bump_smul hs hne (fun _ _ => (1 : ℝ)) hx

private theorem WhitneyBallCover.hasFDerivAt_numerator
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x : E} (hx : x ∈ sᶜ) :
    HasFDerivAt (C.numerator hs hne f f')
      (Finset.sum ((C.outerActive_finite x).toFinset : Finset C.ι) fun i : C.ι =>
        C.bump i x • f' (C.nearest hs hne i) +
          (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
            (C.affine hs hne f f' i x)) x := by
  have hterm (i : C.ι) : HasFDerivAt
      (fun y => C.bump i y • C.affine hs hne f f' i y)
      (C.bump i x • f' (C.nearest hs hne i) +
        (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
          (C.affine hs hne f f' i x)) x :=
    (((C.bump i).contDiff (n := 1)).differentiable_one x |>.hasFDerivAt).smul
      (C.hasFDerivAt_affine hs hne f f' i x)
  apply (HasFDerivAt.fun_sum (u := (C.outerActive_finite x).toFinset)
    fun i _ => hterm i).congr_of_eventuallyEq
  exact C.eventuallyEq_finsum_bump_smul hs hne (C.affine hs hne f f') hx

private theorem WhitneyBallCover.denominator_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) {x : E} (hx : x ∈ sᶜ) :
    0 < C.denominator x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ ball (C.center i) (C.radius i) := by
    simpa only [mem_iUnion] using C.cover hx
  have hibump : C.bump i x = 1 := by
    apply (C.bump i).one_of_mem_closedBall
    exact mem_closedBall.mpr (mem_ball.mp hi).le
  let I := (C.outerActive_finite x).toFinset
  have hiI : i ∈ I := by
    apply (C.outerActive_finite x).mem_toFinset.mpr
    change dist x (C.center i) ≤ 3 * C.radius i
    exact (mem_ball.mp hi).le.trans (by linarith [C.radius_pos i])
  have hsupport : Function.support (fun j => C.bump j x) ⊆ I := by
    intro j hj
    apply (C.outerActive_finite x).mem_toFinset.mpr
    change dist x (C.center j) ≤ 3 * C.radius j
    change C.bump j x ≠ 0 at hj
    have hj' : x ∈ Function.support (C.bump j : E → ℝ) := hj
    rw [C.support_bump j] at hj'
    exact (mem_ball.mp hj').le.trans (by linarith [C.radius_pos j])
  rw [WhitneyBallCover.denominator, finsum_eq_sum_of_support_subset _ hsupport]
  calc
    0 < C.bump i x := by rw [hibump]; exact zero_lt_one
    _ ≤ ∑ j ∈ I, C.bump j x :=
      Finset.single_le_sum (fun j _ => (C.bump j).nonneg) hiI

private theorem WhitneyBallCover.one_le_denominator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) {x : E} (hx : x ∈ sᶜ) :
    1 ≤ C.denominator x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ ball (C.center i) (C.radius i) := by
    simpa only [mem_iUnion] using C.cover hx
  have hibump : C.bump i x = 1 := by
    apply (C.bump i).one_of_mem_closedBall
    exact mem_closedBall.mpr (mem_ball.mp hi).le
  let I := (C.outerActive_finite x).toFinset
  have hiI : i ∈ I := by
    apply (C.outerActive_finite x).mem_toFinset.mpr
    change dist x (C.center i) ≤ 3 * C.radius i
    exact (mem_ball.mp hi).le.trans (by linarith [C.radius_pos i])
  have hsupport : Function.support (fun j => C.bump j x) ⊆ I := by
    intro j hj
    apply (C.outerActive_finite x).mem_toFinset.mpr
    change dist x (C.center j) ≤ 3 * C.radius j
    have hj' : x ∈ Function.support (C.bump j : E → ℝ) := hj
    rw [C.support_bump j] at hj'
    exact (mem_ball.mp hj').le.trans (by linarith [C.radius_pos j])
  rw [WhitneyBallCover.denominator, finsum_eq_sum_of_support_subset _ hsupport, ← hibump]
  exact Finset.single_le_sum (fun j _ => (C.bump j).nonneg) hiI

private theorem WhitneyBallCover.denominator_eq_sum_outerActive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (x : E) :
    C.denominator x = ∑ i ∈ (C.outerActive_finite x).toFinset, C.bump i x := by
  change ∑ᶠ i, C.bump i x = _
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply (C.outerActive_finite x).mem_toFinset.mpr
  change dist x (C.center i) ≤ 3 * C.radius i
  have hi' : x ∈ Function.support (C.bump i : E → ℝ) := hi
  rw [C.support_bump i] at hi'
  exact (mem_ball.mp hi').le.trans (by linarith [C.radius_pos i])

private theorem WhitneyBallCover.numerator_eq_sum_outerActive
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (x : E) :
    C.numerator hs hne f f' x =
      ∑ i ∈ (C.outerActive_finite x).toFinset,
        C.bump i x • C.affine hs hne f f' i x := by
  change ∑ᶠ i, C.bump i x • C.affine hs hne f f' i x = _
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply (C.outerActive_finite x).mem_toFinset.mpr
  change dist x (C.center i) ≤ 3 * C.radius i
  have hibump : C.bump i x ≠ 0 := by
    intro hibump
    apply hi
    simp [hibump]
  have hi' : x ∈ Function.support (C.bump i : E → ℝ) := hibump
  rw [C.support_bump i] at hi'
  exact (mem_ball.mp hi').le.trans (by linarith [C.radius_pos i])

private theorem WhitneyBallCover.contDiffAt_denominator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    {x : E} (hx : x ∈ sᶜ) : ContDiffAt ℝ 1 C.denominator x := by
  change ContDiffAt ℝ 1 (fun y => ∑ᶠ i, C.bump i y) x
  simpa only [smul_eq_mul, mul_one] using
    C.contDiffAt_finsum_bump_smul hs hne (fun _ _ => (1 : ℝ))
      (fun _ => contDiff_const) hx

private theorem WhitneyBallCover.contDiffAt_numerator
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x : E} (hx : x ∈ sᶜ) :
    ContDiffAt ℝ 1 (C.numerator hs hne f f') x := by
  exact C.contDiffAt_finsum_bump_smul hs hne (C.affine hs hne f f')
    (fun i => (C.contDiff_affine hs hne f f' i).of_le (by norm_num)) hx

private def WhitneyBallCover.extension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (x : E) : F :=
  by
    classical
    exact if x ∈ s then f x else (C.denominator x)⁻¹ • C.numerator hs hne f f' x

private theorem WhitneyBallCover.extension_eq_weighted_sum
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x : E} (hx : x ∈ sᶜ) :
    C.extension hs hne f f' x = (C.denominator x)⁻¹ •
      ∑ i ∈ (C.outerActive_finite x).toFinset,
        C.bump i x • C.affine hs hne f f' i x := by
  rw [WhitneyBallCover.extension, if_neg hx, C.numerator_eq_sum_outerActive]

private theorem WhitneyBallCover.extension_eq_on
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) : EqOn (C.extension hs hne f f') f s := by
  intro x hx
  simp [WhitneyBallCover.extension, hx]

private theorem WhitneyBallCover.contDiffAt_extension_of_notMem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x : E} (hx : x ∈ sᶜ) :
    ContDiffAt ℝ 1 (C.extension hs hne f f') x := by
  have hloc : C.extension hs hne f f' =ᶠ[𝓝 x]
      fun y => (C.denominator y)⁻¹ • C.numerator hs hne f f' y := by
    filter_upwards [hs.isOpen_compl.mem_nhds hx] with y hy
    simp only [WhitneyBallCover.extension, if_neg hy]
  apply ((C.contDiffAt_denominator hs hne hx).inv (C.denominator_pos hx).ne'
    |>.smul (C.contDiffAt_numerator hs hne f f' hx)).congr_of_eventuallyEq hloc

private theorem WhitneyBallCover.fderiv_extension_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x : E} (hx : x ∈ sᶜ) :
    fderiv ℝ (C.extension hs hne f f') x =
      (C.denominator x)⁻¹ •
        ((Finset.sum ((C.outerActive_finite x).toFinset : Finset C.ι) fun i : C.ι =>
          C.bump i x • f' (C.nearest hs hne i) +
            (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
              (C.affine hs hne f f' i x)) -
          (∑ i ∈ (C.outerActive_finite x).toFinset,
            fderiv ℝ (C.bump i : E → ℝ) x).smulRight
              (C.extension hs hne f f' x)) := by
  let dD : E →L[ℝ] ℝ := ∑ i ∈ (C.outerActive_finite x).toFinset,
    fderiv ℝ (C.bump i : E → ℝ) x
  let dN : E →L[ℝ] F :=
    Finset.sum ((C.outerActive_finite x).toFinset : Finset C.ι) fun i : C.ι =>
      C.bump i x • f' (C.nearest hs hne i) +
        (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
          (C.affine hs hne f f' i x)
  have hD : HasFDerivAt C.denominator dD x :=
    C.hasFDerivAt_denominator hs hne hx
  have hN : HasFDerivAt (C.numerator hs hne f f') dN x :=
    C.hasFDerivAt_numerator hs hne f f' hx
  have hG : HasFDerivAt (C.extension hs hne f f')
      (fderiv ℝ (C.extension hs hne f f') x) x :=
    (C.contDiffAt_extension_of_notMem hs hne f f' hx).differentiableAt_one.hasFDerivAt
  have heq : C.numerator hs hne f f' =ᶠ[𝓝 x]
      fun y => C.denominator y • C.extension hs hne f f' y := by
    filter_upwards [hs.isOpen_compl.mem_nhds hx] with y hy
    rw [WhitneyBallCover.extension, if_neg hy]
    rw [smul_smul, mul_inv_cancel₀ (C.denominator_pos hy).ne', one_smul]
  have hprod : HasFDerivAt (C.numerator hs hne f f')
      (C.denominator x • fderiv ℝ (C.extension hs hne f f') x +
        dD.smulRight (C.extension hs hne f f' x)) x :=
    (hD.smul hG).congr_of_eventuallyEq heq
  have hderiv := hN.unique hprod
  change fderiv ℝ (C.extension hs hne f f') x =
    (C.denominator x)⁻¹ • (dN - dD.smulRight (C.extension hs hne f f' x))
  rw [hderiv]
  ext v
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [add_sub_cancel_right, ← mul_smul,
    inv_mul_cancel₀ (C.denominator_pos hx).ne', one_smul]

private theorem continuousLinearMap_sum_apply
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : Finset ι) (f : ι → E →L[ℝ] F) (v : E) :
    (∑ i ∈ I, f i) v = ∑ i ∈ I, f i v := by
  change ((∑ i ∈ I, f i).toLinearMap) v = _
  rw [ContinuousLinearMap.toLinearMap_sum]
  exact (congrFun (LinearMap.coe_sum I fun i => (f i).toLinearMap) v).trans
    (Finset.sum_apply v I fun i => (f i : E → F))

private theorem WhitneyBallCover.fderiv_extension_sub_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x : E} (hx : x ∈ sᶜ)
    (L : E →L[ℝ] F) :
    fderiv ℝ (C.extension hs hne f f') x - L =
      (C.denominator x)⁻¹ •
        Finset.sum ((C.outerActive_finite x).toFinset : Finset C.ι) (fun i : C.ι =>
          C.bump i x • (f' (C.nearest hs hne i) - L) +
            (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
              (C.affine hs hne f f' i x - C.extension hs hne f f' x)) := by
  let I : Finset C.ι := (C.outerActive_finite x).toFinset
  let dD : E →L[ℝ] ℝ := ∑ i ∈ I, fderiv ℝ (C.bump i : E → ℝ) x
  let A : E →L[ℝ] F := ∑ i ∈ I, C.bump i x • f' (C.nearest hs hne i)
  let B : E →L[ℝ] F := ∑ i ∈ I,
    (fderiv ℝ (C.bump i : E → ℝ) x).smulRight (C.affine hs hne f f' i x)
  let A' : E →L[ℝ] F := ∑ i ∈ I, C.bump i x • (f' (C.nearest hs hne i) - L)
  let B' : E →L[ℝ] F := ∑ i ∈ I,
    (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
      (C.affine hs hne f f' i x - C.extension hs hne f f' x)
  have hraw : fderiv ℝ (C.extension hs hne f f') x =
      (C.denominator x)⁻¹ •
        (A + B - dD.smulRight (C.extension hs hne f f' x)) := by
    rw [C.fderiv_extension_eq hs hne f f' hx]
    rw [Finset.sum_add_distrib]
  have hdenom : C.denominator x = ∑ i ∈ I, C.bump i x :=
    C.denominator_eq_sum_outerActive x
  have hA : A - C.denominator x • L = A' := by
    ext v
    rw [sub_apply, smul_apply]
    dsimp only [A, A']
    rw [continuousLinearMap_sum_apply, continuousLinearMap_sum_apply]
    rw [hdenom, Finset.sum_smul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_apply, sub_apply, smul_sub]
  have hB : B - dD.smulRight (C.extension hs hne f f' x) = B' := by
    ext v
    rw [sub_apply, ContinuousLinearMap.smulRight_apply]
    dsimp only [B, B', dD]
    rw [continuousLinearMap_sum_apply, continuousLinearMap_sum_apply,
      continuousLinearMap_sum_apply]
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ContinuousLinearMap.smulRight_apply, smul_sub]
  rw [hraw]
  calc
    (C.denominator x)⁻¹ •
          (A + B - dD.smulRight (C.extension hs hne f f' x)) - L =
        (C.denominator x)⁻¹ •
          (A + B - dD.smulRight (C.extension hs hne f f' x) -
            C.denominator x • L) := by
      simp only [smul_sub, smul_smul,
        inv_mul_cancel₀ (C.denominator_pos hx).ne', one_smul]
    _ = (C.denominator x)⁻¹ •
        ((A - C.denominator x • L) +
          (B - dD.smulRight (C.extension hs hne f f' x))) := by
      congr 1
      module
    _ = (C.denominator x)⁻¹ • (A' + B') := by rw [hA, hB]
    _ = (C.denominator x)⁻¹ •
        Finset.sum I (fun i : C.ι =>
          C.bump i x • (f' (C.nearest hs hne i) - L) +
            (fderiv ℝ (C.bump i : E → ℝ) x).smulRight
              (C.affine hs hne f f' i x - C.extension hs hne f f' x)) := by
      rw [Finset.sum_add_distrib]

private theorem IsWhitneyOneJetOn.exists_uniform_estimates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
    (h : IsWhitneyOneJetOn f f' s) {x : E} (hx : x ∈ s)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, dist a x < δ →
      ‖f' a - f' x‖ ≤ η ∧ ∀ b ∈ s, dist b x < δ →
        ‖f a - f b - f' x (a - b)‖ ≤ η * ‖a - b‖ := by
  have hcont : {a | ‖f' a - f' x‖ < η} ∈ 𝓝[s] x := by
    have h' := (h.1 x hx).preimage_mem_nhdsWithin (ball_mem_nhds (f' x) hη)
    exact Filter.mem_of_superset h' fun a ha => by
      simpa only [mem_ofPred_eq, mem_preimage, mem_ball, dist_eq_norm] using ha
  obtain ⟨δ₀, hδ₀, hcontδ⟩ := Metric.mem_nhdsWithin_iff.1 hcont
  have hstrict := h.2 x hx
  rw [HasStrictFDerivWithinAt, insert_eq_of_mem hx, nhdsWithin_prod_eq] at hstrict
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Filter.eventually_prod_iff.1 (hstrict.isLittleO.def hη)
  obtain ⟨δ₁, hδ₁, huδ⟩ := Metric.mem_nhdsWithin_iff.1 hu
  obtain ⟨δ₂, hδ₂, hvδ⟩ := Metric.mem_nhdsWithin_iff.1 hv
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), ?_⟩
  intro a ha hax
  have ha₀ : a ∈ ball x δ₀ ∩ s :=
    ⟨mem_ball.mpr (hax.trans_le (min_le_left _ _)), ha⟩
  have ha₁ : a ∈ ball x δ₁ ∩ s :=
    ⟨mem_ball.mpr (hax.trans_le (min_le_of_right_le (min_le_left _ _))), ha⟩
  refine ⟨(hcontδ ha₀).le, ?_⟩
  intro b hb hbx
  have hb₂ : b ∈ ball x δ₂ ∩ s :=
    ⟨mem_ball.mpr (hbx.trans_le (min_le_of_right_le (min_le_right _ _))), hb⟩
  exact huv (huδ ha₁) (hvδ hb₂)

private theorem WhitneyBallCover.norm_affine_sub_base_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x y : E} (hx : x ∈ s)
    {i : C.ι} (hi : i ∈ C.outerActive y) (hy : dist y x < 29 / 32)
    {η : ℝ} (hη : 0 ≤ η)
    (hL : ‖f' (C.nearest hs hne i) - f' x‖ ≤ η)
    (hR : ‖f (C.nearest hs hne i) - f x -
      f' x (C.nearest hs hne i - x)‖ ≤
        η * ‖C.nearest hs hne i - x‖) :
    ‖C.affine hs hne f f' i y - f x - f' x (y - x)‖ ≤
      4 * η * dist y x := by
  let a := C.nearest hs hne i
  have hdist_ax := C.dist_nearest_base_le_of_mem_outer_of_dist_lt hs hne hx hi hy
  have hdist_ya := C.dist_nearest_le_scale_of_mem_outer_of_dist_lt hs hne hx hi hy
  have hscale : whitneyScale s y ≤ dist y x := whitneyScale_le_dist_of_mem hx
  have hdist_nonneg : 0 ≤ dist y x := dist_nonneg
  have hid : C.affine hs hne f f' i y - f x - f' x (y - x) =
      (f a - f x - f' x (a - x)) + (f' a - f' x) (y - a) := by
    dsimp only [a, WhitneyBallCover.affine]
    simp only [sub_apply, map_sub]
    module
  rw [hid]
  calc
    ‖(f a - f x - f' x (a - x)) + (f' a - f' x) (y - a)‖ ≤
        ‖f a - f x - f' x (a - x)‖ + ‖(f' a - f' x) (y - a)‖ :=
      norm_add_le _ _
    _ ≤ η * ‖a - x‖ + η * ‖y - a‖ := by
      apply add_le_add hR
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hL le_rfl (norm_nonneg _) hη)
    _ ≤ η * (64 / 29 * dist y x) + η * (35 / 29 * whitneyScale s y) := by
      gcongr
      · simpa only [dist_eq_norm] using hdist_ax
      · simpa only [dist_eq_norm] using hdist_ya
    _ ≤ η * (64 / 29 * dist y x) + η * (35 / 29 * dist y x) := by gcongr
    _ ≤ 4 * η * dist y x := by nlinarith

private theorem WhitneyBallCover.norm_affine_sub_affine_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x y : E} (hx : x ∈ s)
    {i j : C.ι} (hi : i ∈ C.outerActive y) (hj : j ∈ C.outerActive y)
    (hy : dist y x < 29 / 32) {η : ℝ} (hη : 0 ≤ η)
    (hLi : ‖f' (C.nearest hs hne i) - f' x‖ ≤ η)
    (hLj : ‖f' (C.nearest hs hne j) - f' x‖ ≤ η)
    (hR : ‖f (C.nearest hs hne i) - f (C.nearest hs hne j) -
      f' x (C.nearest hs hne i - C.nearest hs hne j)‖ ≤
        η * ‖C.nearest hs hne i - C.nearest hs hne j‖) :
    ‖C.affine hs hne f f' i y - C.affine hs hne f f' j y‖ ≤
      8 * η * whitneyScale s y := by
  let a := C.nearest hs hne i
  let b := C.nearest hs hne j
  have hab := C.dist_nearest_nearest_le_of_mem_outer_of_dist_lt hs hne hx hi hj hy
  have hya := C.dist_nearest_le_scale_of_mem_outer_of_dist_lt hs hne hx hi hy
  have hLxj : ‖f' x - f' b‖ ≤ η := by
    simpa only [b, norm_sub_rev] using hLj
  have hLij : ‖f' a - f' b‖ ≤ 2 * η := by
    calc
      ‖f' a - f' b‖ = ‖(f' a - f' x) + (f' x - f' b)‖ := by congr 1; module
      _ ≤ ‖f' a - f' x‖ + ‖f' x - f' b‖ := norm_add_le _ _
      _ ≤ η + η := add_le_add hLi hLxj
      _ = 2 * η := by ring
  have hid : C.affine hs hne f f' i y - C.affine hs hne f f' j y =
      (f a - f b - f' x (a - b)) + (f' x - f' b) (a - b) +
        (f' a - f' b) (y - a) := by
    dsimp only [a, b, WhitneyBallCover.affine]
    simp only [sub_apply, map_sub]
    module
  rw [hid]
  calc
    ‖(f a - f b - f' x (a - b)) + (f' x - f' b) (a - b) +
        (f' a - f' b) (y - a)‖ ≤
        ‖f a - f b - f' x (a - b)‖ + ‖(f' x - f' b) (a - b)‖ +
          ‖(f' a - f' b) (y - a)‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ η * ‖a - b‖ + η * ‖a - b‖ + (2 * η) * ‖y - a‖ := by
      gcongr
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hLxj le_rfl (norm_nonneg _) hη)
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hLij le_rfl (norm_nonneg _) (by positivity))
    _ ≤ η * (70 / 29 * whitneyScale s y) +
        η * (70 / 29 * whitneyScale s y) +
          (2 * η) * (35 / 29 * whitneyScale s y) := by
      gcongr
      · simpa only [dist_eq_norm] using hab
      · simpa only [dist_eq_norm] using hab
      · simpa only [dist_eq_norm] using hya
    _ ≤ 8 * η * whitneyScale s y := by
      nlinarith [whitneyScale_nonneg s y]

private theorem WhitneyBallCover.norm_affine_sub_extension_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x y : E} (hx : x ∈ s)
    {i : C.ι} (hi : i ∈ C.outerActive y) (hyset : y ∈ sᶜ)
    (hy : dist y x < 29 / 32) {η : ℝ} (hη : 0 ≤ η)
    (hL : ∀ j ∈ C.outerActive y, ‖f' (C.nearest hs hne j) - f' x‖ ≤ η)
    (hR : ∀ j ∈ C.outerActive y,
      ‖f (C.nearest hs hne i) - f (C.nearest hs hne j) -
        f' x (C.nearest hs hne i - C.nearest hs hne j)‖ ≤
          η * ‖C.nearest hs hne i - C.nearest hs hne j‖) :
    ‖C.affine hs hne f f' i y - C.extension hs hne f f' y‖ ≤
      8 * η * whitneyScale s y := by
  let I : Finset C.ι := (C.outerActive_finite y).toFinset
  have hdenom : C.denominator y = ∑ j ∈ I, C.bump j y :=
    C.denominator_eq_sum_outerActive y
  have hrepr : C.affine hs hne f f' i y - C.extension hs hne f f' y =
      (C.denominator y)⁻¹ • ∑ j ∈ I, C.bump j y •
        (C.affine hs hne f f' i y - C.affine hs hne f f' j y) := by
    rw [C.extension_eq_weighted_sum hs hne f f' hyset]
    calc
      C.affine hs hne f f' i y -
          (C.denominator y)⁻¹ • ∑ j ∈ I, C.bump j y • C.affine hs hne f f' j y =
        (C.denominator y)⁻¹ •
          (C.denominator y • C.affine hs hne f f' i y -
            ∑ j ∈ I, C.bump j y • C.affine hs hne f f' j y) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ (C.denominator_pos hyset).ne', one_smul]
      _ = (C.denominator y)⁻¹ • ∑ j ∈ I, C.bump j y •
          (C.affine hs hne f f' i y - C.affine hs hne f f' j y) := by
        congr 1
        rw [hdenom, Finset.sum_smul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_sub]
  rw [hrepr, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (C.denominator_pos hyset)]
  calc
    (C.denominator y)⁻¹ *
        ‖∑ j ∈ I, C.bump j y •
          (C.affine hs hne f f' i y - C.affine hs hne f f' j y)‖ ≤
      (C.denominator y)⁻¹ * ∑ j ∈ I,
        C.bump j y * (8 * η * whitneyScale s y) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (C.denominator_pos hyset).le)
      apply norm_sum_le_of_le
      intro j hj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (C.bump j).nonneg]
      apply mul_le_mul_of_nonneg_left _ (C.bump j).nonneg
      apply C.norm_affine_sub_affine_le hs hne f f' hx hi
        ((C.outerActive_finite y).mem_toFinset.mp hj) hy hη
      · exact hL i hi
      · exact hL j ((C.outerActive_finite y).mem_toFinset.mp hj)
      · exact hR j ((C.outerActive_finite y).mem_toFinset.mp hj)
    _ = (C.denominator y)⁻¹ *
        (C.denominator y * (8 * η * whitneyScale s y)) := by
      rw [← Finset.sum_mul, hdenom]
    _ = 8 * η * whitneyScale s y := by
      rw [← mul_assoc, inv_mul_cancel₀ (C.denominator_pos hyset).ne', one_mul]

private theorem WhitneyBallCover.norm_fderiv_extension_sub_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x y : E} (hx : x ∈ s)
    (hyset : y ∈ sᶜ) (hy : dist y x < 29 / 32) {η : ℝ} (hη : 0 ≤ η)
    (hL : ∀ i ∈ C.outerActive y, ‖f' (C.nearest hs hne i) - f' x‖ ≤ η)
    (hR : ∀ i ∈ C.outerActive y, ∀ j ∈ C.outerActive y,
      ‖f (C.nearest hs hne i) - f (C.nearest hs hne j) -
        f' x (C.nearest hs hne i - C.nearest hs hne j)‖ ≤
          η * ‖C.nearest hs hne i - C.nearest hs hne j‖) :
    ‖fderiv ℝ (C.extension hs hne f f') y - f' x‖ ≤
      (1 + 280 * (C.colorCount * 5 ^ Module.finrank ℝ E : ℕ) *
        (whitneyBumpLipschitzConstant E : ℝ)) * η := by
  let I : Finset C.ι := (C.outerActive_finite y).toFinset
  let M : ℕ := C.colorCount * 5 ^ Module.finrank ℝ E
  let K : ℝ := whitneyBumpLipschitzConstant E
  have hDpos := C.denominator_pos hyset
  have hDone := C.one_le_denominator hyset
  have hDinv : 0 ≤ (C.denominator y)⁻¹ := inv_nonneg.mpr hDpos.le
  have hDinv_le : (C.denominator y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hDone
  have hcard : I.card ≤ M := by
    have h := C.outerActive_ncard_le y
    rw [Set.ncard_eq_toFinset_card (C.outerActive y) (C.outerActive_finite y)] at h
    simpa only [I, M] using h
  have hdenom : C.denominator y = ∑ i ∈ I, C.bump i y := by
    simpa only [I] using C.denominator_eq_sum_outerActive y
  have hterm : ∀ i ∈ I,
      ‖C.bump i y • (f' (C.nearest hs hne i) - f' x) +
        (fderiv ℝ (C.bump i : E → ℝ) y).smulRight
          (C.affine hs hne f f' i y - C.extension hs hne f f' y)‖ ≤
        C.bump i y * η + 280 * K * η := by
    intro i hi
    have hiactive : i ∈ C.outerActive y :=
      (C.outerActive_finite y).mem_toFinset.mp hi
    have hrpos := C.radius_pos i
    have hscale := C.scale_le_mul_radius_of_mem_outer hiactive
    have hbumpderiv := C.norm_fderiv_bump_le i y
    have haffine := C.norm_affine_sub_extension_le hs hne f f' hx hiactive
      hyset hy hη hL (hR i hiactive)
    calc
      ‖C.bump i y • (f' (C.nearest hs hne i) - f' x) +
          (fderiv ℝ (C.bump i : E → ℝ) y).smulRight
            (C.affine hs hne f f' i y - C.extension hs hne f f' y)‖ ≤
          ‖C.bump i y • (f' (C.nearest hs hne i) - f' x)‖ +
            ‖(fderiv ℝ (C.bump i : E → ℝ) y).smulRight
              (C.affine hs hne f f' i y - C.extension hs hne f f' y)‖ :=
        norm_add_le _ _
      _ ≤ C.bump i y * η +
          (K / C.radius i) * (8 * η * whitneyScale s y) := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (C.bump i).nonneg]
          exact mul_le_mul_of_nonneg_left (hL i hiactive) (C.bump i).nonneg
        · rw [ContinuousLinearMap.norm_smulRight_apply]
          exact mul_le_mul hbumpderiv haffine (norm_nonneg _) (by positivity)
      _ ≤ C.bump i y * η +
          (K / C.radius i) * (8 * η * (35 * C.radius i)) := by
        gcongr
      _ = C.bump i y * η + 280 * K * η := by
        field_simp [hrpos.ne']
        ring
  rw [C.fderiv_extension_sub_eq hs hne f f' hyset (f' x),
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hDpos]
  calc
    (C.denominator y)⁻¹ *
        ‖Finset.sum I (fun i : C.ι =>
          C.bump i y • (f' (C.nearest hs hne i) - f' x) +
            (fderiv ℝ (C.bump i : E → ℝ) y).smulRight
              (C.affine hs hne f f' i y - C.extension hs hne f f' y))‖ ≤
      (C.denominator y)⁻¹ * ∑ i ∈ I,
        (C.bump i y * η + 280 * K * η) := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le_of_le I hterm) hDinv
    _ = (C.denominator y)⁻¹ *
        (C.denominator y * η + I.card * (280 * K * η)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hdenom]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = η + (C.denominator y)⁻¹ * (I.card * (280 * K * η)) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hDpos.ne', one_mul]
    _ ≤ η + 1 * (M * (280 * K * η)) := by
      gcongr
    _ = (1 + 280 * M * K) * η := by ring

private theorem WhitneyBallCover.norm_extension_sub_base_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) {x y : E} (hx : x ∈ s)
    (hyset : y ∈ sᶜ) (hy : dist y x < 29 / 32) {η : ℝ} (hη : 0 ≤ η)
    (hL : ∀ i ∈ C.outerActive y, ‖f' (C.nearest hs hne i) - f' x‖ ≤ η)
    (hR : ∀ i ∈ C.outerActive y,
      ‖f (C.nearest hs hne i) - f x -
        f' x (C.nearest hs hne i - x)‖ ≤
          η * ‖C.nearest hs hne i - x‖) :
    ‖C.extension hs hne f f' y - f x - f' x (y - x)‖ ≤
      4 * η * dist y x := by
  let I : Finset C.ι := (C.outerActive_finite y).toFinset
  let q := f x + f' x (y - x)
  have hdenom : C.denominator y = ∑ i ∈ I, C.bump i y := by
    simpa only [I] using C.denominator_eq_sum_outerActive y
  have hrepr : C.extension hs hne f f' y - f x - f' x (y - x) =
      (C.denominator y)⁻¹ • ∑ i ∈ I, C.bump i y •
        (C.affine hs hne f f' i y - f x - f' x (y - x)) := by
    rw [C.extension_eq_weighted_sum hs hne f f' hyset]
    calc
      (C.denominator y)⁻¹ •
          (∑ i ∈ I, C.bump i y • C.affine hs hne f f' i y) - f x -
            f' x (y - x) =
        (C.denominator y)⁻¹ •
          (∑ i ∈ I, C.bump i y • C.affine hs hne f f' i y) - q := by
        dsimp only [q]
        module
      _ =
        (C.denominator y)⁻¹ •
          ((∑ i ∈ I, C.bump i y • C.affine hs hne f f' i y) -
            C.denominator y • q) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ (C.denominator_pos hyset).ne', one_smul]
      _ = (C.denominator y)⁻¹ • ∑ i ∈ I, C.bump i y •
          (C.affine hs hne f f' i y - q) := by
        congr 1
        rw [hdenom, Finset.sum_smul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_sub]
      _ = (C.denominator y)⁻¹ • ∑ i ∈ I, C.bump i y •
          (C.affine hs hne f f' i y - f x - f' x (y - x)) := by
        congr 2 with i
        dsimp only [q]
        module
  rw [hrepr, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (C.denominator_pos hyset)]
  calc
    (C.denominator y)⁻¹ *
        ‖∑ i ∈ I, C.bump i y •
          (C.affine hs hne f f' i y - f x - f' x (y - x))‖ ≤
      (C.denominator y)⁻¹ * ∑ i ∈ I,
        C.bump i y * (4 * η * dist y x) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (C.denominator_pos hyset).le)
      apply norm_sum_le_of_le
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (C.bump i).nonneg]
      apply mul_le_mul_of_nonneg_left _ (C.bump i).nonneg
      apply C.norm_affine_sub_base_le hs hne f f' hx
        ((C.outerActive_finite y).mem_toFinset.mp hi) hy hη
      · exact hL i ((C.outerActive_finite y).mem_toFinset.mp hi)
      · exact hR i ((C.outerActive_finite y).mem_toFinset.mp hi)
    _ = (C.denominator y)⁻¹ *
        (C.denominator y * (4 * η * dist y x)) := by
      rw [← Finset.sum_mul, hdenom]
    _ = 4 * η * dist y x := by
      rw [← mul_assoc, inv_mul_cancel₀ (C.denominator_pos hyset).ne', one_mul]

private theorem WhitneyBallCover.hasFDerivAt_extension_of_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (hjet : IsWhitneyOneJetOn f f' s)
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (C.extension hs hne f f') (f' x) x := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hest⟩ := hjet.exists_uniform_estimates hx (η := c / 4) (by positivity)
  let ρ := min (29 / 32) (δ * 29 / 64)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  have hynear : dist y x < 29 / 32 := (mem_ball.mp hy).trans_le (min_le_left _ _)
  have hydelta : 64 / 29 * dist y x < δ := by
    have := (mem_ball.mp hy).trans_le (min_le_right _ _)
    nlinarith
  have hGx : C.extension hs hne f f' x = f x :=
    C.extension_eq_on hs hne f f' hx
  by_cases hys : y ∈ s
  · have hyδ : dist y x < δ := by
      have hdist : 0 ≤ dist y x := dist_nonneg
      nlinarith
    have hrem := (hest y hys hyδ).2 x hx (by simpa using hδ)
    rw [C.extension_eq_on hs hne f f' hys, hGx]
    calc
      ‖f y - f x - f' x (y - x)‖ ≤ (c / 4) * ‖y - x‖ := hrem
      _ ≤ c * ‖y - x‖ := by gcongr; linarith
  · have hyset : y ∈ sᶜ := hys
    have hL : ∀ i ∈ C.outerActive y,
        ‖f' (C.nearest hs hne i) - f' x‖ ≤ c / 4 := by
      intro i hi
      apply (hest (C.nearest hs hne i) (C.nearest_mem hs hne i) ?_).1
      exact (C.dist_nearest_base_le_of_mem_outer_of_dist_lt hs hne hx hi hynear).trans_lt
        hydelta
    have hR : ∀ i ∈ C.outerActive y,
        ‖f (C.nearest hs hne i) - f x -
          f' x (C.nearest hs hne i - x)‖ ≤
            (c / 4) * ‖C.nearest hs hne i - x‖ := by
      intro i hi
      exact (hest (C.nearest hs hne i) (C.nearest_mem hs hne i)
        ((C.dist_nearest_base_le_of_mem_outer_of_dist_lt hs hne hx hi hynear).trans_lt
          hydelta)).2 x hx (by simpa using hδ)
    rw [hGx]
    calc
      ‖C.extension hs hne f f' y - f x - f' x (y - x)‖ ≤
          4 * (c / 4) * dist y x :=
        C.norm_extension_sub_base_le hs hne f f' hx hyset hynear (by positivity) hL hR
      _ = c * ‖y - x‖ := by rw [dist_eq_norm]; ring

private theorem WhitneyBallCover.continuousAt_fderiv_extension_of_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (C : WhitneyBallCover E s) (hs : IsClosed s) (hne : s.Nonempty)
    (f : E → F) (f' : E → E →L[ℝ] F) (hjet : IsWhitneyOneJetOn f f' s)
    {x : E} (hx : x ∈ s) :
    ContinuousAt (fderiv ℝ (C.extension hs hne f f')) x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A : ℝ := 1 + 280 * (C.colorCount * 5 ^ Module.finrank ℝ E : ℕ) *
    whitneyBumpLipschitzConstant E
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hAone : 1 ≤ A := by
    dsimp only [A]
    exact le_add_of_nonneg_right (by positivity)
  let η := ε / (2 * A)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hA)
  obtain ⟨δ, hδ, hest⟩ := hjet.exists_uniform_estimates hx hη
  let ρ := min (29 / 32) (δ * 29 / 64)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  have hynear : dist y x < 29 / 32 := hy.trans_le (min_le_left _ _)
  have hydelta : 64 / 29 * dist y x < δ := by
    have := hy.trans_le (min_le_right _ _)
    nlinarith
  have hdist : 0 ≤ dist y x := dist_nonneg
  have hyδ : dist y x < δ := by nlinarith
  have hxderiv : fderiv ℝ (C.extension hs hne f f') x = f' x :=
    (C.hasFDerivAt_extension_of_mem hs hne f f' hjet hx).fderiv
  rw [hxderiv, dist_eq_norm]
  by_cases hys : y ∈ s
  · rw [(C.hasFDerivAt_extension_of_mem hs hne f f' hjet hys).fderiv]
    exact (hest y hys hyδ).1.trans_lt (div_lt_self hε (by nlinarith [hAone]))
  · have hyset : y ∈ sᶜ := hys
    have hL : ∀ i ∈ C.outerActive y,
        ‖f' (C.nearest hs hne i) - f' x‖ ≤ η := by
      intro i hi
      exact (hest (C.nearest hs hne i) (C.nearest_mem hs hne i)
        ((C.dist_nearest_base_le_of_mem_outer_of_dist_lt hs hne hx hi hynear).trans_lt
          hydelta)).1
    have hR : ∀ i ∈ C.outerActive y, ∀ j ∈ C.outerActive y,
        ‖f (C.nearest hs hne i) - f (C.nearest hs hne j) -
          f' x (C.nearest hs hne i - C.nearest hs hne j)‖ ≤
            η * ‖C.nearest hs hne i - C.nearest hs hne j‖ := by
      intro i hi j hj
      exact (hest (C.nearest hs hne i) (C.nearest_mem hs hne i)
        ((C.dist_nearest_base_le_of_mem_outer_of_dist_lt hs hne hx hi hynear).trans_lt
          hydelta)).2 (C.nearest hs hne j) (C.nearest_mem hs hne j)
        ((C.dist_nearest_base_le_of_mem_outer_of_dist_lt hs hne hx hj hynear).trans_lt
          hydelta)
    have hbound := C.norm_fderiv_extension_sub_le hs hne f f' hx hyset hynear hη.le hL hR
    calc
      ‖fderiv ℝ (C.extension hs hne f f') y - f' x‖ ≤ A * η := by
        simpa only [A] using hbound
      _ = ε / 2 := by
        dsimp only [η]
        field_simp [hA.ne']
      _ < ε := half_lt_self hε

theorem IsWhitneyOneJetOn.exists_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
    (h : IsWhitneyOneJetOn f f' s) (hs : IsClosed s) :
    ∃ g : E → F, ContDiff ℝ 1 g ∧ EqOn g f s ∧ EqOn (fderiv ℝ g) f' s := by
  by_cases hne : s.Nonempty
  · let C := Classical.choice (exists_whitneyBallCover hs hne)
    refine ⟨C.extension hs hne f f', ?_, C.extension_eq_on hs hne f f', ?_⟩
    · rw [contDiff_one_iff_fderiv]
      constructor
      · intro x
        by_cases hx : x ∈ s
        · exact (C.hasFDerivAt_extension_of_mem hs hne f f' h hx).differentiableAt
        · exact (C.contDiffAt_extension_of_notMem hs hne f f' hx).differentiableAt_one
      · rw [continuous_iff_continuousAt]
        intro x
        by_cases hx : x ∈ s
        · exact C.continuousAt_fderiv_extension_of_mem hs hne f f' h hx
        · exact (C.contDiffAt_extension_of_notMem hs hne f f' hx).continuousAt_fderiv
            (by norm_num)
    · intro x hx
      exact (C.hasFDerivAt_extension_of_mem hs hne f f' h hx).fderiv
  · refine ⟨fun _ => 0, contDiff_const, ?_, ?_⟩
    · intro x hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro x hx
      exact False.elim (hne ⟨x, hx⟩)

theorem LipschitzWith.exists_contDiff_eqOn_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → F, ∃ s : Set E, IsClosed s ∧
      (Measure.addHaar : Measure E) sᶜ < ε ∧ ContDiff ℝ 1 g ∧
        EqOn g f s ∧ EqOn (fderiv ℝ g) (fderiv ℝ f) s := by
  obtain ⟨s, hs, hsmeasure, hjet⟩ := hf.exists_isClosed_isWhitneyOneJetOn hε
  obtain ⟨g, hg, hgf, hgf'⟩ := hjet.exists_contDiff hs
  exact ⟨g, s, hs, hsmeasure, hg, hgf, hgf'⟩

theorem LipschitzWith.exists_contDiff_measure_ne_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → F, ContDiff ℝ 1 g ∧
      (Measure.addHaar : Measure E)
        ({x | f x ≠ g x} ∪ {x | fderiv ℝ f x ≠ fderiv ℝ g x}) < ε := by
  obtain ⟨g, s, hs, hsmeasure, hg, hgf, hgf'⟩ :=
    hf.exists_contDiff_eqOn_fderiv hε
  refine ⟨g, hg, (measure_mono ?_).trans_lt hsmeasure⟩
  intro x hx hxs
  rcases hx with hx | hx
  · exact hx (hgf hxs).symm
  · exact hx (hgf' hxs).symm
