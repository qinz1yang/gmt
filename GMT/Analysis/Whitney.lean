import GMT.Analysis.Lipschitz

open Asymptotics Filter MeasureTheory Metric Set

open scoped ENNReal NNReal Topology

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
