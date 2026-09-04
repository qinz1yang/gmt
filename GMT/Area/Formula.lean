import GMT.Area.Jacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Data.Set.Card.Arithmetic

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal MeasureTheory Function NNReal

namespace Area

def multiplicity {E F : Type*} (f : E → F) (s : Set E) (y : F) : ℝ≥0∞ :=
  ENat.toENNReal (encard (s ∩ f ⁻¹' {y}))

theorem multiplicity_eq_zero_of_not_mem_image {E F : Type*} {f : E → F} {s : Set E} {y : F}
    (hy : y ∉ f '' s) : multiplicity f s y = 0 := by
  have hset : s ∩ f ⁻¹' {y} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
      iff_false]
    rintro ⟨hxs, hxy⟩
    exact hy ⟨x, hxs, hxy⟩
  rw [multiplicity, hset, Set.encard_empty, ENat.toENNReal_zero]

theorem multiplicity_eq_one_of_injOn {E F : Type*} {f : E → F} {s : Set E} (hf : InjOn f s)
    {y : F} (hy : y ∈ f '' s) : multiplicity f s y = 1 := by
  obtain ⟨x, hxs, rfl⟩ := hy
  have hset : s ∩ f ⁻¹' {f x} = {x} := by
    ext z
    constructor
    · rintro ⟨hzs, hzf⟩
      have : z = x := hf hzs hxs (by simpa only [mem_preimage, mem_singleton_iff] using hzf)
      simp [this]
    · intro hz
      simp only [mem_singleton_iff] at hz
      subst hz
      exact ⟨hxs, rfl⟩
  rw [multiplicity, hset, encard_eq_one.mpr ⟨x, rfl⟩, ENat.toENNReal_one]

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem injective_area_formula
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hf : InjOn f s) :
    μHE[Module.finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) := by
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  have h := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    (volume : Measure E) hs (fun x hx => (hf' x hx).hasFDerivWithinAt) hf
  calc
    volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| := h.symm
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) := by
      apply setLIntegral_congr_fun hs
      intro x hx
      simp [Area.jacobian, (hf' x hx).fderiv, LinearMap.normDet_eq_abs_det]

theorem injective_area_formula_weighted
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (g : E → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hf : InjOn f s) :
    ∫⁻ y in f '' s, g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure E) hs (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g
  calc
    ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) := h
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      apply setLIntegral_congr_fun hs
      intro x hx
      simp [Area.jacobian, (hf' x hx).fderiv, LinearMap.normDet_eq_abs_det]

theorem monotone_area_formula_real
    {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s) :
    ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf g

theorem monotone_area_formula_real_unweighted
    {f f' : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s) :
    volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal (f' x) := by
  exact (MeasureTheory.lintegral_deriv_eq_volume_image_of_monotoneOn hs hf' hf).symm

theorem antitone_area_formula_real
    {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s) :
    ∫⁻ y in f '' s, g y = ∫⁻ x in s, ENNReal.ofReal (-f' x) * g (f x) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hf' hf g

theorem antitone_area_formula_real_unweighted
    {f f' : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s) :
    volume (f '' s) = ∫⁻ x in s, ENNReal.ofReal (-f' x) := by
  exact (MeasureTheory.lintegral_deriv_eq_volume_image_of_antitoneOn hs hf' hf).symm

theorem monotone_area_formula_real_with_multiplicity
    {f f' : ℝ → ℝ} {s : Set ℝ} (g : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s) :
    ∫⁻ y : ℝ, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) := by
  let bad : Set ℝ := {c | ∃ x y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c}
  have hbad : bad.Countable := hf.countable_setOfPred_two_preimages
  have hbad_ae : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ∉ bad := by
    apply ae_iff.mpr
    simpa [bad] using hbad.measure_zero (volume : Measure ℝ)
  have hpoint : ∀ y, y ∉ bad →
      multiplicity f s y * g y = (f '' s).indicator g y := by
    intro y hybad
    by_cases hy : y ∈ f '' s
    · have hyimage : y ∈ f '' s := hy
      obtain ⟨x, hxs, hxy⟩ := hy
      have hset : s ∩ f ⁻¹' {y} = {x} := by
        ext z
        constructor
        · rintro ⟨hzs, hzf⟩
          have hzy : f z = y := by simpa using hzf
          by_cases hzx : z = x
          · simp [hzx]
          · rcases lt_or_gt_of_ne hzx with hzx | hzx
            · exfalso
              apply hybad
              exact ⟨z, x, hzs, hxs, hzx, hzy, hxy⟩
            · exfalso
              apply hybad
              exact ⟨x, z, hxs, hzs, hzx, hxy, hzy⟩
        · intro hz
          simp only [mem_singleton_iff] at hz
          subst hz
          exact ⟨hxs, by simp [hxy]⟩
      rw [multiplicity, hset, encard_eq_one.mpr ⟨x, rfl⟩, ENat.toENNReal_one]
      simp [Set.indicator, hyimage]
    · have hyimage : y ∉ f '' s := hy
      rw [multiplicity_eq_zero_of_not_mem_image hyimage]
      simp [Set.indicator, hyimage]
  calc
    ∫⁻ y : ℝ, multiplicity f s y * g y =
        ∫⁻ y : ℝ, (f '' s).indicator g y :=
      lintegral_congr_ae (hbad_ae.mono fun y hy => hpoint y hy)
    _ = ∫⁻ y in f '' s, g y :=
      MeasureTheory.lintegral_indicator (hs.image_of_monotoneOn hf) g
    _ = ∫⁻ x in s, ENNReal.ofReal (f' x) * g (f x) :=
      MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf g

theorem area_formula_of_finite_injective_partition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (n : ℕ)
    (t : Fin n → Set E) (g : E → ℝ≥0∞)
    (hpart : (⋃ i, t i) = s) (ht : ∀ i, MeasurableSet (t i))
    (hdisj : ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (t i) (t j))
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i : Fin n, InjOn f (t i))
    (hg : Measurable g) :
    ∫⁻ y, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  classical
  have hmult : ∀ y, multiplicity f s y = ∑ i, multiplicity f (t i) y := by
    intro y
    simp only [multiplicity, ← hpart]
    rw [Set.iUnion_inter]
    have hpair : Pairwise (Function.onFun Disjoint (fun i : Fin n => t i ∩ f ⁻¹' {y})) := by
      intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    rw [Set.encard_iUnion_of_finite hpair]
    rw [← finsum_mem_univ,
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite (Set.univ : Set (Fin n)))]
    let u : Finset (Fin n) := Finset.univ
    have hsum (q : Fin n → ℕ∞) : ENat.toENNReal (∑ i ∈ u, q i) =
        ∑ i ∈ u, ENat.toENNReal (q i) := by
      induction u using Finset.induction_on with
      | empty => simp
      | @insert a u ha ih => simp [Finset.sum_insert, ha, ENat.toENNReal_add, ih]
    simpa [u] using hsum (fun i => (t i ∩ f ⁻¹' {y}).encard)
  have hsubset : ∀ (i : Fin n) x, x ∈ t i → x ∈ s := by
    intro i x hx
    rw [← hpart]
    exact mem_iUnion.2 ⟨i, hx⟩
  have himage : ∀ i : Fin n, MeasurableSet (f '' t i) := by
    intro i
    exact MeasureTheory.measurable_image_of_fderivWithin (ht i)
      (fun x hx => (hf' x (hsubset i x hx)).hasFDerivWithinAt) (hfinj i)
  have hpiece : ∀ i : Fin n, ∫⁻ y, multiplicity f (t i) y * g y =
      ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    calc
      ∫⁻ y, multiplicity f (t i) y * g y = ∫⁻ y, (f '' t i).indicator g y :=
        lintegral_congr (fun y => hpoint y)
      _ = ∫⁻ y in f '' t i, g y := MeasureTheory.lintegral_indicator (himage i) g
      _ = ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) :=
        injective_area_formula_weighted g (ht i)
          (fun x hx => hf' x (hsubset i x hx)) (hfinj i)
  have hmeas : ∀ i : Fin n, Measurable (fun y => multiplicity f (t i) y * g y) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    rw [show (fun y => multiplicity f (t i) y * g y) = (f '' t i).indicator g by
      funext y; exact hpoint y]
    exact hg.indicator (himage i)
  calc
    ∫⁻ y, multiplicity f s y * g y =
        ∫⁻ y, (∑ i, multiplicity f (t i) y) * g y :=
      lintegral_congr (fun y => by rw [hmult y])
    _ = ∫⁻ y, ∑ i, multiplicity f (t i) y * g y := by
      apply lintegral_congr
      intro y
      rw [Finset.sum_mul]
    _ = ∑ i, ∫⁻ y, multiplicity f (t i) y * g y := by
      simpa using MeasureTheory.lintegral_finsetSum (μ := (volume : Measure E))
        (Finset.univ : Finset (Fin n)) (fun i _ => hmeas i)
    _ = ∑ i, ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpiece i
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [← hpart, Measure.restrict_iUnion hdisj ht, MeasureTheory.lintegral_sum_measure]
      simp [tsum_fintype]

private lemma countable_multiplicity
    {E F : Type*} {f : E → F} {t : ℕ → Set E}
    (hdisj : Pairwise (Disjoint on t))
    (hfinj : ∀ i, InjOn f (t i)) (y : F) :
    multiplicity f (⋃ i, t i) y = ∑' i, multiplicity f (t i) y := by
  let u : ℕ → Set E := fun i => t i ∩ f ⁻¹' {y}
  let I : Set ℕ := {i | (u i).Nonempty}
  have hdisju : Pairwise (Disjoint on u) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  have hterm : ∀ i, multiplicity f (t i) y = I.indicator (fun _ => (1 : ℝ≥0∞)) i := by
    intro i
    by_cases hi : i ∈ I
    · have hne : (u i).Nonempty := hi
      obtain ⟨x, hx⟩ := hne
      have hset : u i = {x} := by
        ext z
        constructor
        · intro hz
          exact Set.mem_singleton_iff.mpr ((hfinj i) hz.1 hx.1 (by
            calc f z = y := hz.2
            _ = f x := hx.2.symm))
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          exact hx
      rw [multiplicity, show t i ∩ f ⁻¹' {y} = u i from rfl, hset,
        encard_eq_one.mpr ⟨x, rfl⟩, ENat.toENNReal_one]
      simp [Set.indicator, hi]
    · have hempty : u i = ∅ := not_nonempty_iff_eq_empty.mp hi
      rw [multiplicity, show t i ∩ f ⁻¹' {y} = u i from rfl, hempty, Set.encard_empty,
        ENat.toENNReal_zero]
      simp [Set.indicator, hi]
  have htsum : (∑' i, multiplicity f (t i) y) = I.encard := by
    rw [show (fun i => multiplicity f (t i) y) = I.indicator (fun _ => (1 : ℝ≥0∞)) by
      funext i; exact hterm i]
    rw [← tsum_subtype I (fun _ : ℕ => (1 : ℝ≥0∞)), ENNReal.tsum_set_one]
  have hunion : (⋃ i, u i).encard = I.encard := by
    obtain hfin | hinf := I.finite_or_infinite
    · have finiteI : Finite I := hfin.fintype.finite
      let v : I → Set E := fun i => u i.1
      have hvdisj : Pairwise (Disjoint on v) := by
        intro i j hij
        apply hdisju
        intro h
        apply hij
        exact Subtype.ext h
      have henc := Set.encard_iUnion_of_finite hvdisj
      have hEq : (⋃ i : I, v i) = ⋃ i : ℕ, u i := by
        ext z
        constructor
        · intro hz
          obtain ⟨i, hz⟩ := mem_iUnion.1 hz
          exact mem_iUnion.2 ⟨i.1, hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := mem_iUnion.1 hz
          by_cases hIi : i ∈ I
          · exact mem_iUnion.2 ⟨⟨i, hIi⟩, hi⟩
          · change ¬ (u i).Nonempty at hIi
            exact False.elim (hIi ⟨z, hi⟩)
      have hvcard : ∀ i : I, (v i).encard = 1 := by
        intro i
        apply encard_eq_one.mpr
        refine ⟨i.2.choose, ?_⟩
        ext z
        constructor
        · intro hz
          apply Set.mem_singleton_iff.mpr
          apply (hfinj i.1) hz.1 i.2.choose_spec.1
          calc f z = y := hz.2
            _ = f i.2.choose := i.2.choose_spec.2.symm
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          exact i.2.choose_spec
      rw [← hEq, henc]
      simp_rw [hvcard]
      let e : (↑hfin.toFinset) ≃ I :=
        { toFun := fun i => ⟨i, hfin.mem_toFinset.mp i.2⟩
          invFun := fun i => ⟨i, hfin.mem_toFinset.mpr i.2⟩
          left_inv := by intro i; rfl
          right_inv := by intro i; rfl }
      let J : Finset I := hfin.toFinset.attach.map e.toEmbedding
      have hsupport : Function.support (fun _ : I => (1 : ℕ∞)) ⊆ J := by
        intro i hi
        apply Finset.mem_map.mpr
        refine ⟨e.symm i, Finset.mem_attach _ _, ?_⟩
        simp [e]
      rw [finsum_eq_sum_of_support_subset (fun _ : I => (1 : ℕ∞)) (s := J) hsupport]
      rw [Finset.sum_const, show J.card = hfin.toFinset.card by simp [J]]
      have hcard : I.encard = (hfin.toFinset.card : ℕ∞) := by
        change ENat.card I = (hfin.toFinset.card : ℕ∞)
        rw [@ENat.card_eq_coe_natCard I finiteI, Nat.card_coe_set_eq,
          Set.ncard_eq_toFinset_card I hfin]
      calc
        hfin.toFinset.card • (1 : ℕ∞) = (hfin.toFinset.card : ℕ∞) := by
          rw [nsmul_eq_mul, mul_one]
        _ = I.encard := hcard.symm
    · have hIinf : Infinite I := infinite_coe_iff.mpr hinf
      let fset : I → Set E := fun i => u i.1
      have hfset_inj : Function.Injective fset := by
        intro i j hij
        by_contra hne
        have hd : Disjoint (u i.1) (u j.1) := by
          apply hdisju
          intro h
          apply hne
          exact Subtype.ext h
        obtain ⟨x, hx⟩ := j.2
        apply hd.le_bot
        exact ⟨by
          change x ∈ fset i
          rw [hij]
          exact hx, hx⟩
      have huinf : (⋃ i : I, fset i).Infinite := Set.infinite_iUnion hfset_inj
      have hEq : (⋃ i : I, fset i) = ⋃ i : ℕ, u i := by
        ext z
        constructor
        · intro hz
          obtain ⟨i, hz⟩ := mem_iUnion.1 hz
          exact mem_iUnion.2 ⟨i.1, hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := mem_iUnion.1 hz
          have hIi : i ∈ I := ⟨z, hi⟩
          exact mem_iUnion.2 ⟨⟨i, hIi⟩, hi⟩
      rw [← hEq, encard_eq_top huinf, encard_eq_top hinf]
  rw [multiplicity, show (⋃ i, t i) ∩ f ⁻¹' {y} = ⋃ i, u i by
    ext z
    simp [u], hunion, htsum]

theorem area_formula_of_countable_injective_partition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} (t : ℕ → Set E)
    (g : E → ℝ≥0∞) (hpart : (⋃ i, t i) = s) (ht : ∀ i, MeasurableSet (t i))
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (t i) (t j))
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hfinj : ∀ i : ℕ, InjOn f (t i))
    (hg : Measurable g) :
    ∫⁻ y, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  classical
  have hsubset : ∀ i x, x ∈ t i → x ∈ s := by
    intro i x hx
    rw [← hpart]
    exact mem_iUnion.2 ⟨i, hx⟩
  have himage : ∀ i : ℕ, MeasurableSet (f '' t i) := by
    intro i
    exact MeasureTheory.measurable_image_of_fderivWithin (ht i)
      (fun x hx => (hf' x (hsubset i x hx)).hasFDerivWithinAt) (hfinj i)
  have hpiece : ∀ i : ℕ, ∫⁻ y, multiplicity f (t i) y * g y =
      ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    calc
      ∫⁻ y, multiplicity f (t i) y * g y = ∫⁻ y, (f '' t i).indicator g y :=
        lintegral_congr (fun y => hpoint y)
      _ = ∫⁻ y in f '' t i, g y := MeasureTheory.lintegral_indicator (himage i) g
      _ = ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) :=
        injective_area_formula_weighted g (ht i)
          (fun x hx => hf' x (hsubset i x hx)) (hfinj i)
  have hmeas : ∀ i : ℕ, AEMeasurable (fun y => multiplicity f (t i) y * g y)
      (volume : Measure E) := by
    intro i
    have hpoint : ∀ y, multiplicity f (t i) y * g y = (f '' t i).indicator g y := by
      intro y
      by_cases hy : y ∈ f '' t i
      · rw [multiplicity_eq_one_of_injOn (hfinj i) hy]
        simp [Set.indicator, hy]
      · rw [multiplicity_eq_zero_of_not_mem_image hy]
        simp [Set.indicator, hy]
    rw [show (fun y => multiplicity f (t i) y * g y) = (f '' t i).indicator g by
      funext y; exact hpoint y]
    exact (hg.indicator (himage i)).aemeasurable
  have hmult : ∀ y, multiplicity f s y = ∑' i, multiplicity f (t i) y := by
    intro y
    rw [← hpart]
    exact countable_multiplicity hdisj hfinj y
  calc
    ∫⁻ y, multiplicity f s y * g y =
        ∫⁻ y, (∑' i, multiplicity f (t i) y) * g y :=
      lintegral_congr (fun y => by rw [hmult y])
    _ = ∫⁻ y, ∑' i, multiplicity f (t i) y * g y := by
      apply lintegral_congr
      intro y
      rw [ENNReal.tsum_mul_right]
    _ = ∑' i, ∫⁻ y, multiplicity f (t i) y * g y :=
      MeasureTheory.lintegral_tsum hmeas
    _ = ∑' i, ∫⁻ x in t i, ENNReal.ofReal (jacobian f x) * g (f x) := by
      apply tsum_congr
      intro i
      exact hpiece i
    _ = ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [← hpart, MeasureTheory.lintegral_iUnion ht hdisj]

private def equiv_of_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (h : A.det ≠ 0) : E ≃L[ℝ] E := by
  apply ContinuousLinearEquiv.ofBijective A
  · have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hk
      apply h
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
    exact hker
  · apply LinearMap.range_eq_top.mpr
    apply LinearMap.injective_iff_surjective.mp
    have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hk
      apply h
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
    exact (LinearMap.ker_eq_bot).mp hker

private theorem equiv_of_det_ne_zero_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (h : A.det ≠ 0) :
    (equiv_of_det_ne_zero A h : E →L[ℝ] E) = A := by
  change ↑(ContinuousLinearEquiv.ofBijective A _ _) = A
  exact ContinuousLinearEquiv.coe_ofBijective A _ _

theorem area_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} (g : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hf : ContDiff ℝ 1 f) (hg : Measurable g) :
      ∫⁻ y, multiplicity f s y * g y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
  classical
  let f' : E → E →L[ℝ] E := fun x => fderiv ℝ f x
  let d : E → ℝ := fun x => (f' x).det
  let r : Set E := s ∩ d ⁻¹' {0}ᶜ
  let c : Set E := s \ r
  have hfd : ∀ x, HasFDerivAt f (f' x) x := by
    intro x
    exact (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hdm : Measurable d := by
    exact ContinuousLinearMap.continuous_det.measurable.comp
      (hf.continuous_fderiv one_ne_zero).measurable
  have hr : MeasurableSet r := by
    exact hs.inter ((MeasurableSet.singleton (0 : ℝ)).compl.preimage hdm)
  have hc : MeasurableSet c := hs.diff hr
  have hcrit : volume (f '' c) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (volume : Measure E)
    · intro x hx
      exact (hfd x).hasFDerivWithinAt
    · intro x hx
      have hxsr : x ∈ s := hx.1
      have hxnr : x ∉ r := hx.2
      have hxd : d x = 0 := by
        by_contra hne
        apply hxnr
        exact ⟨hxsr, hne⟩
      exact hxd
  have hjzero : ∀ x ∈ c, jacobian f x = 0 := by
    intro x hxc
    have hxd : d x = 0 := by
      by_contra hne
      apply hxc.2
      exact ⟨hxc.1, hne⟩
    have hdet : (f' x).det = 0 := by simpa [d] using hxd
    rw [jacobian_of_hasFDerivAt (hfd x), LinearMap.normDet_eq_norm_det]
    simp [hdet]
  have hreg_deriv : ∀ x ∈ r, HasFDerivWithinAt f (f' x) r x := by
    intro x hx
    exact (hfd x).hasFDerivWithinAt
  let ρ : (E →L[ℝ] E) → ℝ≥0 := fun A =>
    if hE : Subsingleton E then 1
    else if hA : A.det ≠ 0 then (NNNorm.nnnorm ((equiv_of_det_ne_zero A hA).symm : E →L[ℝ] E))⁻¹ / 2
    else 1
  have hρ : ∀ A, ρ A ≠ 0 := by
    intro A
    by_cases hE : Subsingleton E
    · simp [ρ, hE]
    · simp only [ρ, hE, ↓reduceDIte]
      split_ifs with hA
      · have hpos : 0 < NNNorm.nnnorm ((equiv_of_det_ne_zero A hA).symm : E →L[ℝ] E) :=
          (equiv_of_det_ne_zero A hA).subsingleton_or_nnnorm_symm_pos.resolve_left hE
        exact div_ne_zero (inv_ne_zero hpos.ne') (by norm_num)
      · simp
  obtain ⟨t, A, ht_disj, ht_meas, ht_cover, ht_approx, ht_repr⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f r f' hreg_deriv ρ hρ
  have hreg_nonempty_or : r.Nonempty ∨ r = ∅ := by
    rcases eq_empty_or_nonempty r with hre | hrne
    · exact Or.inr hre
    · exact Or.inl hrne
  rcases hreg_nonempty_or with hrne | hre
  · have hpiece_inj : ∀ n : ℕ, InjOn f (r ∩ t n) := by
      intro n
      obtain ⟨y, hyr, hAn⟩ := ht_repr hrne n
      have hdet : (A n).det ≠ 0 := by
        rw [hAn]
        simpa [r, d] using hyr.2
      let e := equiv_of_det_ne_zero (A n) hdet
      have he : (e : E →L[ℝ] E) = A n := by
        exact equiv_of_det_ne_zero_coe (A n) hdet
      have happrox : ApproximatesLinearOn f (e : E →L[ℝ] E) (r ∩ t n) (ρ (A n)) := by
        simpa [he] using ht_approx n
      have hc' : Subsingleton E ∨ ρ (A n) < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := by
        rcases e.subsingleton_or_nnnorm_symm_pos with hE | hpos
        · exact Or.inl hE
        · right
          have hEnot : ¬ Subsingleton E := by
            intro hE
            have hz : (e.symm : E →L[ℝ] E) = 0 := Subsingleton.elim _ _
            simp [hz] at hpos
          simpa [ρ, hEnot, hdet, e] using (NNReal.half_lt_self (inv_ne_zero hpos.ne'))
      exact happrox.injOn hc'
    let u : ℕ → Set E := fun n => r ∩ t n
    have hu_meas : ∀ n, MeasurableSet (u n) := fun n => hr.inter (ht_meas n)
    have hu_disj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (u i) (u j) := by
      intro i j hij
      exact (ht_disj hij).mono inter_subset_right inter_subset_right
    have hu_part : (⋃ n, u n) = r := by
      dsimp [u]
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
        exact hxn.1
      · intro x hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 (ht_cover hx)
        exact mem_iUnion.2 ⟨n, ⟨hx, hxn⟩⟩
    have hformula : ∫⁻ y, multiplicity f r y * g y =
        ∫⁻ x in r, ENNReal.ofReal (jacobian f x) * g (f x) := by
      exact area_formula_of_countable_injective_partition u g hu_part hu_meas hu_disj
        (fun x _ => hfd x) hpiece_inj hg
    have hleft : ∫⁻ y, multiplicity f s y * g y = ∫⁻ y, multiplicity f r y * g y := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' c := by
        apply ae_iff.mpr
        have hset : {a : E | ¬ a ∉ f '' c} = f '' c := by
          ext a
          simp
        rw [hset]
        exact hcrit
      filter_upwards [hae] with y hy
      have hset : s ∩ f ⁻¹' {y} = r ∩ f ⁻¹' {y} := by
        ext x
        constructor
        · rintro ⟨hxs, hxy⟩
          by_cases hxr : x ∈ r
          · exact ⟨hxr, hxy⟩
          · exfalso
            apply hy
            exact ⟨x, ⟨hxs, hxr⟩, hxy⟩
        · rintro ⟨hxr, hxy⟩
          exact ⟨hxr.1, hxy⟩
      rw [multiplicity, multiplicity, hset]
    have hright : ∫⁻ x in r, ENNReal.ofReal (jacobian f x) * g (f x) =
        ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) := by
      rw [← MeasureTheory.lintegral_indicator hr, ← MeasureTheory.lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hxr : x ∈ r
      · have hxs : x ∈ s := hxr.1
        simp [Set.indicator, hxr, hxs]
      · by_cases hxs : x ∈ s
        · have hxc : x ∈ c := ⟨hxs, hxr⟩
          rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxr, hjzero x hxc]
          simp
        · simp [Set.indicator, hxr, hxs]
    exact hleft.trans (hformula.trans hright)
  · have hceq : c = s := by
      ext x
      constructor
      · exact fun hx => hx.1
      · intro hxs
        exact ⟨hxs, by simp [hre]⟩
    have hcrit' : volume (f '' s) = 0 := by simpa [hceq] using hcrit
    have hleft : ∫⁻ y, multiplicity f s y * g y = 0 := by
      rw [← lintegral_zero]
      apply lintegral_congr_ae
      have hae : ∀ᵐ y : E ∂(volume : Measure E), y ∉ f '' s := by
        apply ae_iff.mpr
        have hset : {a : E | ¬ a ∉ f '' s} = f '' s := by
          ext a
          simp
        rw [hset]
        exact hcrit'
      filter_upwards [hae] with y hy
      rw [multiplicity_eq_zero_of_not_mem_image hy]
      simp
    have hright : ∫⁻ x in s, ENNReal.ofReal (jacobian f x) * g (f x) = 0 := by
      rw [← MeasureTheory.lintegral_indicator hs, ← lintegral_zero]
      apply lintegral_congr_ae
      filter_upwards [] with x
      by_cases hxs : x ∈ s
      · have hxc : x ∈ c := by simpa [hceq] using hxs
        rw [Set.indicator_of_mem hxs, hjzero x hxc]
        simp
      · simp [Set.indicator, hxs]
    exact hleft.trans hright.symm

theorem area_formula_unweighted
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {s : Set E} (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f) :
      ∫⁻ y, multiplicity f s y =
      ∫⁻ x in s, ENNReal.ofReal (jacobian f x) := by
  simpa only [mul_one] using
    (area_formula (f := f) (s := s) (fun _ => (1 : ℝ≥0∞)) hs hf measurable_const)

end Area
