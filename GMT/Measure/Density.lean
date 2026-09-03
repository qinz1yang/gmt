import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

open Filter Metric Set
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace MeasureTheory

-- Simon, Chapter 4, formula (3.9), p. 91: the n-dimensional unit-ball constant omega_n.
def euclideanUnitBallVolume (n : ℕ) : ℝ≥0∞ :=
  μHE[n] (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

theorem euclideanUnitBallVolume_ne_zero (n : ℕ) : euclideanUnitBallVolume n ≠ 0 := by
  rw [euclideanUnitBallVolume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'

theorem euclideanUnitBallVolume_ne_top (n : ℕ) : euclideanUnitBallVolume n ≠ ∞ := by
  rw [euclideanUnitBallVolume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact measure_closedBall_lt_top.ne

private theorem euclideanHausdorffMeasure_unit_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (μHE[Module.finrank ℝ E] : Measure E) (closedBall 0 1) =
      euclideanUnitBallVolume (Module.finrank ℝ E) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  rw [euclideanUnitBallVolume]
  calc
    (μHE[Module.finrank ℝ E] : Measure E) (closedBall 0 1) =
        (μHE[Module.finrank ℝ E] :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
            (e '' closedBall 0 1) :=
      (e.isometry.euclideanHausdorffMeasure_image (closedBall 0 1)).symm
    _ = (μHE[Module.finrank ℝ E] :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
            (closedBall 0 1) := by
      rw [e.image_closedBall]
      simp only [map_zero]

theorem euclideanHausdorffMeasure_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x : E) {r : ℝ} (hr : 0 < r) :
    (μHE[Module.finrank ℝ E] : Measure E) (closedBall x r) =
      (ENNReal.ofReal r) ^ Module.finrank ℝ E *
        euclideanUnitBallVolume (Module.finrank ℝ E) := by
  have hcenter : (μHE[Module.finrank ℝ E] : Measure E) (closedBall x r) =
      (μHE[Module.finrank ℝ E] : Measure E) (closedBall (0 : E) r) := by
    have h := measure_preimage_vadd (μHE[Module.finrank ℝ E] : Measure E)
      (-x) (closedBall (0 : E) r)
    have hset : (fun y : E => -x +ᵥ y) ⁻¹' closedBall (0 : E) r = closedBall x r := by
      ext y
      simp [mem_closedBall, dist_eq_norm, vadd_eq_add, sub_eq_add_neg, add_comm]
    rw [hset] at h
    exact h
  have hscale : (r • ·) '' closedBall (0 : E) 1 = closedBall 0 r := by
    simpa [Real.norm_of_nonneg hr.le] using
      Metric.smul_image_closedBall hr.ne' (0 : E) 1
  calc
    (μHE[Module.finrank ℝ E] : Measure E) (closedBall x r) =
        (μHE[Module.finrank ℝ E] : Measure E) (closedBall (0 : E) r) := hcenter
    _ = (μHE[Module.finrank ℝ E] : Measure E)
        ((r • ·) '' closedBall (0 : E) 1) :=
      congrArg (fun s : Set E => (μHE[Module.finrank ℝ E] : Measure E) s) hscale.symm
    _ = ‖r‖₊ ^ Module.finrank ℝ E •
        (μHE[Module.finrank ℝ E] : Measure E) (closedBall 0 1) :=
      Measure.euclideanHausdorffMeasure_smul₀ (Module.finrank ℝ E) hr.ne' _
    _ = (ENNReal.ofReal r) ^ Module.finrank ℝ E *
        euclideanUnitBallVolume (Module.finrank ℝ E) := by
      rw [euclideanHausdorffMeasure_unit_closedBall]
      change (↑‖r‖₊ : ℝ≥0∞) ^ Module.finrank ℝ E *
        euclideanUnitBallVolume (Module.finrank ℝ E) = _
      have hnorm : (↑‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
        calc
          (↑‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖r‖ := (ofReal_norm r).symm
          _ = ENNReal.ofReal r := by rw [Real.norm_of_nonneg hr.le]
      rw [hnorm]

namespace Measure

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

-- Simon, Chapter 4, formula (3.8), p. 91: the unnormalized mass ratio r^(-n) mu(B_r(x)).
def massRatio (μ : Measure E) (n : ℕ) (x : E) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ n * μ (closedBall x r)

-- Simon, Chapter 4, formula (3.9), p. 91: the normalized density ratio.
def densityRatio (μ : Measure E) (n : ℕ) (x : E) (r : ℝ) : ℝ≥0∞ :=
  massRatio μ n x r / euclideanUnitBallVolume n

-- Simon, Chapter 4, formula (3.9), p. 91: the lower radial density limit.
def lowerDensity (μ : Measure E) (n : ℕ) (x : E) : ℝ≥0∞ :=
  liminf (densityRatio μ n x) (𝓝[>] 0)

-- Simon, Chapter 4, formula (3.9), p. 91: the upper radial density limit.
def upperDensity (μ : Measure E) (n : ℕ) (x : E) : ℝ≥0∞ :=
  limsup (densityRatio μ n x) (𝓝[>] 0)

@[simp]
theorem massRatio_zero (μ : Measure E) (x : E) (r : ℝ) :
    massRatio μ 0 x r = μ (closedBall x r) := by
  simp [massRatio]

section ProperSpace

variable [ProperSpace E] [BorelSpace E]

theorem upperSemicontinuous_measure_closedBall
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (r : ℝ) :
    UpperSemicontinuous fun x => μ (closedBall x r) := by
  rw [upperSemicontinuous_iff]
  intro x a hxa
  let δ : ℕ → ℝ := fun i => 1 / (i + 1 : ℝ)
  let s : ℕ → Set E := fun i => closedBall x (r + δ i)
  have hδ_pos (i : ℕ) : 0 < δ i := by
    dsimp only [δ]
    positivity
  have hδ_zero : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hδ_anti : Antitone δ := by
    intro i j hij
    dsimp only [δ]
    gcongr
  have hs_anti : Antitone s := by
    intro i j hij
    apply closedBall_subset_closedBall
    exact add_le_add_right (hδ_anti hij) r
  have hs_inter : ⋂ i, s i = closedBall x r := by
    ext y
    simp only [mem_iInter, s, mem_closedBall]
    constructor
    · intro hy
      have hlim : Tendsto (fun i => r + δ i) atTop (𝓝 r) := by
        simpa using tendsto_const_nhds.add hδ_zero
      exact ge_of_tendsto' hlim hy
    · intro hy i
      exact hy.trans (le_add_of_nonneg_right (hδ_pos i).le)
  have hmeasure : Tendsto (fun i => μ (s i)) atTop (𝓝 (μ (closedBall x r))) := by
    have h := tendsto_measure_iInter_atTop
      (μ := μ) (s := s)
      (fun _ => measurableSet_closedBall.nullMeasurableSet) hs_anti
      ⟨0, (isCompact_closedBall x (r + δ 0)).measure_ne_top⟩
    change Tendsto (fun i => μ (s i)) atTop (𝓝 (μ (⋂ i, s i))) at h
    rw [hs_inter] at h
    exact h
  obtain ⟨i, hi⟩ := (hmeasure.eventually (Iio_mem_nhds hxa)).exists
  filter_upwards [ball_mem_nhds x (hδ_pos i)] with y hy
  apply (measure_mono ?_).trans_lt hi
  apply closedBall_subset_closedBall'
  rw [mem_ball] at hy
  linarith

theorem upperSemicontinuous_massRatio
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (n : ℕ) {r : ℝ} (hr : 0 < r) :
    UpperSemicontinuous fun x => μ.massRatio n x r := by
  let c : ℝ≥0∞ := (ENNReal.ofReal r)⁻¹ ^ n
  have hc : c ≠ ∞ := by
    exact ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hr))
  have hcomp := (ENNReal.continuous_const_mul hc).comp_upperSemicontinuous
    (upperSemicontinuous_measure_closedBall μ r)
    (monotone_id.const_mul (show 0 ≤ c from bot_le))
  simpa only [massRatio, c, Function.comp_def] using hcomp

theorem upperSemicontinuous_densityRatio
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (n : ℕ) {r : ℝ} (hr : 0 < r) :
    UpperSemicontinuous fun x => μ.densityRatio n x r := by
  have hcomp :=
    (ENNReal.continuous_div_const (euclideanUnitBallVolume n)
      (euclideanUnitBallVolume_ne_zero n)).comp_upperSemicontinuous
      (upperSemicontinuous_massRatio μ n hr)
      (fun _ _ h => ENNReal.div_le_div h le_rfl)
  simpa only [densityRatio, Function.comp_def] using hcomp

end ProperSpace

end Measure

end MeasureTheory
