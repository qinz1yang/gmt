import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.LiminfLimsup

open Filter Metric
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace MeasureTheory

def euclideanUnitBallVolume (n : ℕ) : ℝ≥0∞ :=
  μHE[n] (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

theorem euclideanUnitBallVolume_ne_zero (n : ℕ) : euclideanUnitBallVolume n ≠ 0 := by
  rw [euclideanUnitBallVolume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'

theorem euclideanUnitBallVolume_ne_top (n : ℕ) : euclideanUnitBallVolume n ≠ ∞ := by
  rw [euclideanUnitBallVolume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact measure_closedBall_lt_top.ne

namespace Measure

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

def massRatio (μ : Measure E) (n : ℕ) (x : E) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ n * μ (closedBall x r)

def densityRatio (μ : Measure E) (n : ℕ) (x : E) (r : ℝ) : ℝ≥0∞ :=
  massRatio μ n x r / euclideanUnitBallVolume n

def lowerDensity (μ : Measure E) (n : ℕ) (x : E) : ℝ≥0∞ :=
  liminf (densityRatio μ n x) (𝓝[>] 0)

def upperDensity (μ : Measure E) (n : ℕ) (x : E) : ℝ≥0∞ :=
  limsup (densityRatio μ n x) (𝓝[>] 0)

@[simp]
theorem massRatio_zero (μ : Measure E) (x : E) (r : ℝ) :
    massRatio μ 0 x r = μ (closedBall x r) := by
  simp [massRatio]

end Measure

end MeasureTheory
