# GMT

A Lean 4 and Mathlib library for Euclidean geometric measure theory. The current prototype develops
general varifolds, first variation, stationarity, and the stationary monotonicity and density theory.
The intended scope also includes area and coarea, rectifiability, BV and finite perimeter, currents,
and regularity theory.

The project uses Lean and Mathlib version `v4.33.1`.

## Build

```bash
lake exe cache get
lake build GMT
```

## Simon correspondence

The table below records the public declarations that currently correspond directly to Leon Simon's
*Introduction to Geometric Measure Theory* (2014 revision). Source links open the Lean statements.
The Chapter 4 results are proved for general varifolds in arbitrary finite-dimensional real inner
product spaces, so Simon's rectifiable Euclidean statements follow as special cases once the
rectifiable representation layer is added.

### Chapter 4: Rectifiable n-varifolds

| Simon | Lean statements |
| --- | --- |
| Section 3, radial test field and formula (3.2), pp. 89-90 | [`radialVectorField`](GMT/Analysis/Radial.lean#L9), [`squaredRadiusRadialVectorField`](GMT/Analysis/Radial.lean#L14), [`Grassmannian.perpendicularProjection`](GMT/Linear/Grassmannian/Defs.lean#L46), [`Grassmannian.tangentialDivergence_radialVectorField`](GMT/Varifold/FirstVariation.lean#L20), [`Grassmannian.tangentialDivergence_radialVectorField_eq_perpendicularProjection`](GMT/Varifold/FirstVariation.lean#L29), [`Grassmannian.radialTilt`](GMT/Varifold/Monotonicity.lean#L19) |
| Stationary radial identity (3.3), p. 90 | [`Varifold.IsStationaryOn.integral_squaredRadiusRadial_eq_zero`](GMT/Varifold/Monotonicity.lean#L57), [`Varifold.IsStationaryOn.integral_squaredRadiusRadial_perpendicular_eq_zero`](GMT/Varifold/Monotonicity.lean#L101) |
| Exact stationary monotonicity identity (3.6), p. 90 | [`Varifold.IsStationaryOn.monotonicity`](GMT/Varifold/Monotonicity.lean#L1135), [`Varifold.IsStationaryOn.monotonicity_sub`](GMT/Varifold/Monotonicity.lean#L1153) |
| Mass ratio and normalized density notation (3.8)-(3.9), p. 91 | [`MeasureTheory.euclideanUnitBallVolume`](GMT/Measure/Density.lean#L14), [`MeasureTheory.Measure.massRatio`](GMT/Measure/Density.lean#L88), [`MeasureTheory.Measure.densityRatio`](GMT/Measure/Density.lean#L92), [`MeasureTheory.Measure.lowerDensity`](GMT/Measure/Density.lean#L96), [`MeasureTheory.Measure.upperDensity`](GMT/Measure/Density.lean#L100) |
| Monotonicity and existence and finiteness of density (3.8)-(3.9), p. 91 | [`Varifold.IsStationaryOn.massRatio_monotoneOn`](GMT/Varifold/Monotonicity.lean#L1169), [`Varifold.IsStationaryOn.densityRatio_monotoneOn`](GMT/Varifold/Monotonicity.lean#L1180), [`Varifold.IsStationaryOn.tendsto_densityRatio`](GMT/Varifold/Monotonicity.lean#L1189), [`Varifold.IsStationaryOn.lowerDensity_ne_top`](GMT/Varifold/Monotonicity.lean#L1206), [`Varifold.IsStationaryOn.lowerDensity_eq_upperDensity`](GMT/Varifold/Monotonicity.lean#L1229), [`Varifold.IsStationaryOn.upperDensity_ne_top`](GMT/Varifold/Monotonicity.lean#L1237) |
| Density-excess identity (3.10), p. 91 | [`Varifold.IsStationaryOn.density_excess`](GMT/Varifold/Monotonicity.lean#L1245), [`Varifold.IsStationaryOn.density_excess_sub`](GMT/Varifold/Monotonicity.lean#L1346) |
| Upper semicontinuity of stationary density (3.11), p. 91 | [`Varifold.IsStationaryOn.upperSemicontinuousOn_lowerDensity`](GMT/Varifold/Monotonicity.lean#L1358) |
| Euclidean and flat-plane normalization checks | [`MeasureTheory.euclideanHausdorffMeasure_closedBall`](GMT/Measure/Density.lean#L44), [`Varifold.weightMeasure_ofPlane`](GMT/Varifold/Plane.lean#L84), [`Varifold.weightMeasure_ofPlane_closedBall`](GMT/Varifold/Plane.lean#L97), [`Varifold.massRatio_ofPlane`](GMT/Varifold/Plane.lean#L115), [`Varifold.densityRatio_ofPlane`](GMT/Varifold/Plane.lean#L123), [`Varifold.lowerDensity_ofPlane`](GMT/Varifold/Plane.lean#L195), [`Varifold.upperDensity_ofPlane`](GMT/Varifold/Plane.lean#L208) |

### Chapter 8: Theory of general varifolds

| Simon | Lean statements |
| --- | --- |
| Section 1, Grassmannian and orthogonal projection, p. 205 | [`Grassmannian`](GMT/Linear/Grassmannian/Defs.lean#L8), [`Grassmannian.projection`](GMT/Linear/Grassmannian/Defs.lean#L31), [`Grassmannian.subspace`](GMT/Linear/Grassmannian/Defs.lean#L43), [`Grassmannian.perpendicularProjection`](GMT/Linear/Grassmannian/Defs.lean#L46) |
| Section 1, general varifold, weight, and mass, pp. 205-206 | [`Varifold`](GMT/Varifold/Defs.lean#L9), [`Varifold.weightMeasure`](GMT/Varifold/Defs.lean#L67), [`Varifold.mass`](GMT/Varifold/Defs.lean#L70), [`Varifold.massOn`](GMT/Varifold/Defs.lean#L73) |
| Section 1, restriction, p. 206 | [`Varifold.restrict`](GMT/Varifold/Basic.lean#L45), [`Varifold.toMeasure_restrict`](GMT/Varifold/Basic.lean#L49), [`Varifold.weightMeasure_restrict`](GMT/Varifold/Basic.lean#L52) |
| Section 1, multiplicity-one plane, p. 206 | [`Varifold.ofPlane`](GMT/Varifold/Plane.lean#L48), [`Varifold.toMeasure_ofPlane`](GMT/Varifold/Plane.lean#L61), [`Varifold.isStationaryOn_ofPlane`](GMT/Varifold/Plane.lean#L131), [`Varifold.ofPlane_ne_zero`](GMT/Varifold/Plane.lean#L215) |
| Section 2, tangential divergence and first variation (2.3), pp. 208-209 | [`Grassmannian.tangentialDivergence`](GMT/Varifold/FirstVariation.lean#L16), [`Varifold.firstVariation`](GMT/Varifold/FirstVariation.lean#L161), [`Varifold.firstVariation_apply`](GMT/Varifold/FirstVariation.lean#L176), [`Varifold.firstVariation_apply_restrict`](GMT/Varifold/FirstVariation.lean#L183) |
| Section 2, stationarity (2.4), p. 209 | [`Varifold.IsStationaryOn`](GMT/Varifold/FirstVariation.lean#L224), [`Varifold.IsStationaryOn.integral_tangentialDivergence_eq_zero`](GMT/Varifold/FirstVariation.lean#L249), [`Varifold.IsStationaryOn.integral_tangentialDivergence_eq_zero_restrict`](GMT/Varifold/FirstVariation.lean#L257) |
| Section 3, stationary monotonicity and density-excess identity (3.4), pp. 210-211 | [`Varifold.IsStationaryOn.monotonicity`](GMT/Varifold/Monotonicity.lean#L1135), [`Varifold.IsStationaryOn.density_excess`](GMT/Varifold/Monotonicity.lean#L1245), [`Varifold.IsStationaryOn.density_excess_sub`](GMT/Varifold/Monotonicity.lean#L1346) |

Chapters 1-3 and 5-7 do not yet have chapter-level public formalizations in this repository. Imported
Mathlib results are not counted as completed GMT coverage, and the normalization lemmas listed above
do not by themselves constitute a formalization of Simon's preliminary measure theory.
