module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandDerivativeNorm

/-! Pointwise and averaged oscillation of the actual full fresh band. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model Triadic Inverse Algsuperdiff.Section3
noncomputable section

/-- The physical cube has Pi-norm diameter at most its side length. -/
theorem upper_cell_cube_diameter (Q : TriadicCube 2) {x y : Vec 2}
    (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    ‖y-x‖ ≤ cubeScaleFactor Q := by
  have hx' := cubeSet_subset_closedBall Q hx
  have hy' := cubeSet_subset_closedBall Q hy
  change dist x (cubeCenter Q) ≤ cubeRadius Q at hx'
  change dist y (cubeCenter Q) ≤ cubeRadius Q at hy'
  rw [←dist_eq_norm,cubeScaleFactor_eq_two_mul_cubeRadius]
  have ht := dist_triangle y (cubeCenter Q) x
  rw [dist_comm (cubeCenter Q) x] at ht
  linarith only [ht,hx',hy']

/-- The same full-band envelope controls every pairwise scalar oscillation
on the physical cube, without a triangle over individual shells. -/
theorem upper_cell_band_oscillation
    (Q : TriadicCube 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) {x y : Vec 2} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    |laterScalarBand n (n+(height:ℤ)) weights ω y-
      laterScalarBand n (n+(height:ℤ)) weights ω x| ≤
    upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
      (fun i => weights (upperCellPhysicalBandLabel n height i))
      (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω := by
  let B := ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
    (fun i => weights (upperCellPhysicalBandLabel n height i)) Q3SpatialJet.first
    (cubeCenter Q) (cubeScaleFactor Q) ω‖
  have hc : Convex ℝ (cubeSet Q) := by
    rw [cubeSet_eq_pi_Ico]
    exact convex_pi (fun i _ => convex_Ico _ _)
  have hd := (later_scalar_band_contDiff n (n+(height:ℤ)) weights ω).differentiable
    (by norm_num : (2:WithTop ℕ∞)≠0)
  have hh := hc.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hd x) (fun x hx => upper_cell_band_fderiv_norm_le Q n height weights ω hx) hx hy
  have hdiam := mul_le_mul_of_nonneg_left (upper_cell_cube_diameter Q hx hy)
    (show 0≤B by dsimp [B]; positivity)
  change |laterScalarBand n (n+(height:ℤ)) weights ω y-
    laterScalarBand n (n+(height:ℤ)) weights ω x| ≤ _
  have hh' : |laterScalarBand n (n+(height:ℤ)) weights ω y-
      laterScalarBand n (n+(height:ℤ)) weights ω x| ≤ B*cubeScaleFactor Q :=
    (show |laterScalarBand n (n+(height:ℤ)) weights ω y-
      laterScalarBand n (n+(height:ℤ)) weights ω x| ≤ B*‖y-x‖ by
        simpa only [Real.norm_eq_abs] using hh).trans hdiam
  apply hh'.trans
  change B*cubeScaleFactor Q ≤ cubeScaleFactor Q*B+_
  rw [mul_comm B]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (norm_nonneg _))

/-- A continuous function with bounded displacement from a fixed value has
an average with the same bound, on the literal normalized cube measure. -/
theorem upper_cell_mean_displacement
    (R : TriadicCube 2) (f : Vec 2 → ℝ) (hf : Continuous f) (c C : ℝ)
    (hbound : ∀ x ∈ cubeSet R, |f x-c| ≤ C) : |cubeAverage R f-c| ≤ C := by
  have hi := (continuous_memLp_top_cube R (normalizedCubeMeasure R)
    (normalized_cube_support R) f hf).integrable (by norm_num)
  have he : cubeAverage R f-c = ∫ x, (f x-c) ∂normalizedCubeMeasure R := by
    rw [integral_sub hi (integrable_const c),cubeAverage_eq_integral_normalizedCubeMeasure]
    simp [Measure.real]
  rw [he,←Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (f := fun x => f x-c) (C := C)
    ((normalized_cube_support R).mono (fun x hx => by
      simpa only [Real.norm_eq_abs] using hbound x hx))
  simpa [Measure.real] using hb

/-- Parent and descendant gauges differ by at most twice the same actual
full-band envelope, uniformly over all contained cubes. -/
theorem upper_cell_band_mean_difference
    (Q R : TriadicCube 2) (hR : cubeSet R ⊆ cubeSet Q)
    (n : ℤ) (height : ℕ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    |cubeAverage R (laterScalarBand n (n+(height:ℤ)) weights ω)-
      cubeAverage Q (laterScalarBand n (n+(height:ℤ)) weights ω)| ≤
    2*upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
      (fun i => weights (upperCellPhysicalBandLabel n height i))
      (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω := by
  let f := laterScalarBand n (n+(height:ℤ)) weights ω
  let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
    (fun i => weights (upperCellPhysicalBandLabel n height i))
    (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
  have hc : cubeCenter Q ∈ cubeSet Q := by
    apply openCubeSet_subset_cubeSet Q
    rw [←ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q)
  have hf := (later_scalar_band_contDiff n (n+(height:ℤ)) weights ω).continuous
  have hroot : |cubeAverage Q f-f (cubeCenter Q)| ≤ F :=
    upper_cell_mean_displacement Q f hf _ _
      (fun x hx => upper_cell_band_oscillation Q n height weights ω hc hx)
  have hchild : |cubeAverage R f-f (cubeCenter Q)| ≤ F :=
    upper_cell_mean_displacement R f hf _ _
      (fun x hx => upper_cell_band_oscillation Q n height weights ω hc (hR hx))
  have hh := abs_sub_le (cubeAverage R f) (f (cubeCenter Q)) (cubeAverage Q f)
  rw [abs_sub_comm (f (cubeCenter Q))] at hh
  exact hh.trans (by linarith only [hroot,hchild])

end
end ASDExplicitGamma.Scalar
