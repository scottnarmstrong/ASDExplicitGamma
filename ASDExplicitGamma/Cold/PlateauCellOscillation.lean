module

public import ASDExplicitGamma.Cold.PlateauOnSquareMoments
public import Homogenization.Geometry.CubeMetric

/-! # The actual depth-four oscillation of the plateau cutoff -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Set
open ASDExplicitGamma.Triadic
open scoped ENNReal NNReal
namespace ASDExplicitGamma.Cold

/-- Sup-norm diameter of an actual triadic cell. -/
theorem square_cell_dist_le {R : TriadicCube 2} {x y : Vec 2}
    (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet R) : dist x y ≤ cubeScaleFactor R := by
  have hx' := Metric.mem_closedBall.mp (cubeSet_subset_closedBall R hx)
  have hy' := Metric.mem_closedBall.mp (cubeSet_subset_closedBall R hy)
  calc
    dist x y ≤ dist x (cubeCenter R) + dist (cubeCenter R) y := dist_triangle _ _ _
    _ ≤ cubeRadius R + cubeRadius R := add_le_add hx' (by rwa [dist_comm] at hy')
    _ = _ := by unfold cubeRadius; ring

/-- The actual plateau oscillates by less than `1/8` on every depth-four cell.
Its sup-norm Lipschitz bound gives a slightly sharper estimate than the source Euclidean bound. -/
theorem plateau_depth_four_oscillation {Q R : TriadicCube 2} {r : ℕ}
    (hR : R ∈ descendantsAtDepth Q r) (hr : r = 4) {x y : Vec 2}
    (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet R) :
    |plateauOnSquare Q x - plateauOnSquare Q y| ≤ (1/8 : ℝ) := by
  have h : |plateauOnSquare Q x - plateauOnSquare Q y| ≤
      ((48/7 : ℝ) * (cubeScaleFactor Q)⁻¹) * dist x y := by
    simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat,
      NNReal.coe_inv, NNReal.coe_mk] using (lipschitzWith_plateauOnSquare Q).dist_le_mul x y
  have hc : ((48/7 : ℝ)*(cubeScaleFactor Q)⁻¹) = 48/(7*cubeScaleFactor Q) := by ring
  have hdist : |plateauOnSquare Q x - plateauOnSquare Q y| ≤
      (48/(7*cubeScaleFactor Q))*dist x y :=
    h.trans_eq (congrArg (fun c : ℝ => c * dist x y) hc)
  have hℓ := cubeScaleFactor_pos' Q
  have hd := mul_le_mul_of_nonneg_left (square_cell_dist_le hx hy)
    (by positivity : 0 ≤ 48/(7*cubeScaleFactor Q))
  have hscale := congrArg (fun c : ℝ => (48/(7*cubeScaleFactor Q))*c)
    (cubeScaleFactor_descendant_eq_div_pow (Q := Q) (R := R) (n := r) hR)
  rw [hr] at hscale
  have hd' := hd.trans_eq hscale
  have hconst : (48/(7*cubeScaleFactor Q))*(cubeScaleFactor Q/(3:ℝ)^(4 : ℕ)) ≤ (1/8 : ℝ) := by
    field_simp [hℓ.ne']
    norm_num
  exact hdist.trans (hd'.trans hconst)

/-- The actual spatial cell average differs from every cutoff value by at most `1/8`. -/
theorem plateau_depth_four_average_le {Q R : TriadicCube 2} {r : ℕ}
    (hR : R ∈ descendantsAtDepth Q r) (hr : r = 4) {x : Vec 2} (hx : x ∈ cubeSet R) :
    cubeAverage R (plateauOnSquare Q) - (1/8 : ℝ) ≤ plateauOnSquare Q x := by
  have hInt : Integrable (plateauOnSquare Q) (normalizedCubeMeasure R) :=
    (MemLp.of_bound (lipschitzWith_plateauOnSquare Q).continuous.aestronglyMeasurable
      (12/7) (Filter.Eventually.of_forall (norm_plateauOnSquare_le Q)) :
      MemLp (plateauOnSquare Q) 1 (normalizedCubeMeasure R)).integrable (by simp)
  have hle : ∫ y, plateauOnSquare Q y ∂normalizedCubeMeasure R ≤ plateauOnSquare Q x + 1/8 := by
    calc
      _ ≤ ∫ _y : Vec 2, (plateauOnSquare Q x + (1/8 : ℝ)) ∂normalizedCubeMeasure R := by
        apply integral_mono_ae (μ := normalizedCubeMeasure R)
          (f := plateauOnSquare Q) (g := fun _ : Vec 2 => plateauOnSquare Q x + 1/8)
          hInt (integrable_const (plateauOnSquare Q x + 1/8))
        have hmem : ∀ᵐ y ∂normalizedCubeMeasure R, y ∈ cubeSet R := by
          unfold normalizedCubeMeasure
          exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cubeSet R)) _
        filter_upwards [hmem] with y hy
        have h := (le_abs_self _).trans (plateau_depth_four_oscillation hR hr hy hx)
        linarith only [h]
      _ = _ := by simp [Measure.real, normalizedCubeMeasure_apply_univ]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  linarith only [hle]

end ASDExplicitGamma.Cold
