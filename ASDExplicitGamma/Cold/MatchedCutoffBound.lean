module

public import ASDExplicitGamma.Cold.SquareMatchedCutoff

/-! # Integrable domination of the actual cutoff-weighted matched energies -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace ASDExplicitGamma.Cold

/-- The exact cutoff height bounds the actual weighted four-load energy by its genuine trace. -/
theorem square_matched_cutoff_bounds (Q R : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a) (v : SquareMatchedOptimizers R a) :
    0 ≤ volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x*squareMatchedDensity R v x) ∧
      volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x*squareMatchedDensity R v x) ≤
        (24/7:ℝ)*traceDefect (openCubeSet R) a 1 := by
  have hn (x : Vec 2) (hx : x ∈ openCubeSet R) : 0 ≤ plateauOnSquare Q x*squareMatchedDensity R v x :=
    mul_nonneg (plateauOnSquare_nonneg Q x) (squareMatchedDensity_nonneg R hEll v hx)
  refine ⟨volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R) hn,?_⟩
  have hh := square_volumeAverage_mono_ae R (integrable_plateau_squareMatchedDensity Q R hEll v)
    ((integrable_squareMatchedDensity R hEll v).const_mul (12/7:ℝ))
    (by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (norm_plateauOnSquare_le Q x))
        (squareMatchedDensity_nonneg R hEll v hx))
  have he : volumeAverage (openCubeSet R) (fun x => (12/7:ℝ)*squareMatchedDensity R v x) =
      (12/7:ℝ)*volumeAverage (openCubeSet R) (squareMatchedDensity R v) := by
    unfold volumeAverage
    rw [integral_const_mul]
    ring
  rw [he,squareMatchedDensity_average R hEll v] at hh
  linarith only [hh]

end ASDExplicitGamma.Cold
