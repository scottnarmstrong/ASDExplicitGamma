module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicApproximation
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compact square carriers and convergence of their actual dyadic-center approximations. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Filter
open scoped Topology
noncomputable section

/-- The physical square is the literal product interval. -/
theorem supMean_closed_square_eq_Icc (c : Fin 2 → ℝ) (s : ℝ) :
    supMeanClosedSquare c s = Set.Icc (fun d => c d-s/2) (fun d => c d+s/2) := by
  ext x
  constructor
  · intro hx
    constructor
    · intro d
      have hd := (abs_le.mp (hx d)).1
      linarith only [hd]
    · intro d
      have hd := (abs_le.mp (hx d)).2
      linarith only [hd]
  · intro hx d
    exact abs_le.mpr ⟨by linarith only [hx.1 d],by linarith only [hx.2 d]⟩

/-- Compactness concerns the actual closed physical square. -/
theorem supMean_closed_square_isCompact (c : Fin 2 → ℝ) (s : ℝ) :
    IsCompact (supMeanClosedSquare c s) := by
  rw [supMean_closed_square_eq_Icc]
  exact isCompact_Icc

/-- The compact continuous-map norm on the square is available without any
extra geometric compactness premise. -/
instance supMeanClosedSquareCompact (c : Fin 2 → ℝ) (s : ℝ) :
    CompactSpace (supMeanClosedSquare c s) :=
  isCompact_iff_compactSpace.mp (supMean_closed_square_isCompact c s)

/-- The root center belongs to every square of nonnegative side. -/
theorem supMean_center_mem_closed_square (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    c ∈ supMeanClosedSquare c s := by
  intro d
  simpa only [sub_self, abs_zero] using div_nonneg hs (by norm_num : (0:ℝ) ≤ 2)

/-- The full vector approximation has the exact half-cell sup-norm bound. -/
theorem supMean_dyadic_approx_norm_error (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s)
    (n : ℕ) (x : Fin 2 → ℝ) (hx : x ∈ supMeanClosedSquare c s) :
    ‖supMeanDyadicCenter c s n (supMeanDyadicApproxIndex c s n x)-x‖ ≤ s/(2:ℝ)^(n+1) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ s/(2:ℝ)^(n+1))).mpr
  intro d
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    supMean_dyadic_approx_coordinate_error c s hs n x hx d

/-- Every point of the actual closed square is the limit of its dyadic cell centers. -/
theorem supMean_dyadic_approx_tendsto (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s)
    (x : Fin 2 → ℝ) (hx : x ∈ supMeanClosedSquare c s) :
    Tendsto (fun n => supMeanDyadicCenter c s n (supMeanDyadicApproxIndex c s n x)) atTop (𝓝 x) := by
  have he (n : ℕ) : s/(2:ℝ)^(n+1) = (s/2)*(1/2:ℝ)^n := by
    simp only [div_pow, one_pow, pow_succ]
    ring
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh : Tendsto (fun n : ℕ => s/(2:ℝ)^(n+1)) atTop (𝓝 0) := by
    simpa only [he, mul_zero] using tendsto_const_nhds.mul hp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => supMean_dyadic_approx_norm_error c s hs n x hx) hh

end
end ASDExplicitGamma.Gaussian
