module

public import ASDExplicitGamma.Gaussian.SupMeanSeries
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin

/-! Literal dyadic cell centers, parent maps and exact center-to-child distances on a square. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open scoped BigOperators
noncomputable section

/-- The full two-coordinate dyadic grid at level n. -/
abbrev SupMeanDyadicIndex (n : ℕ) := Fin 2 → Fin (2^n)

/-- The unique parent cell index in each coordinate. -/
def supMeanDyadicParent {n : ℕ} (i : SupMeanDyadicIndex (n+1)) : SupMeanDyadicIndex n :=
  fun d => ⟨(i d).val/2, by
    have hh : (i d).val < 2^n*2 := (i d).isLt.trans_eq (pow_succ 2 n)
    omega⟩

/-- Actual centers in the square of side s about c. -/
def supMeanDyadicCenter (c : Fin 2 → ℝ) (s : ℝ) (n : ℕ) (i : SupMeanDyadicIndex n) : Fin 2 → ℝ :=
  fun d => c d-s/2+s*((i d).val+1/2)/(2:ℝ)^n

/-- The closed physical square, with its actual coordinate carrier. -/
def supMeanClosedSquare (c : Fin 2 → ℝ) (s : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∀ d, |x d-c d| ≤ s/2}

/-- The number of level-n cell centers is exactly 4^n. -/
theorem supMean_dyadic_card (n : ℕ) : Fintype.card (SupMeanDyadicIndex n) = 4^n := by
  simp only [SupMeanDyadicIndex, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

/-- The level-zero center is the root center itself. -/
theorem supMean_dyadic_zero_center (c : Fin 2 → ℝ) (s : ℝ) (i : SupMeanDyadicIndex 0) :
    supMeanDyadicCenter c s 0 i = c := by
  funext d
  have hi : (i d).val = 0 := by have hh := (i d).isLt; norm_num at hh; omega
  simp only [supMeanDyadicCenter, hi, Nat.cast_zero, zero_add, pow_zero, div_one]
  ring

/-- Every actual center lies in the closed physical square. -/
theorem supMean_dyadic_center_mem (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (i : SupMeanDyadicIndex n) : supMeanDyadicCenter c s n i ∈ supMeanClosedSquare c s := by
  intro d
  have hpow : 0 < (2:ℝ)^n := by positivity
  have hnat : (i d).val+1 ≤ 2^n := (i d).isLt
  have hcast : ((i d).val:ℝ)+1 ≤ (2:ℝ)^n := by exact_mod_cast hnat
  let t : ℝ := ((i d).val+1/2)/(2:ℝ)^n
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one hpow).mpr (by linarith only [hcast])
  have he : supMeanDyadicCenter c s n i d-c d = s*(t-1/2) := by
    unfold supMeanDyadicCenter t
    ring
  rw [he, abs_mul, abs_of_nonneg hs]
  have ht : |t-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith only [ht0],by linarith only [ht1]⟩
  exact (mul_le_mul_of_nonneg_left ht hs).trans_eq (by ring)

/-- Each coordinate of a center-to-child increment has the exact squared length. -/
theorem supMean_dyadic_parent_coordinate_sq (c : Fin 2 → ℝ) (s : ℝ) (n : ℕ)
    (i : SupMeanDyadicIndex (n+1)) (d : Fin 2) :
    (supMeanDyadicCenter c s (n+1) i d-supMeanDyadicCenter c s n (supMeanDyadicParent i) d)^2 =
      s^2/((2:ℝ)^(n+2))^2 := by
  let m := (i d).val/2
  let r := (i d).val%2
  have hn : (i d).val = 2*m+r := by dsimp only [m,r]; omega
  have hc : ((i d).val:ℝ) = 2*(m:ℝ)+(r:ℝ) := by exact_mod_cast hn
  have hr : r=0 ∨ r=1 := by dsimp only [r]; omega
  have hpow : (2:ℝ)^(n+2) = (2:ℝ)^n*4 := by
    rw [show n+2 = (n+1)+1 by omega, pow_succ, pow_succ]
    ring
  change (c d-s/2+s*(((i d).val:ℝ)+1/2)/(2:ℝ)^(n+1)-
    (c d-s/2+s*((m:ℝ)+1/2)/(2:ℝ)^n))^2 = _
  rw [hc, pow_succ (2:ℝ) n, hpow]
  rcases hr with hr | hr
  · rw [hr]
    norm_num only [Nat.cast_zero, add_zero]
    field_simp [pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0)]
    ring
  · rw [hr]
    norm_num only [Nat.cast_one]
    field_simp [pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0)]
    ring

/-- The actual planar center-to-child Euclidean distance squared. -/
theorem supMean_dyadic_parent_distance_sq (c : Fin 2 → ℝ) (s : ℝ) (n : ℕ)
    (i : SupMeanDyadicIndex (n+1)) :
    (∑ d : Fin 2, (supMeanDyadicCenter c s (n+1) i d-
      supMeanDyadicCenter c s n (supMeanDyadicParent i) d)^2) = 2*s^2/((2:ℝ)^(n+2))^2 := by
  simp only [supMean_dyadic_parent_coordinate_sq, Fin.sum_univ_two]
  ring

end
end ASDExplicitGamma.Gaussian
