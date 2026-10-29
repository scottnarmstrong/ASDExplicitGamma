module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicSquare
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Every point of the closed square is approximated by its literal dyadic cell centers. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
noncomputable section

/-- Cell index, clamped only at the upper endpoint of the unit interval. -/
def supMeanDyadicUnitIndex (n : ℕ) (t : ℝ) : Fin (2^n) :=
  ⟨min ⌊(2:ℝ)^n*t⌋₊ (2^n-1), lt_of_le_of_lt (min_le_right _ _)
    (Nat.sub_lt (by positivity) (by decide : 0 < 1))⟩

/-- The dyadic center is within half a cell of every point of the closed unit interval. -/
theorem supMean_dyadic_unit_index_error (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |((supMeanDyadicUnitIndex n t).val:ℝ)+1/2-(2:ℝ)^n*t| ≤ 1/2 := by
  let N : ℕ := 2^n
  have hN : 0 < N := by dsimp only [N]; positivity
  have hNr : (N:ℝ) = (2:ℝ)^n := by dsimp only [N]; norm_cast
  let f := ⌊(2:ℝ)^n*t⌋₊
  have hflo : (f:ℝ) ≤ (2:ℝ)^n*t := Nat.floor_le (by positivity)
  have hfhi : (2:ℝ)^n*t < (f:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hf : f < N
  · have hmin : min f (N-1) = f := min_eq_left (by omega)
    change |(min f (N-1):ℕ)+1/2-(2:ℝ)^n*t| ≤ 1/2
    rw [hmin]
    exact abs_le.mpr ⟨by linarith only [hfhi],by linarith only [hflo]⟩
  · have hmin : min f (N-1) = N-1 := min_eq_right (by omega)
    have hfcast : (N:ℝ) ≤ f := by exact_mod_cast (le_of_not_gt hf)
    have hprod : (2:ℝ)^n ≤ (2:ℝ)^n*t := by linarith only [hfcast,hflo,hNr]
    have ht : t = 1 := le_antisymm ht1
      ((mul_le_mul_iff_left₀ (by positivity : (0:ℝ) < (2:ℝ)^n)).mp (by simpa only [mul_one, one_mul, mul_comm] using! hprod))
    have hsub : ((N-1:ℕ):ℝ) = (N:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    change |(min f (N-1):ℕ)+1/2-(2:ℝ)^n*t| ≤ 1/2
    rw [hmin,hsub,ht,← hNr]
    have he : (N:ℝ)-1+1/2-(N:ℝ) = -(1/2:ℝ) := by ring
    simpa only [mul_one, he] using (show |-(1/2:ℝ)| ≤ 1/2 by norm_num)

/-- The actual approximation index of a point of a physical square. -/
def supMeanDyadicApproxIndex (c : Fin 2 → ℝ) (s : ℝ) (n : ℕ) (x : Fin 2 → ℝ) : SupMeanDyadicIndex n :=
  fun d => supMeanDyadicUnitIndex n ((x d-c d+s/2)/s)

/-- Every coordinate of the physical square approximation has the exact half-cell error. -/
theorem supMean_dyadic_approx_coordinate_error (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s)
    (n : ℕ) (x : Fin 2 → ℝ) (hx : x ∈ supMeanClosedSquare c s) (d : Fin 2) :
    |supMeanDyadicCenter c s n (supMeanDyadicApproxIndex c s n x) d-x d| ≤ s/(2:ℝ)^(n+1) := by
  have hd := abs_le.mp (hx d)
  let t := (x d-c d+s/2)/s
  have ht0 : 0 ≤ t := div_nonneg (by linarith only [hd.1]) hs.le
  have ht1 : t ≤ 1 := (div_le_one hs).mpr (by linarith only [hd.2])
  have he := supMean_dyadic_unit_index_error n t ht0 ht1
  have hN : 0 < (2:ℝ)^n := by positivity
  have hpoint : supMeanDyadicCenter c s n (supMeanDyadicApproxIndex c s n x) d-x d =
      (s/(2:ℝ)^n)*(((supMeanDyadicUnitIndex n t).val:ℝ)+1/2-(2:ℝ)^n*t) := by
    dsimp only [supMeanDyadicCenter, supMeanDyadicApproxIndex, t]
    field_simp [hs.ne', hN.ne']
    ring
  rw [hpoint, abs_mul, abs_of_pos (div_pos hs hN)]
  exact (mul_le_mul_of_nonneg_left he (div_pos hs hN).le).trans_eq (by rw [pow_succ]; ring)

end
end ASDExplicitGamma.Gaussian
