module

public import ASDExplicitGamma.Native.GenericSourceMeans
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The scalar source heat inequality integrates to the literal
finite mean profile, retaining the entire phi1 series, including the zero-rate endpoint. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Set
noncomputable section

/-- The entire source function satisfies its exact exponential identity. -/
theorem native_source_phiOne_mul (c : ℝ) :
    c*nativeSourcePhiOne c = Real.exp c-1 := by
  have hs := (Real.summable_pow_div_factorial c).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at hs
  have he : Real.exp c = ∑' n : ℕ, c^n/(n.factorial:ℝ) := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
  unfold nativeSourcePhiOne
  rw [← tsum_mul_left]
  have hterm (n : ℕ) : c*(c^n/((n+1).factorial:ℝ)) = c^(n+1)/((n+1).factorial:ℝ) := by
    rw [pow_succ]
    ring
  simp_rw [hterm]
  linarith only [hs,he]

/-- The zero-rate value is one, with no division-by-zero convention. -/
theorem native_source_phiOne_zero : nativeSourcePhiOne 0 = 1 := by
  unfold nativeSourcePhiOne
  rw [tsum_eq_single 0 (fun n hn => by simp only [zero_pow hn,zero_div])]
  norm_num

end
end ASDExplicitGamma.Native
