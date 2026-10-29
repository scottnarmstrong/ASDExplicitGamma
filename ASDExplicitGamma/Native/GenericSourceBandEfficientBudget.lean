module

public import ASDExplicitGamma.Native.GenericSourceShellBudget
public import ASDExplicitGamma.Inverse.SourceStrongVarianceClock
public import ASDExplicitGamma.Inverse.SourceRefinedBudget

/-! The actual source variance/covariance budget with arbitrary positive
norm factors; used before the simultaneous moment is integrated. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse
noncomputable section

/-- The finite physical shell costs obey the complete sharp source budget
for any three nonnegative factors; no truncation of covariance tails occurs. -/
theorem native_source_band_efficient_coefficient_budget
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ)
    (hstate : nativeInductionState M h n) (b d u1 u2 : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) :
    (∑ i ∈ Finset.range height,
      let v := (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2
      v*(39+38*nativeSourceShellK i)*d+2*v*nativeSourceShellK i*(b*u1)+
        v*(nativeSourceShellMu i+38*nativeSourceShellQ i)*(b^2*u2)) ≤
      ((4/5:ℝ)*nativeSourceRawShellVarianceCap M.gamma height) *
        ((39*(height:ℝ)+38*(521/1000:ℝ))*d+2*(521/1000:ℝ)*b*u1+
          ((1975/1000:ℝ)+38*(1565/1000:ℝ))*b^2*u2) := by
  let e := ((4/5:ℝ)*nativeSourceRawShellVarianceCap M.gamma height)
  let v := fun i : ℕ => (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/
    (Annealed.sigmaBar M n:ℝ)^2
  have hg := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hv (i : ℕ) (hi : i ∈ Finset.range height) : v i ≤ e := by
    have hh := source_native_strong_shell_variance_clock M h n (n+((i+1:ℕ):ℤ)) hstate
    have hiR : ((i+1:ℕ):ℝ) ≤ (height:ℝ) := by exact_mod_cast (by have hh := Finset.mem_range.mp hi; omega : i+1 ≤ height)
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (mul_le_mul_of_nonneg_left hiR (show (0:ℝ)≤2*M.gamma by positivity))
    have hh' : v i ≤ (18/5:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*((i+1:ℕ):ℝ)) := by
      simpa only [Int.cast_add,Int.cast_natCast,add_sub_cancel_left] using hh
    have hfinal := hh'.trans (mul_le_mul_of_nonneg_left hp
      (show (0:ℝ)≤(18/5:ℝ)*M.gamma by positivity))
    have hexp : (3:ℝ)^(2*(height:ℝ)*M.gamma)=(3:ℝ)^(2*M.gamma*(height:ℝ)) := by congr 1; ring
    have heq : e=(18/5:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*(height:ℝ)) := by
      dsimp [e,nativeSourceRawShellVarianceCap]
      rw [hexp]
      ring
    exact hfinal.trans_eq heq.symm
  have hsums := source_covariance_weighted_partial_sums (Finset.range height) v e he hv
  apply source_refined_shell_sum_budget height e b d u1 u2 v nativeSourceShellK
    (fun i => v i*nativeSourceShellMu i) nativeSourceShellQ _ hb hd hu1 hu2
  · calc
      _ ≤ ∑ _i ∈ Finset.range height, e := Finset.sum_le_sum hv
      _ = (height:ℝ)*e := by simp
  · exact hsums.1
  · exact hsums.2.1
  · exact hsums.2.2
  · intro i _
    exact le_of_eq (by ring)

end
end ASDExplicitGamma.Native
