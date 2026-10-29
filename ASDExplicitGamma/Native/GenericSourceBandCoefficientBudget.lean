module

public import ASDExplicitGamma.Native.GenericSourceShellBudget
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
theorem native_source_band_coefficient_budget
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ)
    (hstate : nativeInductionState M h n) (b d u1 u2 : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) :
    (∑ i ∈ Finset.range height,
      let v := (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2
      v*(39+38*nativeSourceShellK i)*d+2*v*nativeSourceShellK i*(b*u1)+
        v*(nativeSourceShellMu i+38*nativeSourceShellQ i)*(b^2*u2)) ≤
      nativeSourceRawShellVarianceCap M.gamma height *
        ((39*(height:ℝ)+38*(521/1000:ℝ))*d+2*(521/1000:ℝ)*b*u1+
          ((1975/1000:ℝ)+38*(1565/1000:ℝ))*b^2*u2) := by
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let v := fun i : ℕ => (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/
    (Annealed.sigmaBar M n:ℝ)^2
  have hg := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have heq : nativeSourceShellClock M.gamma height=e := by
    dsimp [e,nativeSourceShellClock,nativeSourceRawShellVarianceCap]
    congr 2
    ring
  have hv (i : ℕ) (hi : i ∈ Finset.range height) : v i ≤ e := by
    rw [←heq]
    exact native_source_shell_variance_le_clock M h n height (i+1) hstate
      (by have hh := Finset.mem_range.mp hi; omega)
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
