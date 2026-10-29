module

public import ASDExplicitGamma.Native.GenericSourceChildBandMeanPointwise
public import ASDExplicitGamma.Inverse.SourceRefinedBudget

/-! The actual source variance/covariance budget with arbitrary positive
norm factors; used before the simultaneous moment is integrated. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Variational
noncomputable section

/-- The refined child's squared bracket coefficient at each shell distance. -/
def nativeSourceChildShellQ (i : ℕ) : ℝ :=
  (pureFluxCovarianceB 1 i)^2+nativeSourceChildShellK i

/-- Positivity of the three actual shifted source shell coefficients. -/
theorem native_source_child_shell_coefficients_nonneg (i : ℕ) :
    0 ≤ nativeSourceChildShellK i ∧ 0 ≤ nativeSourceChildShellQ i ∧ 0 ≤ nativeSourceChildShellMu i := by
  have hr := (pureFlux_covariance_rho_pos 1 i).le
  have hd := (pureFlux_covariance_delta_bounds 1 i).1
  have hk : 0 ≤ nativeSourceChildShellK i := by
    unfold nativeSourceChildShellK lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  exact ⟨hk,add_nonneg (sq_nonneg _) hk,(pureFlux_covariance_mu_lower _ _).1⟩

/-- The finite physical shell costs obey the complete sharp source budget
for any three nonnegative factors; no truncation of covariance tails occurs. -/
theorem native_source_child_band_coefficient_budget
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ)
    (hstate : nativeInductionState M h n) (b d u1 u2 : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) :
    (∑ i ∈ Finset.range height,
      let v := (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2
      v*(39+38*nativeSourceChildShellK i)*d+2*v*nativeSourceChildShellK i*(b*u1)+
        v*(nativeSourceChildShellMu i+38*nativeSourceChildShellQ i)*(b^2*u2)) ≤
      nativeSourceRawShellVarianceCap M.gamma height *
        ((39*(height:ℝ)+38*(65399707/10^9:ℝ))*d+2*(65399707/10^9:ℝ)*b*u1+
          ((259713047/10^9:ℝ)+38*((259713047/10^9:ℝ)+(65399707/10^9:ℝ)))*b^2*u2) := by
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
  have hsums := source_child_covariance_weighted_partial_sums (Finset.range height) v e he hv
  apply source_refined_shell_sum_budget_of_covariance_caps height e b d u1 u2
    (65399707/10^9) (259713047/10^9) ((259713047/10^9)+(65399707/10^9)) v nativeSourceChildShellK
    (fun i => v i*nativeSourceChildShellMu i) nativeSourceChildShellQ _ hb hd hu1 hu2
  · calc
      _ ≤ ∑ _i ∈ Finset.range height, e := Finset.sum_le_sum hv
      _ = (height:ℝ)*e := by simp
  · exact hsums.1
  · exact hsums.2
  · exact source_child_covariance_q_weighted_sum (Finset.range height) v e he hv
      (fun _ _ => by dsimp [v]; positivity)
  · intro i _
    exact le_of_eq (by ring)

end
end ASDExplicitGamma.Native
