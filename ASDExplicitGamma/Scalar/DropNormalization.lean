module

public import ASDExplicitGamma.Scalar.OldHessianTrialFinal

/-! NORMALIZATION CHECK for SC-ONE-SHELL-RECIPROCAL-DROP: the one-shell remainder variable
`v_m = (3^{2γ} - 1) B_m / σ̄_m²` equals `(amp / σ̄_m)²`, the `v` used by the flat, defect and
combine nodes, and equals `(B_{m+1} - B_m)/σ̄_m²`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3

theorem shellVarianceSum_succ (h γ : ℝ) (m : ℤ) :
    shellVarianceSum h γ (m + 1) = (3 : ℝ) ^ (2 * γ) * shellVarianceSum h γ m := by
  unfold shellVarianceSum
  have hx : (3 : ℝ) ^ (2 * γ * (((m + 1 : ℤ)) : ℝ)) =
      (3 : ℝ) ^ (2 * γ * (m : ℝ)) * (3 : ℝ) ^ (2 * γ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [hx]
  ring

/-- The drop's remainder variable is the shell amplitude ratio squared. -/
theorem drop_v_eq_amp_sq (M : ABKModel 2) (h : ℝ) (m : ℤ) :
    ((3 : ℝ) ^ (2 * M.gamma) - 1) * shellVarianceSum h M.gamma m /
        (Annealed.sigmaBar M m : ℝ) ^ 2 =
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 := by
  rw [div_pow, ← old_hessian_shell_variance_increment M h m,
    shellVarianceSum_succ]
  ring

end ASDExplicitGamma.Scalar
