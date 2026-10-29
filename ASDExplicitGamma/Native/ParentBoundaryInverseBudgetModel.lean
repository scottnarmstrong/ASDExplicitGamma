module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBudget

/-! Actual model coefficients fit the rational inverse-return allocation
on the whole smaller-gamma ray. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Each actual physical shell variance is paid by the proportional
rational endpoint clock at the terminal finite height. -/
theorem parent_boundary_model_shell_variance_budget
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (height s : ℕ) (hh : height≤16) (hs : s≤height)
    (hstate : nativeInductionState M h n) :
    (q3ModelAmplitude M h (n+(s:ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2≤
      theta M*(parentBoundaryVarianceBudget height:ℝ) := by
  have hv := native_source_shell_variance_le_clock M h n height s hstate hs
  have heq : nativeSourceShellClock M.gamma height=nativeSourceRawShellVarianceCap M.gamma height := by
    unfold nativeSourceShellClock nativeSourceRawShellVarianceCap
    congr 2
    ring
  rw [heq] at hv
  have he := native_source_true_variance_le_generic M.gamma height M.shellPrefix.gamma_pos.le hg (by omega)
  have hd := native_source_generic_variance_cap_degree M.gamma (theta M) height
    M.shellPrefix.gamma_pos.le hg rfl (by omega)
  have hc : nativeSourceGenericVarianceCap (17/50000) height=
      (parentBoundaryVarianceBudget height:ℝ) := by
    simp [nativeSourceGenericVarianceCap,nativeSourceE,parentBoundaryVarianceBudget]
  exact hv.trans (he.trans (hd.trans_eq (congrArg (fun x : ℝ => theta M*x) hc)))

/-- The actual full band variance has its proportional finite-height cap. -/
theorem parent_boundary_model_band_variance_budget
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (height : ℕ) (hh : height≤16) (hstate : nativeInductionState M h n) :
    parentBoundaryBandVariance M h n height≤
      theta M*((height:ℝ)*(parentBoundaryVarianceBudget height:ℝ)) := by
  calc
    _ ≤ ∑ i : Fin height,theta M*(parentBoundaryVarianceBudget height:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [div_pow] using parent_boundary_model_shell_variance_budget
        M h hg n height (i.val+1) hh (by omega) hstate
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- The actual inverse drift clock is paid proportionally by the rational
global-bank coefficient, with no assumed variance or covariance estimate. -/
theorem parent_boundary_model_inverse_kappa_budget
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (height : ℕ) (hh : height≤16) (hstate : nativeInductionState M h n) :
    mainKappa (parentBoundaryBandInverseClock M h n height)≤
      theta M*(parentBoundaryInverseKBudget height:ℝ) := by
  have hv := parent_boundary_model_band_variance_budget M h hg n height hh hstate
  have hv0 : 0≤parentBoundaryBandVariance M h n height := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr := (parent_boundary_inverse_band_clock_le_variance M h n height).trans
    (mul_le_mul_of_nonneg_right parent_boundary_inverse_unit_root_cap hv0)
  have hs := mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ)≤232/125)
  have hk := mul_le_mul_of_nonneg_right (hr.trans hs) (sq_nonneg mainBeta)
  have he : (parentBoundaryInverseKBudget height:ℝ)=
      (232/125:ℝ)*(14103/10000)^2*(height:ℝ)*(parentBoundaryVarianceBudget height:ℝ) := by
    simp [parentBoundaryInverseKBudget]
  rw [he]
  dsimp only [mainKappa]
  apply hk.trans_eq
  unfold mainBeta
  ring

/-- The actual complete two-load Dirichlet energy keeps every shell's
own geometric decay inside the rational endpoint allocation. -/
theorem parent_boundary_model_inverse_y_budget
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (height : ℕ) (hh : height≤16) (hstate : nativeInductionState M h n) :
    parentBoundaryBandDirichletEnergy M h n height≤
      theta M*(parentBoundaryInverseYBudget height:ℝ) := by
  have hi (i : Fin height) : parentBoundaryDirichletEnergy (originCube 2 n)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))≤
      (26/15:ℝ)*(1/9:ℝ)^(i.val+1)*(theta M*(parentBoundaryVarianceBudget height:ℝ)) := by
    have hc := parent_boundary_model_dirichlet_clock n (i.val+1)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [div_pow] using parent_boundary_model_shell_variance_budget M h hg n height
      (i.val+1) hh (by omega) hstate
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have he : (parentBoundaryInverseYBudget height:ℝ)=
      (26/15:ℝ)*(parentBoundaryVarianceBudget height:ℝ)*
        ∑ i∈Finset.range height,(1/9:ℝ)^(i+1) := by
    simp [parentBoundaryInverseYBudget]
  apply hs.trans_eq
  rw [he,←Fin.sum_univ_eq_sum_range (fun i : ℕ => (1/9:ℝ)^(i+1)),Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end ASDExplicitGamma.Native
