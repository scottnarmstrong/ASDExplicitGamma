module

public import ASDExplicitGamma.Inverse.AssemblyMatrixSeries
public import ASDExplicitGamma.Inverse.AssemblyDensitySeries

/-! Actual positive error moments before selecting a root height. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

theorem assembly_matrix_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ assemblyMatrixTerm M Q H0 hk ω :=
  mul_nonneg (mul_nonneg root_assembly_sensitivity_pos.le
    (root_assembly_clock_pos _ _ _).le) (le_max_left _ _)

theorem assembly_density_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ assemblyDensityTerm M Q H0 hk ω := by
  have hs := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  unfold assemblyDensityTerm resetDensityTerm2
  apply mul_nonneg
  · unfold rootResponseEnvelope
    positivity
  · apply mul_nonneg
    · unfold planarGradientCharge
      positivity
    · exact Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- Extended nonnegative error terms equal their actual matrix and density
parts, without defining an error by subtraction of norms. -/
theorem assembly_error_term_ofReal (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 38 ≤ H0) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (assemblyMatrixTerm M Q H0 hk ω+assemblyDensityTerm M Q H0 hk ω) =
      ENNReal.ofReal rootAssemblySensitivity * assemblyInverseErrorLayer M Q H0 hk ω := by
  let Y := fun e : Fin 3 => resetDensityExcess M Q H0 resetAllOrderTau
    (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e ω
  have hY (e : Fin 3) : 0 ≤ Y e := le_max_right _ _
  have hs := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hc : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau)*(planarGradientCharge 40+1) := by
    unfold rootResponseEnvelope planarGradientCharge
    positivity
  have hm : 0 ≤ resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau ω := le_max_left _ _
  have he : assemblyMatrixTerm M Q H0 hk ω+assemblyDensityTerm M Q H0 hk ω =
      rootAssemblySensitivity*(rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)*
        (resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau ω+
          (rootResponseEnvelope (6*resetAllOrderTau)*(planarGradientCharge 40+1))*∑ e, Y e)) := by
    unfold assemblyMatrixTerm assemblyDensityTerm resetDensityTerm2
    rw [assembly_clock_eq_reset _ _ hH0]
    dsimp only [Y]
    ring
  rw [he,ENNReal.ofReal_mul hs,ENNReal.ofReal_mul (root_assembly_clock_pos _ _ _).le,
    ENNReal.ofReal_add hm (mul_nonneg hc (Finset.sum_nonneg fun e _ => hY e)),
    ENNReal.ofReal_mul hc,ENNReal.ofReal_sum_of_nonneg (fun e _ => hY e)]
  rfl

/-- The complete extended error equals its convergent real positive series. -/
theorem assembly_inverse_error_eq_parts (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 38 ≤ H0) (ω : Cutoff.CutoffSample 2)
    (hm : Summable (fun hk => assemblyMatrixTerm M Q H0 hk ω))
    (hd : Summable (fun hk => assemblyDensityTerm M Q H0 hk ω)) :
    assemblyInverseError M Q H0 ω = ENNReal.ofReal
      ((∑' hk, assemblyMatrixTerm M Q H0 hk ω)+(∑' hk, assemblyDensityTerm M Q H0 hk ω)) := by
  rw [← hm.tsum_add hd,ENNReal.ofReal_tsum_of_nonneg
    (fun hk => add_nonneg (assembly_matrix_term_nonneg M Q H0 hk ω)
      (assembly_density_term_nonneg M Q H0 hk ω)) (hm.add hd)]
  simp only [assembly_error_term_ofReal M Q H0 hH0,ENNReal.tsum_mul_left,
    assemblyInverseError]

/-- The literal positive error has an all-real-order norm bound. Only
the source model and protected native past are hypotheses. -/
theorem assembly_inverse_error_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p) (H0 : ℕ)
    (hH0 : heightEntrance (orderBand p)+5 ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n) :
    eLpNorm (assemblyInverseError M Q H0) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        (assemblyMatrixBudget M.gamma p H0+assemblyDensityBudget M.gamma (orderBand p) H0) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun ω => ∑' hk, assemblyMatrixTerm M Q H0 hk ω
  let D := fun ω => ∑' hk, assemblyDensityTerm M Q H0 hk ω
  have h38 : 38 ≤ H0 := by unfold heightEntrance at hH0; omega
  have hmat := assembly_matrix_series_Lp M h hM hγ Q H0 h38 p (by linarith only [hp])
  have hden := assembly_density_series_Lp M h hM hγ Q p hp H0 hH0 hpast
  have heq : assemblyInverseError M Q H0 =ᵐ[μ] ENNReal.ofReal ∘ (fun ω => F ω+D ω) := by
    filter_upwards [hmat.1,hden.1] with ω hm hd
    exact assembly_inverse_error_eq_parts M Q H0 h38 ω (Summable.of_norm hm) (Summable.of_norm hd)
  have hn (ω : Cutoff.CutoffSample 2) : 0 ≤ F ω+D ω :=
    add_nonneg (tsum_nonneg fun hk => assembly_matrix_term_nonneg M Q H0 hk ω)
      (tsum_nonneg fun hk => assembly_density_term_nonneg M Q H0 hk ω)
  rw [eLpNorm_congr_ae heq,eLpNorm_ofReal _ (Filter.Eventually.of_forall hn)]
  apply (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))).trans
  apply (add_le_add hmat.2 hden.2).trans
  have hs := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hm0 : 0 ≤ assemblyMatrixBudget M.gamma p H0 := by
    rw [← (assembly_matrix_budget_hasSum M.gamma p hγ H0).tsum_eq]
    apply tsum_nonneg
    intro hk
    unfold assemblyMatrixBudgetTerm rootResponseEnvelope
    positivity
  have hd0 : 0 ≤ assemblyDensityBudget M.gamma (orderBand p) H0 := by
    rw [← (assembly_density_budget_hasSum M.gamma hγ (orderBand p) H0).tsum_eq]
    exact tsum_nonneg (assembly_density_budget_term_nonneg M.gamma (orderBand p) H0)
  exact (ENNReal.ofReal_add hm0 hd0).symm.le

end
end ASDExplicitGamma.Inverse
