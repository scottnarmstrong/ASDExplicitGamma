module

public import ASDExplicitGamma.Inverse.AssemblyPositiveLayer
public import ASDExplicitGamma.Inverse.RootMatrixBudget
public import ASDExplicitGamma.Inverse.StoppedSeriesLp

/-! Complete positive matrix series on all deterministic heights. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual matrix part of the positive inverse error. -/
def assemblyMatrixTerm (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  rootAssemblySensitivity*rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)*
    resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau ω

/-- A summable deterministic envelope for each actual matrix term. -/
def assemblyMatrixBudgetTerm (γ p : ℝ) (H0 : ℕ) (hk : ℕ × ℕ) : ℝ :=
  (rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau)*
    ((3:ℝ)^(2*γ*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
      (3:ℝ)^(-((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)))

/-- Closed complete matrix budget; no random height is substituted into it. -/
def assemblyMatrixBudget (γ p : ℝ) (H0 : ℕ) : ℝ :=
  (rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau)*
    densityResetPowerSum (2*γ) 1 (H0-38)

theorem assembly_matrix_budget_hasSum (γ p : ℝ) (hγ : γ ≤ gammaZero) (H0 : ℕ) :
    HasSum (assemblyMatrixBudgetTerm γ p H0) (assemblyMatrixBudget γ p H0) := by
  have hγ' : γ ≤ 17/50000 := hγ
  have hh := (density_reset_power_hasSum (2*γ) 1 (by linarith only [hγ'])
    (H0-38)).mul_left
      (rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau)
  convert hh using 1
  · funext hk
    simp only [assemblyMatrixBudgetTerm,neg_one_mul]
  · rfl

/-- Actual clipped matrices control every deterministic matrix term. -/
theorem assembly_matrix_term_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 38 ≤ H0)
    (hk : ℕ × ℕ) (p : ℝ) (hp : 1 ≤ p) :
    Measurable (assemblyMatrixTerm M Q H0 hk) ∧
      eLpNorm (assemblyMatrixTerm M Q H0 hk) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (assemblyMatrixBudgetTerm M.gamma p H0 hk) := by
  let w := rootAssemblySensitivity*rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)
  have hw : 0 ≤ w := mul_nonneg root_assembly_sensitivity_pos.le
    (root_assembly_clock_pos _ _ _).le
  have hm := (reset_root_matrix_positive_error_measurable M Q (H0+hk.1) (hk.2+1)
    resetAllOrderTau).const_mul w
  refine ⟨hm, ?_⟩
  have he : assemblyMatrixTerm M Q H0 hk =
      w • resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau := rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hw]
  have hb := reset_root_matrix_positive_error_Lp M h hM Q (H0+hk.1) (hk.2+1)
    (by omega) resetAllOrderTau (by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]) p hp
  apply (mul_le_mul_of_nonneg_left hb (zero_le : (0:ℝ≥0∞) ≤ _)).trans
  rw [← ENNReal.ofReal_mul hw]
  apply ENNReal.ofReal_le_ofReal
  have hv : Real.sqrt (bankLayerWeight hk.2) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    simpa only [layerWeight_hasSum.tsum_eq] using
      layerWeight_hasSum.summable.le_tsum hk.2 (fun _ _ => bankLayerWeight_nonneg _)
  have hd : layerDepth (H0+hk.1) (hk.2+1) =
      hk.2+1+whitneyProfile (H0+hk.1) (hk.2+1) := by
    unfold layerDepth layerProfile whitneyProfile
    omega
  rw [hd]
  have hfactor := root_matrix_depth_factor H0 hk.1 hk.2 hH0
  have hscalar : w*(256*Real.sqrt p*(1+resetAllOrderTau+
      Real.sqrt (resetAllOrderTau*(resetAllOrderTau+2)))*Real.sqrt (bankLayerWeight hk.2)*
      (1/3:ℝ)^(hk.2+1+whitneyProfile (H0+hk.1) (hk.2+1))*(3:ℝ)^40) =
      assemblyMatrixBudgetTerm M.gamma p H0 hk*Real.sqrt (bankLayerWeight hk.2) := by
    dsimp only [w,assemblyMatrixBudgetTerm,rootResponseEnvelope]
    rw [assembly_clock_eq_reset _ _ hH0]
    calc
      _ = (rootAssemblySensitivity*256*Real.sqrt p*
          (1+resetAllOrderTau+Real.sqrt (resetAllOrderTau*(resetAllOrderTau+2)))*
          (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
          Real.sqrt (bankLayerWeight hk.2))*
          ((1/3:ℝ)^(hk.2+1+whitneyProfile (H0+hk.1) (hk.2+1))*(3:ℝ)^40) := by ring
      _ = _ := by rw [hfactor]; ring
  simp only [Nat.add_sub_cancel] at *
  rw [hscalar]
  apply mul_le_of_le_one_right _ hv
  have hs0 := root_assembly_sensitivity_pos.le
  unfold assemblyMatrixBudgetTerm rootResponseEnvelope
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  positivity

/-- The complete positive matrix series is absolutely summable a.e. and has
an all-real-order norm bound before selection of the root height. -/
theorem assembly_matrix_series_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 38 ≤ H0) (p : ℝ) (hp : 1 ≤ p) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun hk => ‖assemblyMatrixTerm M Q H0 hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, assemblyMatrixTerm M Q H0 hk ω)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (assemblyMatrixBudget M.gamma p H0) := by
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hs0 := root_assembly_sensitivity_pos.le
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp) (assemblyMatrixTerm M Q H0)
    (fun hk => (assembly_matrix_term_Lp M h hM Q H0 hH0 hk p hp).1)
    (assemblyMatrixBudgetTerm M.gamma p H0)
    (fun hk => by unfold assemblyMatrixBudgetTerm rootResponseEnvelope; positivity)
    _ (assembly_matrix_budget_hasSum M.gamma p hγ H0)
    (fun hk => (assembly_matrix_term_Lp M h hM Q H0 hH0 hk p hp).2)

end
end ASDExplicitGamma.Inverse
