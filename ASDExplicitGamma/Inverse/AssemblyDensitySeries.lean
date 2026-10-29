module

public import ASDExplicitGamma.Inverse.AssemblyDensity
public import ASDExplicitGamma.Inverse.AssemblyPositiveLayer
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! Complete positive density series at the actual geometric labels. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The actual density part of the positive inverse error. -/
def assemblyDensityTerm (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (rootAssemblySensitivity*rootResponseEnvelope (6*resetAllOrderTau))*
    resetDensityTerm2 M Q H0 resetAllOrderTau (waveGateEta .allOrder)
      (allOrderDensity:ℝ) 1324 (planarGradientCharge 40) hk ω

/-- Retained band envelope for one height and layer, with all resolutions. -/
def assemblyDensityBudgetTerm (γ : ℝ) (k H0 : ℕ) (hk : ℕ × ℕ) : ℝ :=
  (rootAssemblySensitivity*rootResponseEnvelope (6*resetAllOrderTau)*
    (planarGradientCharge 40+1))*
    ∑ i : Fin 3, bandDensityCoefficient 2 k i*
      (1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i))*
      ((3:ℝ)^(2*γ*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
        (3:ℝ)^(-densityPERate 2 i*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)))

/-- Closed complete density budget over all heights and layers. -/
def assemblyDensityBudget (γ : ℝ) (k H0 : ℕ) : ℝ :=
  (rootAssemblySensitivity*rootResponseEnvelope (6*resetAllOrderTau)*
    (planarGradientCharge 40+1))*
    ∑ i : Fin 3, bandDensityCoefficient 2 k i*
      (1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i))*
      densityResetPowerSum (2*γ) (densityPERate 2 i) (H0-38)

theorem assembly_density_budget_term_nonneg (γ : ℝ) (k H0 : ℕ) (hk : ℕ × ℕ) :
    0 ≤ assemblyDensityBudgetTerm γ k H0 hk := by
  have hs := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  unfold assemblyDensityBudgetTerm
  apply mul_nonneg
  · unfold rootResponseEnvelope planarGradientCharge
    positivity
  · exact Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (band_density_coefficient_nonneg 2 k i) (by positivity)) (by positivity)

theorem assembly_density_budget_hasSum (γ : ℝ) (hγ : γ ≤ gammaZero) (k H0 : ℕ) :
    HasSum (assemblyDensityBudgetTerm γ k H0) (assemblyDensityBudget γ k H0) := by
  unfold assemblyDensityBudgetTerm assemblyDensityBudget
  apply HasSum.mul_left
  apply hasSum_sum
  intro i _
  exact (density_reset_power_hasSum (2*γ) (densityPERate 2 i)
    (density_rates_decay γ hγ 2 (Or.inl rfl) i).1 (H0-38)).mul_left _

/-- The band envelope sums the three actual geometric density resolutions. -/
theorem assembly_density_resolution_sum (k H0 : ℕ) (hk : ℕ × ℕ) :
    (∑ e : Fin 3, bandDensityPowerEnvelope 2 k (resetDensityDepth H0 hk e)) =
      ∑ i : Fin 3, bandDensityCoefficient 2 k i*
        (1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i))*
        (3:ℝ)^(-densityPERate 2 i*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)) := by
  simp_rw [band_density_envelope_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  simp_rw [reset_density_depth_real H0 hk]
  rw [localization_resolution_power_sum]
  ring

/-- Every actual geometric density summand obeys its complete band envelope. -/
theorem assembly_density_term_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p) (H0 : ℕ)
    (hH0 : heightEntrance (orderBand p)+5 ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (hk : ℕ × ℕ) :
    Measurable (assemblyDensityTerm M Q H0 hk) ∧
      eLpNorm (assemblyDensityTerm M Q H0 hk) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (assemblyDensityBudgetTerm M.gamma (orderBand p) H0 hk) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := fun e : Fin 3 => resetDensityExcess M Q H0 resetAllOrderTau
    (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e
  let w := rootAssemblySensitivity*rootResponseEnvelope (6*resetAllOrderTau)*
    (planarGradientCharge 40+1)*
      (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))
  have hs0 := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hw : 0 ≤ w := by dsimp only [w]; unfold rootResponseEnvelope planarGradientCharge; positivity
  have hY (e : Fin 3) : Measurable (Y e) :=
    reset_density_excess_measurable M Q H0 _ _ _ _ _ hk e
  have he : assemblyDensityTerm M Q H0 hk = w • (fun ω => ∑ e, Y e ω) := by
    funext ω
    dsimp only [assemblyDensityTerm,resetDensityTerm2,w,Pi.smul_apply,smul_eq_mul,Y]
    ring
  rw [he]
  refine ⟨(Finset.measurable_sum _ (fun e _ => hY e)).const_mul w, ?_⟩
  have hC (e : Fin 3) : 0 ≤ bandDensityPowerEnvelope 2 (orderBand p)
      (resetDensityDepth H0 hk e) := by
    rw [band_density_envelope_eq]
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (band_density_coefficient_nonneg 2 _ i) (by positivity)
  have hb := finite_density_sum_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) Y (fun _ => 1)
    (fun e => bandDensityPowerEnvelope 2 (orderBand p) (resetDensityDepth H0 hk e))
    (fun _ => by norm_num) hC
    (fun e => assembly_geometric_density_band_Lp M h hM hγ Q p hp H0 hH0 hpast
      2 (Or.inl rfl) hk e)
  simp only [one_mul] at hb
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hw]
  apply (mul_le_mul_of_nonneg_left hb (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul hw,assembly_density_resolution_sum]
  congr 1
  dsimp only [w,assemblyDensityBudgetTerm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The density error is absolutely summable a.e. on the actual law, with
no assumed error moment or independence premise. -/
theorem assembly_density_series_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p) (H0 : ℕ)
    (hH0 : heightEntrance (orderBand p)+5 ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun hk => ‖assemblyDensityTerm M Q H0 hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, assemblyDensityTerm M Q H0 hk ω)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (assemblyDensityBudget M.gamma (orderBand p) H0) := by
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (assemblyDensityTerm M Q H0)
    (fun hk => (assembly_density_term_Lp M h hM hγ Q p hp H0 hH0 hpast hk).1)
    (assemblyDensityBudgetTerm M.gamma (orderBand p) H0)
    (assembly_density_budget_term_nonneg M.gamma (orderBand p) H0)
    _ (assembly_density_budget_hasSum M.gamma hγ (orderBand p) H0)
    (fun hk => (assembly_density_term_Lp M h hM hγ Q p hp H0 hH0 hpast hk).2)

end
end ASDExplicitGamma.Inverse
