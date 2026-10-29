module

public import ASDExplicitGamma.Inverse.BandDensity
public import ASDExplicitGamma.Inverse.StoppedResetDensityBudgets

/-! Exact sums of retained wave-density errors over all heights and layers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Source D4 summand with all-order coefficients. -/
def bandDensityBudget4 (k : ℕ) (γ S : ℝ) (C : ℕ) (j : Fin 2)
    (hk : ℕ × ℕ) : ℝ :=
  (S+1)*∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
    (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
    ((localizationResetAbscissa C hk.1 hk.2:ℝ)^j.val*
      ((3:ℝ)^(4*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
        (3:ℝ)^(-(densityPERate 4 i/2)*
          ((localizationResetAbscissa C hk.1 hk.2:ℝ)+1))))

/-- Closed complete D4 sum, including the first abscissa moment for j=1. -/
def bandDensitySum4 (k : ℕ) (γ S : ℝ) (C : ℕ) (j : Fin 2) : ℝ :=
  (S+1)*∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
    (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
    (if j=0 then densityResetPowerSum (4*γ) (densityPERate 4 i/2) C
      else densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) C)

theorem band_density_budget4_nonneg (k : ℕ) (γ S : ℝ) (hS : 0 ≤ S)
    (C : ℕ) (j : Fin 2) (hk : ℕ × ℕ) :
    0 ≤ bandDensityBudget4 k γ S C j hk := by
  unfold bandDensityBudget4
  positivity

/-- Both infinite indices converge with the source's three distinct rates. -/
theorem band_density_budget4_hasSum (k : ℕ) (γ S : ℝ)
    (hγ : γ ≤ gammaZero) (C : ℕ) (j : Fin 2) :
    HasSum (bandDensityBudget4 k γ S C j) (bandDensitySum4 k γ S C j) := by
  unfold bandDensityBudget4 bandDensitySum4
  fin_cases j
  · simp only [Fin.val_zero, pow_zero, one_mul, ite_true]
    apply HasSum.mul_left
    apply hasSum_sum
    intro i _
    exact (density_reset_power_hasSum (4*γ) (densityPERate 4 i/2)
      (density_rates_decay γ hγ 4 (Or.inr rfl) i).2 C).mul_left _
  · simp only [Fin.val_one, pow_one, show ¬(1:Fin 2)=0 by decide, ite_false]
    apply HasSum.mul_left
    apply hasSum_sum
    intro i _
    exact (density_reset_first_power_hasSum (4*γ) (densityPERate 4 i/2)
      (density_rates_decay γ hγ 4 (Or.inr rfl) i).2 C).mul_left _

/-- Exact equality of the layer's three buffer depths and source reset depths. -/
theorem layer_reset_density_depth (H0 : ℕ) (hH : 38 ≤ H0)
    (hk : ℕ × ℕ) (e : Fin 3) :
    layerDepth (H0+hk.1) (hk.2+1)-40-e.val = resetDensityDepth H0 hk e := by
  unfold layerDepth layerProfile resetDensityDepth
    localizationResetAbscissa localizationProfileDepth
  omega

/-- The square-root envelope retains all three resolution offsets exactly. -/
theorem band_density_sqrt_resolution_sum (k H0 : ℕ) (hk : ℕ × ℕ) :
    (∑ e : Fin 3, Real.sqrt (bandDensityPowerEnvelope 4 k (resetDensityDepth H0 hk e))) ≤
      ∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
        (3:ℝ)^(-densityPERate 4 i*
          ((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)/2) := by
  simp_rw [band_density_envelope_eq]
  apply (Finset.sum_le_sum (fun e _ => localization_sqrt_power_envelope Finset.univ
    (bandDensityCoefficient 4 k) (densityPERate 4)
    (fun i _ => band_density_coefficient_nonneg 4 k i)
    (resetDensityDepth H0 hk e:ℝ))).trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  simp_rw [reset_density_depth_real H0 hk]
  rw [localization_resolution_sqrt_power_sum]
  ring

end
end ASDExplicitGamma.Inverse
