module

public import ASDExplicitGamma.Inverse.StoppedResetDensityFields
public import ASDExplicitGamma.Inverse.WeightedLocalizationRetainedPowers

/-! Exact source resolution offsets for the actual reset density envelopes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

theorem density_PE_coefficient_nonneg (q : ℝ) (m : ℕ) (p T : ℝ) (hp : 0 ≤ p) (i : Fin 3) :
    0 ≤ densityPECoefficient q m p T i := by
  unfold densityPECoefficient
  split
  · positivity
  · split
    · positivity
    · unfold localizationMismatchCoefficient
      positivity

theorem density_PE_envelope_nonneg (q : ℝ) (m : ℕ) (p T : ℝ) (hp : 0 ≤ p) (R : ℕ) :
    0 ≤ densityPEEnvelope q m p T R := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (density_PE_coefficient_nonneg q m p T hp i)
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)

/-- Summing the three genuine density resolutions gives the exact source
factor 1+3^nu+3^(2nu), with no worst-resolution substitution. -/
theorem reset_density_PE_resolution_sum (q : ℝ) (m : ℕ) (p T : ℝ)
    (H0 : ℕ) (hk : ℕ × ℕ) :
    (∑ e : Fin 3, densityPEEnvelope q m p T (resetDensityDepth H0 hk e)) =
      ∑ i : Fin 3, densityPECoefficient q m p T i *
        (1+(3:ℝ)^(densityPERate m i)+(3:ℝ)^(2*densityPERate m i))*
        (3:ℝ)^(-densityPERate m i*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)) := by
  unfold densityPEEnvelope
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  simp_rw [reset_density_depth_real H0 hk]
  rw [localization_resolution_power_sum]
  ring

/-- Square-root density errors retain half of each individual PE rate and
exactly the three source half-rate resolution offsets. -/
theorem reset_density_PE_sqrt_resolution_sum (q : ℝ) (m : ℕ) (p T : ℝ) (hp : 0 ≤ p)
    (H0 : ℕ) (hk : ℕ × ℕ) :
    (∑ e : Fin 3, Real.sqrt (densityPEEnvelope q m p T (resetDensityDepth H0 hk e))) ≤
      ∑ i : Fin 3, Real.sqrt (densityPECoefficient q m p T i) *
        (1+(3:ℝ)^(densityPERate m i/2)+(3:ℝ)^(densityPERate m i))*
        (3:ℝ)^(-densityPERate m i*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)/2) := by
  apply (Finset.sum_le_sum (fun e _ => localization_sqrt_power_envelope Finset.univ
    (densityPECoefficient q m p T) (densityPERate m)
    (fun i _ => density_PE_coefficient_nonneg q m p T hp i)
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
