module

public import ASDExplicitGamma.Inverse.StoppedDensityResetPowers
public import ASDExplicitGamma.Inverse.WeightedLocalizationRetainedPowers

/-! Exact complete D2 and D4 density series with all three resolution offsets. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The exact D_{2,0} expression after summing both infinite indices. -/
def densityD2 (q p T γ S : ℝ) (C : ℕ) : ℝ :=
  (S+1)*∑ i : Fin 3, densityPECoefficient q 2 p T i *
    (1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i))*
    densityResetPowerSum (2*γ) (densityPERate 2 i) C

/-- Exact D_{4,0}, with the square root applied to each retained coefficient. -/
def densityD40 (q p T γ S : ℝ) (C : ℕ) : ℝ :=
  (S+1)*∑ i : Fin 3, Real.sqrt (densityPECoefficient q 4 p T i) *
    (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
    densityResetPowerSum (4*γ) (densityPERate 4 i/2) C

/-- Exact D_{4,1}, retaining the first abscissa moment. -/
def densityD41 (q p T γ S : ℝ) (C : ℕ) : ℝ :=
  (S+1)*∑ i : Fin 3, Real.sqrt (densityPECoefficient q 4 p T i) *
    (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
    densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) C

/-- Full source D2 series with all three resolutions; no layer-weight envelope
or finite height scan replaces the complete source sums. -/
theorem density_D2_hasSum (q p T γ S : ℝ) (hγ : γ ≤ gammaZero) (C : ℕ) :
    HasSum (fun hk : ℕ × ℕ => (S+1)*∑ i : Fin 3,
      densityPECoefficient q 2 p T i *
      (1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i))*
      ((3:ℝ)^(2*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
       (3:ℝ)^(-densityPERate 2 i*((localizationResetAbscissa C hk.1 hk.2:ℝ)+1))))
      (densityD2 q p T γ S C) := by
  apply HasSum.mul_left
  apply hasSum_sum
  intro i _
  exact (density_reset_power_hasSum (2*γ) (densityPERate 2 i)
    (density_rates_decay γ hγ 2 (Or.inl rfl) i).1 C).mul_left _

/-- The entire D_{4,0} wave-density series converges to its exact expression. -/
theorem density_D40_hasSum (q p T γ S : ℝ) (hγ : γ ≤ gammaZero) (C : ℕ) :
    HasSum (fun hk : ℕ × ℕ => (S+1)*∑ i : Fin 3,
      Real.sqrt (densityPECoefficient q 4 p T i) *
      (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
      ((3:ℝ)^(4*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
       (3:ℝ)^(-(densityPERate 4 i/2)*((localizationResetAbscissa C hk.1 hk.2:ℝ)+1))))
      (densityD40 q p T γ S C) := by
  apply HasSum.mul_left
  apply hasSum_sum
  intro i _
  exact (density_reset_power_hasSum (4*γ) (densityPERate 4 i/2)
    (density_rates_decay γ hγ 4 (Or.inr rfl) i).2 C).mul_left _

/-- The entire D_{4,1} wave-density series converges with the literal x factor. -/
theorem density_D41_hasSum (q p T γ S : ℝ) (hγ : γ ≤ gammaZero) (C : ℕ) :
    HasSum (fun hk : ℕ × ℕ => (S+1)*∑ i : Fin 3,
      Real.sqrt (densityPECoefficient q 4 p T i) *
      (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
      ((localizationResetAbscissa C hk.1 hk.2:ℝ)*
       ((3:ℝ)^(4*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
        (3:ℝ)^(-(densityPERate 4 i/2)*((localizationResetAbscissa C hk.1 hk.2:ℝ)+1)))))
      (densityD41 q p T γ S C) := by
  apply HasSum.mul_left
  apply hasSum_sum
  intro i _
  exact (density_reset_first_power_hasSum (4*γ) (densityPERate 4 i/2)
    (density_rates_decay γ hγ 4 (Or.inr rfl) i).2 C).mul_left _

end
end ASDExplicitGamma.Inverse
