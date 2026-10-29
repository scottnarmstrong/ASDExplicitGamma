module

public import ASDExplicitGamma.Inverse.StoppedDensitySeries
public import ASDExplicitGamma.Inverse.StoppedDensityResolution

/-! The exact summable per-height/layer density budgets appearing in the reset. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Literal per-height/layer summand of D2, with all source resolution offsets. -/
def resetDensityBudget2 (q p T γ S : ℝ) (C : ℕ) (hk : ℕ × ℕ) : ℝ :=
  (S+1)*∑ i : Fin 3, densityPECoefficient q 2 p T i *
    (1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i))*
    ((3:ℝ)^(2*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
      (3:ℝ)^(-densityPERate 2 i*((localizationResetAbscissa C hk.1 hk.2:ℝ)+1)))

/-- Literal per-height/layer summand of D4, with first-moment choice j=0,1. -/
def resetDensityBudget4 (q p T γ S : ℝ) (C : ℕ) (j : Fin 2) (hk : ℕ × ℕ) : ℝ :=
  (S+1)*∑ i : Fin 3, Real.sqrt (densityPECoefficient q 4 p T i) *
    (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))*
    ((localizationResetAbscissa C hk.1 hk.2:ℝ)^j.val*
      ((3:ℝ)^(4*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
       (3:ℝ)^(-(densityPERate 4 i/2)*((localizationResetAbscissa C hk.1 hk.2:ℝ)+1))))

theorem reset_density_budget2_nonneg (q p T γ S : ℝ) (hp : 0 ≤ p) (hS : 0 ≤ S)
    (C : ℕ) (hk : ℕ × ℕ) : 0 ≤ resetDensityBudget2 q p T γ S C hk := by
  apply mul_nonneg (by linarith only [hS])
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (density_PE_coefficient_nonneg q 2 p T hp i) (by positivity)) (by positivity)

theorem reset_density_budget4_nonneg (q p T γ S : ℝ) (hS : 0 ≤ S)
    (C : ℕ) (j : Fin 2) (hk : ℕ × ℕ) : 0 ≤ resetDensityBudget4 q p T γ S C j hk := by
  unfold resetDensityBudget4
  positivity

/-- Complete D2 series, as a deterministic norm envelope. -/
theorem reset_density_budget2_hasSum (q p T γ S : ℝ) (hg : γ ≤ gammaZero) (C : ℕ) :
    HasSum (resetDensityBudget2 q p T γ S C) (densityD2 q p T γ S C) :=
  density_D2_hasSum q p T γ S hg C

/-- Complete D4 series for both first-moment choices. -/
theorem reset_density_budget4_hasSum (q p T γ S : ℝ) (hg : γ ≤ gammaZero)
    (C : ℕ) (j : Fin 2) :
    HasSum (resetDensityBudget4 q p T γ S C j)
      (if j=0 then densityD40 q p T γ S C else densityD41 q p T γ S C) := by
  unfold resetDensityBudget4
  fin_cases j
  · simpa only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,one_mul,ite_true,show ¬(1:Fin 2)=0 by decide,ite_false] using!
      density_D40_hasSum q p T γ S hg C
  · simpa only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,one_mul,ite_true,show ¬(1:Fin 2)=0 by decide,ite_false] using!
      density_D41_hasSum q p T γ S hg C

end
end ASDExplicitGamma.Inverse
