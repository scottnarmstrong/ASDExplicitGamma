module

public import ASDExplicitGamma.Inverse.StoppedDensityBudgets
public import ASDExplicitGamma.Inverse.StoppedDensityLinearPower
public import Mathlib.Tactic.FinCases

/-! The three exact retained PE powers of the actual weighted density bound. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The three literal PE coefficients, including both localization and
expectation errors in the third coefficient. -/
def densityPECoefficient (q : ℝ) (m : ℕ) (p T : ℝ) (i : Fin 3) : ℝ :=
  if i=0 then 4*Real.sqrt (p*63^2*densityMomentBudget q (2*m) T)
  else if i=1 then 4*p*63^2*12^m else localizationMismatchCoefficient m p

/-- The source retained rates nu=(5/6,(10-m)/6,2). -/
def densityPERate (m : ℕ) (i : Fin 3) : ℝ :=
  if i=0 then 5/6 else if i=1 then (10-(m:ℝ))/6 else 2

/-- The complete source PE sum, before any later height/layer summation. -/
def densityPEEnvelope (q : ℝ) (m : ℕ) (p T : ℝ) (R : ℕ) : ℝ :=
  ∑ i : Fin 3, densityPECoefficient q m p T i*(3:ℝ)^(-densityPERate m i*(R:ℝ))

theorem density_PE_envelope_eq (q : ℝ) (m : ℕ) (p T : ℝ) (R : ℕ) :
    densityPEEnvelope q m p T R =
      4*Real.sqrt (p*63^2*densityMomentBudget q (2*m) T)*(3:ℝ)^(-(5/6:ℝ)*(R:ℝ))+
      4*p*63^2*12^m*(3:ℝ)^(-((10-(m:ℝ))/6)*(R:ℝ))+
      localizationMismatchCoefficient m p*(3:ℝ)^(-2*(R:ℝ)) := by
  norm_num [densityPEEnvelope,densityPECoefficient,densityPERate,Fin.sum_univ_succ]
  ring

/-- The literal N=3^(floor(R/6)+1) budget obeys all three retained source
powers for every later depth, retaining the true volume in its baseline. -/
theorem full_density_budget_le_PE (q : ℝ) (hq : 0 ≤ q) (m : ℕ)
    (p T : ℝ) (hp : 0 < p) (hp256 : p ≤ 256) (hT : 0 ≤ T)
    (R : ℕ) (hR : 60 ≤ R) (v : ℝ) (hv1 : v ≤ 1) :
    fullDensityBudget q m p T (R/6+1) ((1/9:ℝ)^R) v ≤ densityPEEnvelope q m p T R := by
  have hβ := density_moment_budget_nonneg q hq (2*m) T hT
  have hvar := density_variance_power_bound p (densityMomentBudget q (2*m) T) v hp.le hβ R
  have hvs : Real.sqrt v ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by simpa only [one_pow] using hv1⟩
  have hvar' : 4*Real.sqrt (p*21^2*densityMomentBudget q (2*m) T*(3:ℝ)^(2*(R/6+1))*(1/9:ℝ)^R*v) ≤
      4*Real.sqrt (p*63^2*densityMomentBudget q (2*m) T)*(3:ℝ)^(-(5/6:ℝ)*(R:ℝ)) := by
    apply hvar.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvs (show 0 ≤ 4*Real.sqrt (p*63^2*densityMomentBudget q (2*m) T) by positivity))
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)
  have hlin := density_linear_power_bound p hp.le m R
  have herr : 2*localizationErrorBudget m p (R/6+1) ≤
      localizationMismatchCoefficient m p*(3:ℝ)^(-2*(R:ℝ)) := by
    have hh := localization_retained_mismatch_bound m p hp hp256 R hR
    simpa only [localizationErrorBudget,localizationCutoffRadius,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using! hh
  have hC := localization_error_budget_nonneg m p hp.le (R/6+1)
  have hvol := mul_le_mul_of_nonneg_left hv1 (show 0 ≤ 2*localizationErrorBudget m p (R/6+1) by positivity)
  have herr' := hvol.trans (by simpa only [mul_one] using herr)
  rw [density_PE_envelope_eq]
  unfold fullDensityBudget localizedDensityBudget
  exact add_le_add (add_le_add hvar' hlin) herr'

end
end ASDExplicitGamma.Inverse
