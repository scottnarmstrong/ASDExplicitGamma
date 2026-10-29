module

public import ASDExplicitGamma.Inverse.FullResponseParameterEndpoint
public import ASDExplicitGamma.Inverse.WeightedLocalizationMismatchNumerics

/-! The actual three D4 coefficients consume their certified radicals and offset payment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The actual full-row eighth rare mean agrees with the literal source value. -/
theorem full_response_m8_endpoint :
    densityMomentBudget (rootQ .full) 8 1232=(invFullM8:ℝ) := by
  norm_num [densityMomentBudget,rootQ,rareMomentPolynomial,invFullQ,invFullM8]

/-- The fourth-power radical check bounds the square root of the variance coefficient. -/
theorem full_response_sqrt_variance_le (x R : ℝ) (hR : 0 ≤ R) (h4 : 16*x ≤ R^4) :
    Real.sqrt (4*Real.sqrt x) ≤ R := by
  have hs : Real.sqrt x ≤ R^2/4 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith only [h4]⟩
  exact (Real.sqrt_le_iff).mpr ⟨hR,by nlinarith only [hs]⟩

/-- Generic real consumption of the three literal coefficient certificates.
The third offset is 13; it is never replaced by the first two offsets. -/
theorem full_response_D4_coefficient_caps (p V D : ℝ)
    (hV : 0 ≤ V) (hV4 : 16*p*63^2*(invFullM8:ℝ) ≤ V^4)
    (hD : 0 ≤ D) (hD2 : 4*p*63^2*12^4 ≤ D^2)
    (hlocal : (13:ℝ)^2*localizationMismatchCoefficient 4 p ≤ 9^2) :
    Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 0) ≤ V ∧
      Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 1) ≤ D ∧
        13*Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 2) ≤ 9 := by
  constructor
  · simp only [densityPECoefficient,ite_true]
    rw [show 2*4=8 by decide,full_response_m8_endpoint]
    apply full_response_sqrt_variance_le _ V hV
    nlinarith only [hV4]
  constructor
  · simpa [densityPECoefficient] using (Real.sqrt_le_iff).mpr ⟨hD,hD2⟩
  · have hh : Real.sqrt (localizationMismatchCoefficient 4 p) ≤ 9/13 :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith only [hlocal]⟩
    simp only [densityPECoefficient,show ¬(2:Fin 3)=0 by decide,ite_false,
      show ¬(2:Fin 3)=1 by decide]
    nlinarith only [hh]

/-- Literal order-64 D4 radical and corrected-offset payments. -/
theorem full_response_D4_coefficients64 :
    Real.sqrt (densityPECoefficient (rootQ .full) 4 64 1232 0) ≤ (invFull64Vroot:ℝ) ∧
      Real.sqrt (densityPECoefficient (rootQ .full) 4 64 1232 1) ≤ (invFull64Droot:ℝ) ∧
        13*Real.sqrt (densityPECoefficient (rootQ .full) 4 64 1232 2) ≤ 9 := by
  apply full_response_D4_coefficient_caps
  · exact_mod_cast invFull64_radicals.2.2.2.2.1.le
  · exact_mod_cast invFull64_radicals.2.2.2.2.2.le
  · exact_mod_cast invFull64_radicals.2.2.1.le
  · exact_mod_cast invFull64_radicals.2.2.2.1.le
  · exact localization_mismatch_offset_payments.1.le

/-- Literal order-128 D4 radical and corrected-offset payments. -/
theorem full_response_D4_coefficients128 :
    Real.sqrt (densityPECoefficient (rootQ .full) 4 128 1232 0) ≤ (invFull128Vroot:ℝ) ∧
      Real.sqrt (densityPECoefficient (rootQ .full) 4 128 1232 1) ≤ (invFull128Droot:ℝ) ∧
        13*Real.sqrt (densityPECoefficient (rootQ .full) 4 128 1232 2) ≤ 9 := by
  apply full_response_D4_coefficient_caps
  · exact_mod_cast invFull128_radicals.2.2.2.2.1.le
  · exact_mod_cast invFull128_radicals.2.2.2.2.2.le
  · exact_mod_cast invFull128_radicals.2.2.1.le
  · exact_mod_cast invFull128_radicals.2.2.2.1.le
  · exact localization_mismatch_offset_payments.2.le

end
end ASDExplicitGamma.Inverse
