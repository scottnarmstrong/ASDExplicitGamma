module

public import ASDExplicitGamma.Scalar.ResolventCombine
public import ASDExplicitGamma.Numerics.Scalar.LowerR

/-! R-successor of the certified C-sharp coefficient and charge facts consumed by the
reciprocal drop. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open ASDExplicitGamma.Numerics.Scalar
open ASDExplicitGamma.Numerics.Mirror

noncomputable section

noncomputable def certifiedQuarticSharpR : ℝ :=
  evalReal scalarRealEnv quarticSharpRExpr

noncomputable def certifiedQuarticChargeR : ℝ :=
  evalReal scalarRealEnv quarticChargeRExpr

noncomputable def scalarReciprocalGainR : ℝ := evalReal scalarRealEnv lowerGainRExpr

theorem certified_quartic_sharp_formula_R :
    certifiedQuarticSharpR =
      evalReal scalarRealEnv quarticFlatExpr +
        (141 / 50 : ℝ) * Real.sqrt
          (evalReal scalarRealEnv quarticFlatExpr *
            evalReal scalarRealEnv quarticDefectRExpr) +
        (44 / 25 : ℝ) * evalReal scalarRealEnv quarticDefectRExpr := by
  simp [certifiedQuarticSharpR, quarticSharpRExpr, evalReal, sc]
  ring

theorem certified_quartic_charge_factorization_R :
    certifiedQuarticChargeR = certifiedQuarticSharpR *
      (((11 / 5 : ℝ) * (17 / 50000)) /
        (1 - (11 / 5 : ℝ) * (17 / 50000))) := by
  simp [certifiedQuarticChargeR, certifiedQuarticSharpR,
    quarticChargeRExpr, quarticSharpRExpr, evalReal, sc]
  field_simp
  ring

/-- Analogue of `drop_gain_eq` (DropOneShell). -/
theorem drop_gain_eq_R : scalarReciprocalGainR =
    evalReal scalarRealEnv lowerBaseExpr - certifiedQuarticChargeR / (31 / 50) := by
  simp [scalarReciprocalGainR, lowerGainRExpr, certifiedQuarticChargeR, evalReal, sc]

theorem scalarReciprocalGainR_ge : (3143488/10^7 : ℝ) ≤ scalarReciprocalGainR :=
  lower_gain_margin_R.1

end
end ASDExplicitGamma.Scalar
