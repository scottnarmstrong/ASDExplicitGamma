module

public import ASDExplicitGamma.Joint.LowerScalarN
public import ASDExplicitGamma.Scalar.DefectCapRModel
public import ASDExplicitGamma.Scalar.ResolventCombineR
public import ASDExplicitGamma.Main.MainLaneClosed

/-! JO-LOWER-SCALAR-N closed: the certificate bundle is built from the certified
constants and the model defect cap, leaving only the standing assumptions. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar

noncomputable section

theorem jo_lower_scalar_N_closed (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ) (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n) :
    LowerScalarConclusion M h N := by
  have hflat : evalReal scalarRealEnv quarticFlatExpr =
      (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) := by
    simp [quarticFlatExpr, evalReal, sc]
    ring
  have hD0 : 0 ≤ evalReal scalarRealEnv quarticDefectRExpr := by
    rw [← defect_fdefR_eq_certificate]
    exact defectFdefR_nonneg _ _ _
  have hG := lower_gain_margin_R
  refine jo_lower_scalar_N_of_R_cert M h hM hγ N hprev
    { Ddef := evalReal scalarRealEnv quarticDefectRExpr
      Csh := certifiedQuarticSharpR
      Chg := certifiedQuarticChargeR
      G := scalarReciprocalGainR
      hDdef0 := hD0
      hdef := fun i hi => drop_defect_cap_R M h hM hγ i
        (fun n hn => hprev n (lt_of_le_of_lt hn hi))
      hCsh := by rw [certified_quartic_sharp_formula_R, hflat]
      hChg := certified_quartic_charge_factorization_R
      hG := drop_gain_eq_R
      hGm := (hG.2.1.le).trans scalarReciprocalGainR_ge |>.trans' (by norm_num) }

/-- The exact statement of the frozen `induction_step`. -/
theorem gate_step_closed (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n) :
    nativeInductionState M h N :=
  gate_step_of_lower_scalar M h hM hγ N hprev (jo_lower_scalar_N_closed M h hM hγ N hprev)

end

end ASDExplicitGamma.Joint
