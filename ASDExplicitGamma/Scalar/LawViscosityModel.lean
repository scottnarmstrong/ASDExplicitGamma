module

public import ASDExplicitGamma.Scalar.LawShiftCarrier
public import Algsuperdiff.Section3.Cutoff.CoefficientFamily

/-! The exact fixed-shell-law family obtained by replacing molecular viscosity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory
open Algsuperdiff.Section3

/-- Change only viscosity; all shell-law data remain the original model data. -/
def modelWithViscosity {d : ℕ} (M : ABKModel d) (ν : ℝ) (hν : 0 < ν) : ABKModel d :=
  { M with nu := ν,nu_pos := hν }

/-- Literal amplitude/spatial covariance of each honest cutoff coefficient. -/
theorem coefficient_cutoff_scale_shift {d : ℕ} (M : ABKModel d) (m n : ℤ)
    (ω : Cutoff.CutoffSample d) (x : Vec d) :
    Cutoff.coefficientCutoff (Real.rpow 3 (M.gamma*((-m:ℤ):ℝ))*M.nu) n
      (cutoffScaleShift M.gamma m ω) x=
      Real.rpow 3 (M.gamma*((-m:ℤ):ℝ)) •
        Cutoff.coefficientCutoff M.nu (n+m) ω ((3:ℝ)^m • x) := by
  simp only [Cutoff.coefficientCutoff_apply,cutoff_scale_shift_value,smul_add,smul_smul]

/-- Rescaling space by a natural triadic factor gives c times the shifted unit-law coefficient. -/
theorem coefficient_cutoff_rescale {d : ℕ} (M : ABKModel d) (j : ℕ) (n : ℤ)
    (ω : Cutoff.CutoffSample d) :
    (fun x => Cutoff.coefficientCutoff M.nu (n+(j:ℤ)) ω ((3:ℝ)^(j:ℤ) • x))=
      Real.rpow 3 (M.gamma*(j:ℝ)) •
        (Cutoff.coefficientCutoff (Real.rpow 3 (-(M.gamma*(j:ℝ)))*M.nu) n
          (cutoffScaleShift M.gamma (j:ℤ) ω)).toFun := by
  have hi : Real.rpow 3 (M.gamma*(j:ℝ))*Real.rpow 3 (-(M.gamma*(j:ℝ)))=1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3),add_neg_cancel,Real.rpow_zero]
  funext x
  have h := coefficient_cutoff_scale_shift M (j:ℤ) n ω x
  simp only [Int.cast_neg,Int.cast_natCast,mul_neg] at h
  simp only [Pi.smul_apply]
  rw [h]
  simp only [smul_smul,hi,one_smul]

end ASDExplicitGamma.Scalar
