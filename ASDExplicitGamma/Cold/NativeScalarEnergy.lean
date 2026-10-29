module

public import ASDExplicitGamma.Cold.NativeMatchedFamily

/-! # Exact constant symmetric energy of the native molecular coefficient -/

@[expose] public section
noncomputable section
open Homogenization Algsuperdiff.Section3
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The normalized native symmetric part is the actual molecular parameter divided by its true frame. -/
theorem coldNativeCoefficient_symmPart (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart ((coldNativeCoefficient M m ω).toFun x) = coldNativeLower M m • (1:Mat 2) := by
  have he : symmPart ((coldNativeCoefficient M m ω).toFun x) =
      (Annealed.sigmaBar M m:ℝ)⁻¹ • symmPart (Cutoff.coefficientCutoff M.nu m ω x) := by
    ext i j
    simp only [coldNativeCoefficient,RegCoeffField.smul_apply,symmPart,Matrix.smul_apply,
      smul_eq_mul]
    ring
  rw [he,Cutoff.symmPart_coefficientCutoff,smul_smul]
  rfl

/-- Passing to the actual adjoint preserves the symmetric molecular energy. -/
theorem coldNativeAdjoint_symmPart (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart ((adjointReg (coldNativeCoefficient M m ω)).toFun x) = coldNativeLower M m • (1:Mat 2) := by
  have he : symmPart ((adjointReg (coldNativeCoefficient M m ω)).toFun x) =
      symmPart ((coldNativeCoefficient M m ω).toFun x) := by
    ext i j
    simp only [adjointReg_apply,symmPart,Matrix.transpose_apply]
    ring
  rw [he,coldNativeCoefficient_symmPart]

/-- A scalar symmetric part makes the exact variation energy a sum of squared gradients. -/
theorem cold_scalar_energy_integrand {U : Set (Vec 2)} {a : CoeffField 2} {ν : ℝ}
    (ha : ∀ x, symmPart (a x) = ν • (1:Mat 2)) (v : AHarmonicFunction a U) (x : Vec 2) :
    scalarVariationEnergyIntegrand a v x = ν*∑ i : Fin 2, (v.toH1.grad x i)^2 := by
  unfold scalarVariationEnergyIntegrand
  rw [ha]
  simp [vecDot,matVecMul,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,pow_two]
  ring

end ASDExplicitGamma.Cold
