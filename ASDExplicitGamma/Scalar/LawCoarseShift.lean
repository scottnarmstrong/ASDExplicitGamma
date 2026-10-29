module

public import ASDExplicitGamma.Scalar.LawViscosityModel
public import ASDExplicitGamma.Variational.AdapterAmplitude
public import ASDExplicitGamma.Variational.TraceDefect
public import Homogenization.Book.Ch04.Theorems.DilationLaw

/-! Actual pathwise coarse response under the exact law scale shift. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational Book
open Algsuperdiff.Section3

/-- The actual model with the source viscosity nu 3^(-gamma m), and the same shell law. -/
noncomputable def viscosityShiftModel {d : ℕ} (M : ABKModel d) (m : ℤ) : ABKModel d :=
  modelWithViscosity M (Real.rpow 3 (-(M.gamma*(m:ℝ)))*M.nu)
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) M.nu_pos)

/-- The literal finite-volume coarse matrix has the exact paired amplitude/dilation covariance. -/
theorem cutoff_coarse_scale_shift (M : ABKModel 2) (j k : ℕ) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (cubeSet (originCube 2 ((j+k:ℕ):ℤ)))
      (Cutoff.coefficientCutoff M.nu (n+(j:ℤ)) ω).toFun=
    coarseMatrixRescale (Real.sqrt (Real.rpow 3 (M.gamma*(j:ℝ))))
      (coarseBlockMatrix (cubeSet (originCube 2 (k:ℤ)))
        (Cutoff.coefficientCutoff (viscosityShiftModel M (j:ℤ)).nu n
          (cutoffScaleShift M.gamma (j:ℤ) ω)).toFun) := by
  have hd := Ch04.coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M (n+(j:ℤ)) ω) j k
  rw [← hd]
  have he : (rescaleReg j (Cutoff.coefficientCutoff M.nu (n+(j:ℤ)) ω)).toFun=
      Real.rpow 3 (M.gamma*(j:ℝ)) •
        (Cutoff.coefficientCutoff (viscosityShiftModel M (j:ℤ)).nu n
          (cutoffScaleShift M.gamma (j:ℤ) ω)).toFun := by
    simpa only [viscosityShiftModel,modelWithViscosity,Int.cast_natCast,zpow_natCast,
      rescaleReg,smulReg] using coefficient_cutoff_rescale M j n ω
  rw [he]
  obtain ⟨Λ,hEll⟩ := cutoff_isEllipticFieldOn_cube (viscosityShiftModel M (j:ℤ)) n
    (cutoffScaleShift M.gamma (j:ℤ) ω) (originCube 2 (k:ℤ))
  exact coarseBlockMatrix_smul_elliptic_triCube (viscosityShiftModel M (j:ℤ)).nu_pos hEll
    (Real.rpow_pos_of_pos (by norm_num) _)

end ASDExplicitGamma.Scalar
