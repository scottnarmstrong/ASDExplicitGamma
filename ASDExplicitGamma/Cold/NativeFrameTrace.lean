module

public import ASDExplicitGamma.Cold.NativeCoefficient
public import ASDExplicitGamma.Cold.CoefficientFrame
public import Homogenization.CoarseGraining.OriginCubeOpenBridge

/-! # Exact identification of normalized actual-cell traces with the frozen frame -/

@[expose] public section
noncomputable section
open Homogenization Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- The source open domain and its half-open partition representative give the same coarse matrix. -/
theorem cold_coarse_cube_open (Q : TriadicCube 2) (a : CoeffField 2) :
    coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a := by
  let z : Vec 2 := fun i => (Q.index i:ℝ)*cubeScaleFactor Q
  have hcube : cubeSet Q = translateSet z (cubeSet (originCube 2 Q.scale)) :=
    cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hopen : openCubeSet Q = translateSet z (openCubeSet (originCube 2 Q.scale)) :=
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  rw [hcube,hopen,coarseBlockMatrix_translateSet_eq_translateCoeffField,
    coarseBlockMatrix_translateSet_eq_translateCoeffField,coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]

/-- The unit-frame trace of the normalized literal field is the original true-frame trace. -/
theorem cold_trace_frame {Q : TriadicCube 2} {a : CoeffField 2} {lam Λ σ : ℝ}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Λ (cubeSet Q) a) (hσ : 0 < σ) :
    traceDefect (openCubeSet Q) (σ⁻¹ • a) 1 = traceDefect (cubeSet Q) a σ := by
  unfold traceDefect
  rw [← cold_coarse_cube_open,cold_coarse_frame hlam hEll hσ]
  simp only [Variational.frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

/-- Exact equality of the actual source cell trace with the normalized optimizer-family trace. -/
theorem coldNativeCellTrace_eq_normalized (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    coldNativeCellTrace M m Q ω =
      traceDefect (openCubeSet Q) (coldNativeCoefficient M m ω).toFun 1 := by
  obtain ⟨Λ,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
  exact (cold_trace_frame M.nu_pos hEll (Annealed.sigmaBar_characterization M m).1).symm

end ASDExplicitGamma.Cold
