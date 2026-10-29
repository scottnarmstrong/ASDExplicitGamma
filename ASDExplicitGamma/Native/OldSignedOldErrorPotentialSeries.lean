module

public import ASDExplicitGamma.Native.OldSignedPureSecondConvergence
public import ASDExplicitGamma.Native.OldSignedQ3SourceEnergy
public import ASDExplicitGamma.Native.OldSignedActualCellPotentials

/-! Genuine complete-mode convergence of the actual projected OLD-error
first potentials, with all source convergence inputs discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
noncomputable section

/-- The actual cell OLD-error first potentials are square-summable in
the weak Haar norm. Neither convergence nor a quantitative projection
estimate is assumed as a premise. -/
theorem old_signed_old_error_cell_potential_summable (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    Summable (fun n : whiteBasisIndex => vectorWeakHaarNorm U
      (oldSignedCellErrorPotential (originCube 2 m) U (openCubeSet_subset_of_mem_descendantsAtDepth hU)
        mesh nu sigma hnu hsigma k b L n P).toH1Function.grad^2) := by
  let Q := originCube 2 m
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let g := fun n x => (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P x).2
  have hg (n : whiteBasisIndex) : MemVectorL2 (openCubeSet U) (g n) := by
    have hp : MemVectorL2 (openCubeSet Q) (g n) := memVectorL2_snd_of_memBlockL2
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P)
    exact hp.mono_measure (Measure.restrict_mono_set volume hsub)
  have hpos (n : whiteBasisIndex) (i : Fin 2) : Summable (fun j =>
      (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1) (fun x => g n x i))) :=
    old_signed_old_error_source_positive m mesh a hEll P b L U hU n i
  have hs : Summable (fun n : whiteBasisIndex => vectorPositiveHaarNorm U (g n)^2) :=
    old_signed_old_error_source_cell_energy_summable m mesh a hEll P b L U hU
  have hh := old_signed_pure_second_residual_first_summable U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U hsub k) g hg hpos hs
  apply hh.congr
  intro n
  rw [old_signed_cell_error_potential_grad]
  rfl

end
end ASDExplicitGamma.Native
