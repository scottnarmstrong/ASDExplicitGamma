module

public import ASDExplicitGamma.Native.ParentBoundaryBrokenBudgets
public import ASDExplicitGamma.Native.GenericSourceBandFrame
public import ASDExplicitGamma.Inverse.SourceFramedHistory

/-! Exact actual-law bank and trace sequences for the simultaneous band,
with all descendants kept in the starting true scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Actual normalized simultaneous-band coefficient on the parent cube. -/
def parentBoundaryBandFrameField (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega))

/-- Actual depthwise extended bank maximum, converted to real only at a
finite population of physical cells. -/
def parentBoundaryBandInverseDepth (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  (bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 n) j)
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega).toReal

/-- Literal physical four-load trace on the actual attenuated band,
with sigma_n fixed at every descendant center. -/
def parentBoundaryBandTraceDepth (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  descendantsAverage (originCube 2 n) j (fun U => traceDefect (cubeSet U)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega) (Annealed.sigmaBar M n))

/-- The complete physical depth bank maximum is exactly the extended
normalized inverse maximum; no finiteness event is needed for a finite depth. -/
theorem parent_boundary_band_inverse_depth_ennreal (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) :
    bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 n) j)
      M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega =
    ENNReal.ofReal (lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t omega) j) := by
  let Q := originCube 2 n
  let a := parentBoundaryBandFrameField M n height t omega
  have hs := (Annealed.sigmaBar_characterization M n).1
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M n) M.nu_pos hs
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega))
  have hmax := bank_finite_max_ofReal (descendantsAtDepth Q j) (descendantsAtDepth_nonempty Q j)
    (fun U => rootInverseResponse M U n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
  change bankFiniteRootResponseMax (descendantsAtDepth Q j) M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega=_ at hmax
  rw [hmax]
  apply congrArg ENNReal.ofReal
  unfold lemmaVInverseDepthMax
  apply Book.Ch02.finsetSupReal_congr
  intro U hU
  rw [inverse_history_lowerRight U a (hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU))]
  dsimp only [a,parentBoundaryBandFrameField]
  rw [native_source_band_coarse_matrix_frame M n height t omega hU]
  simp only [frameMatrix]
  rw [inverse_history_matrixNorm_smul _ _ hs.le]
  rfl

/-- The real physical bank maximum is exactly the actual normalized
inverse maximum, after proving its finite extended representation. -/
theorem parent_boundary_band_inverse_depth (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) :
    parentBoundaryBandInverseDepth M n height t omega j=
      lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t omega) j := by
  rw [parentBoundaryBandInverseDepth,parent_boundary_band_inverse_depth_ennreal,
    ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg _ _ _)]

/-- The normalized complete trace sequence is precisely the physical
fixed-frame sequence on the same descendant cells. -/
theorem parent_boundary_band_trace_depth (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) :
    descendantsAverage (originCube 2 n) j (fun U => traceDefect (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega) 1)=
      parentBoundaryBandTraceDepth M n height t omega j := by
  unfold parentBoundaryBandTraceDepth descendantsAverage
  apply congrArg (fun z : ℝ => ((descendantsAtDepth (originCube 2 n) j).card : ℝ)⁻¹*z)
  apply Finset.sum_congr rfl
  intro U hU
  unfold traceDefect parentBoundaryBandFrameField
  rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
    native_source_band_coarse_matrix_frame M n height t omega hU]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

end
end ASDExplicitGamma.Native
