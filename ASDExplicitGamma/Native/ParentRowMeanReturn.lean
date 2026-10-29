module

public import ASDExplicitGamma.Native.ParentBoundaryWeakSourceReturn
public import ASDExplicitGamma.Native.ParentBoundaryMeanTheta
public import ASDExplicitGamma.Native.OldSignedInitialGenericMean

/-! The actual mesh-five parent mean with its generic initial value and physical source slope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Response Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- At the first weak depth the protected slope is the ordinary mesh-five source slope. -/
theorem parent_row_depth_zero_slope (gamma : ℝ) (height : ℕ) :
    parentBoundaryMeanDepthSlope gamma height 0=parentBoundaryMeanSourceSlope gamma height := by
  simp only [parentBoundaryMeanDepthSlope,parentBoundaryMeanSourceSlope,
    Nat.cast_zero,mul_zero,Real.rpow_zero,Nat.add_zero,mul_one,one_pow]

/-- Every actual mesh-five cell has the same endpoint-normalized source mean envelope. -/
theorem parent_row_actual_mean_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height)
    (hstate : nativeInductionState M h n) (hpast : ∀ k<n,nativeInductionState M h k)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ ω,traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)
      (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
    theta M*(nativeSourceGenericMeanProfile gammaZero 1 5+
      t*parentBoundaryMeanSourceSlope gammaZero height) := by
  have hh := parent_boundary_weak_cell_mean_return M h hM hg n height hheight hpast
    hstate r hr U hU t ht0 ht1 0
  simp only [parentBoundaryBandCellTrace,descendantsAverage,descendantsAtDepth_zero,
    Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_mul,
    Nat.add_zero,parent_row_depth_zero_slope] at hh
  have hi := old_signed_initial_generic_depth_mean M h hM hg n hpast 5 (by omega) (by omega)
  have hs := mul_le_mul_of_nonneg_left (parent_boundary_mean_source_slope_theta M hg height) ht0
  exact hh.trans ((add_le_add hi hs).trans_eq (by unfold gammaZero; ring))

end
end ASDExplicitGamma.Native
