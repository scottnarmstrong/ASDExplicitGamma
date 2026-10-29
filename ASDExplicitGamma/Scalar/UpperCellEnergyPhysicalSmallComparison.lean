module

public import ASDExplicitGamma.Scalar.UpperCellEnergyCoefficientPath
public import ASDExplicitGamma.Scalar.UpperCellEnergySmallComparison

/-! The source small-event comparison for the actual centered terminal coarse
matrix, in the fixed OLD frame and with the literal fresh Sobolev band. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Inverse Triadic
noncomputable section

/-- Small-event upper comparison of the physical centered terminal matrix to
the physical OLD matrix. The only estimate premise is the defining small event. -/
theorem upper_cell_physical_small_comparison
    (M : ABKModel 2) (Q : TriadicCube 2) (n terminal : ℤ) (hn : n ≤ terminal)
    (sigma : ℝ) (hsigma : 0 < sigma) (ω : Cutoff.CutoffSample 2)
    (hsmall : sensitivityDsharp Q (laterBandW2 Q n terminal (fun _ => sigma⁻¹) ω) *
      sensitivityPathLambdaInverse (M.nu/sigma) (div_pos M.nu_pos hsigma)
        (sigma⁻¹ • oldCutoffSkewCoefficient n Q ω)
        (laterResponseCoefficient Q n terminal (fun _ => sigma⁻¹) ω) (1/4) 0 ≤ 2/5) :
    let h := laterBandW2 Q n terminal (fun _ => sigma⁻¹) ω
    let x := sensitivityDsharp Q h *
      sensitivityPathLambdaInverse (M.nu/sigma) (div_pos M.nu_pos hsigma)
        (sigma⁻¹ • oldCutoffSkewCoefficient n Q ω)
        (laterResponseCoefficient Q n terminal (fun _ => sigma⁻¹) ω) (1/4) 0
    let centered := oldCutoffSkewCoefficient terminal Q ω -
      BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*cubeAverage Q h.value.toFun)
    BlockMatLoewnerLE
      (coarseBlockMatrix (openCubeSet Q) (responseFramePlanarCoefficientField M.nu sigma centered))
      (sensitivityBlockScale (1+(5/4:ℝ)*x)
        (coarseBlockMatrix (openCubeSet Q)
          (responseFramePlanarCoefficientField M.nu sigma (oldCutoffSkewCoefficient n Q ω)))) := by
  have hh := upper_cell_small_centered_matrix (M.nu/sigma) (div_pos M.nu_pos hsigma)
    (sigma⁻¹ • oldCutoffSkewCoefficient n Q ω)
    (laterResponseCoefficient Q n terminal (fun _ => sigma⁻¹) ω)
    (laterBandW2 Q n terminal (fun _ => sigma⁻¹) ω)
    (later_response_coefficient_represents Q n terminal (fun _ => sigma⁻¹) ω)
    (by norm_num : (0:ℝ)<1/4) le_rfl hsmall
  rw [upper_cell_centered_response_path Q n terminal hn sigma hsigma ω,
    upper_cell_normalized_book_matrix Q M.nu sigma M.nu_pos hsigma,
    upper_cell_normalized_book_matrix Q M.nu sigma M.nu_pos hsigma] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
