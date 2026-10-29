module

public import ASDExplicitGamma.Scalar.UpperCellEnergyGlobalBookComparison

/-! The all-event large-response comparison in the actual physical fixed
OLD frame, with the literal fresh mean skew removed. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic Inverse Algsuperdiff.Section3
noncomputable section

/-- Actual physical centered-terminal comparison on every sample, with no
smallness or norm-bound premise. The same fresh envelope is used throughout. -/
theorem upper_cell_physical_large_comparison
    (M : ABKModel 2) (n ell : ℤ) (height : ℕ) (ω : Cutoff.CutoffSample 2) :
    let Q := originCube 2 (n-ell)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let h := laterBandW2 Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
    let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
      (fun _ => sigma⁻¹) (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
    let A := 1+2*(lagTraceHistory M n ell ω).toReal+Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)
    let centered := oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω-
      BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*cubeAverage Q h.value.toFun)
    ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
        (responseFramePlanarCoefficientField M.nu sigma centered)) P) ≤
        A*(1+3*A*F)*(1+2*F+4*F^2)*blockVecDot P P := by
  dsimp only
  intro P
  have hh := upper_cell_global_book_comparison M n ell height ω P
  rw [upper_cell_centered_response_path _ n (n+(height:ℤ)) (by omega)
    _ (Annealed.sigmaBar M n).property ω,
    upper_cell_normalized_book_matrix _ M.nu _ M.nu_pos (Annealed.sigmaBar M n).property] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
