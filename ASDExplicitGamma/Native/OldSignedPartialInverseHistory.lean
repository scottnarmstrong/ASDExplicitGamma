module

public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory

/-! Exact physical inverse scaling and actual one-shell OLD weak proxy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Every actual inverse depth maximum has the same fixed scalar-frame
scaling as its descendant coarse matrices. -/
theorem old_signed_partial_inverse_depth (M : ABKModel 2) (n : ℤ) (s : ℕ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    lemmaVInverseDepthMax (originCube 2 n) (oldSignedPartialFrameField M n s t ω) j=
      (Annealed.sigmaBar M n : ℝ)*lemmaVInverseDepthMax (originCube 2 n)
        (Model.partialInsertedCoefficient M (n+(s:ℤ)-1) t ω).toFun j := by
  let Q := originCube 2 n
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet Q))
    (isBounded_cubeSet Q).isCompact_closure
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell (n+(s:ℤ)-1) ω ht
    (measurableSet_openCubeSet Q)
    (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet Q hx)))
  have hσ := (Annealed.sigmaBar_characterization M n).1
  exact pureFlux_inverseDepthMax_frame_eq Q _ _ hEll
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      M.nu (Annealed.sigmaBar M n) M.nu_pos hσ (oldSignedPartialResponseCoefficient n s t ω)) hσ j
    (fun U hU => old_signed_partial_cell_frame M n s t ω U j hU)

end
end ASDExplicitGamma.Native
