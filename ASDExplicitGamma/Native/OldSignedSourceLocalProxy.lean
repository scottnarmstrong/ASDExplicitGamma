module

public import ASDExplicitGamma.Native.OldSignedSourceDirectionalHistory

/-! The actual local response restriction consumes the source-law directional budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The local directional proxy used by the actual flat-cell construction is
identical to the proxy of the parent display field on that cell. -/
theorem old_signed_source_local_proxy_eq (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
      (oldSignedCellCoefficient (originCube 2 n) U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (oldSignedPartialResponseCoefficient n 1 t ω))) e=
      oldSignedDirectionalProxy U (oldSignedPartialFrameField M n 1 t ω) e := by
  let k := oldSignedPartialResponseCoefficient n 1 t ω
  have hσ := (Annealed.sigmaBar_characterization M n).1
  apply old_signed_directional_proxy_congr U _ _
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
      M.nu (Annealed.sigmaBar M n) M.nu_pos hσ _)
    ((responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
      M.nu (Annealed.sigmaBar M n) M.nu_pos hσ k).mono (measurableSet_openCubeSet U)
      (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  exact old_signed_cell_frame_coefficient_ae (originCube 2 n) U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) M.nu (Annealed.sigmaBar M n) k

/-- The literal coefficient restrictions in the plus-cell energy theorem have
finite expected directional proxies with the sharp half-trace budget. -/
theorem old_signed_source_local_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (e : Vec 2) :
    let p := fun ω => oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (oldSignedCellCoefficient (originCube 2 n) U
          (openCubeSet_subset_of_mem_descendantsAtDepth hU) (oldSignedPartialResponseCoefficient n 1 t ω))) e
    Integrable p (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,p ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ((1-inverseHistoryDiscount^2)*
          ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*vecNormSq e := by
  dsimp only
  simp_rw [old_signed_source_local_proxy_eq M n r U hU]
  exact old_signed_source_directional_proxy_payment M h hM hg n r hr U hU t ht hstates e

end
end ASDExplicitGamma.Native
