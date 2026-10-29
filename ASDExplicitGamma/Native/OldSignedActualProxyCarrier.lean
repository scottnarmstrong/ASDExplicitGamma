module

public import ASDExplicitGamma.Native.OldSignedJointSpatialProxy
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy

/-! Identification of the physical AN covariance profiles with their actual-law proxies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Response Algsuperdiff.Section3
noncomputable section

/-- The complete plus profile in the physical generator equals the actual
restricted-coefficient random proxy used by the moment estimates. -/
theorem old_signed_actual_plus_proxy_eq (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    oldSignedFlatDirectionalMeanProxy (originCube 2 n) U (oldSignedPartialFrameField M n 1 t ω) b L true=
      oldSignedActualPlusMeanProxy M n r U hU t b L ω := by
  have hh := old_signed_flat_directional_proxy_cell_eq (originCube 2 n) U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω) b L true
  exact hh.symm

/-- The minus physical profile has the same exact carrier identification. -/
theorem old_signed_actual_minus_proxy_eq (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    oldSignedFlatDirectionalMeanProxy (originCube 2 n) U (oldSignedPartialFrameField M n 1 t ω) b L false=
      oldSignedActualMinusMeanProxy M n r U hU t b L ω := by
  have hh := old_signed_flat_directional_proxy_cell_eq (originCube 2 n) U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω) b L false
  exact hh.symm

end
end ASDExplicitGamma.Native
