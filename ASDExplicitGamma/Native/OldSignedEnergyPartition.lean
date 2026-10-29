module

public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing
public import ASDExplicitGamma.Native.OldSignedShearFieldTransport

/-! Spatial partition of the physical feedback pairing, before any estimate
or complete-mode summation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- Changing representatives on the physical cell does not change its
normalized energy pairing. -/
theorem old_signed_energy_pairing_congr_ae (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G F' G' : Vec 2 → BlockVec 2}
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] F')
    (hG : G =ᵐ[volumeMeasureOn (openCubeSet Q)] G') :
    oldSignedEnergyPairing Q nu sigma k F G=oldSignedEnergyPairing Q nu sigma k F' G' := by
  unfold oldSignedEnergyPairing volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hF,hG] with x hx hy
  rw [hx,hy]

/-- The physical parent pairing is exactly the finite average in the true
restricted coefficients; no cell minimizer replaces either field. -/
theorem old_signed_energy_pairing_partition (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k F G=
      oldSignedCellAverage Q depth (fun U => oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) F G) := by
  have hh := old_signed_volumeAverage_descendants Q depth _
    (old_signed_energy_pairing_integrable Q nu sigma hnu hsigma k hF hG)
  change oldSignedEnergyPairing Q nu sigma k F G=_ at hh
  rw [hh,← old_signed_cell_average_eq_descendantsAverage]
  congr 1
  funext U
  unfold oldSignedEnergyPairing volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [old_signed_cell_frame_coefficient_ae Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma k] with x hx
  simp only [blockCoeffField,← hx]

/-- The physical shear respects cellwise almost-everywhere equality. -/
theorem old_signed_pointwise_shear_congr_ae (Q : TriadicCube 2) (psi : Vec 2 → ℝ)
    {F G : Vec 2 → BlockVec 2} (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    oldSignedPointwiseShear psi F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      oldSignedPointwiseShear psi G := by
  filter_upwards [h] with x hx
  change (0,-(psi x • matVecMul responsePlanarJ (F x).1))=
    (0,-(psi x • matVecMul responsePlanarJ (G x).1))
  rw [hx]

/-- Actual patched residual feedback partitions into actual cell residual
feedback against the same parent field. -/
theorem old_signed_patched_feedback_partition (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) {S F : Vec 2 → BlockVec 2}
    (hS : MemBlockL2 (openCubeSet Q) S) (hF : MemBlockL2 (openCubeSet Q) F) :
    oldSignedEnergyPairing Q nu sigma k S
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF))=
    oldSignedCellAverage Q depth (fun U => oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) S
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k F hF))) := by
  have hR := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  rw [old_signed_energy_pairing_partition Q depth nu sigma hnu hsigma k hS
    (old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hR)]
  congr 1
  funext U
  exact old_signed_energy_pairing_congr_ae U.val nu sigma _ Filter.EventuallyEq.rfl
    (old_signed_pointwise_shear_congr_ae U.val _
      (old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k F hF U.val U.property))

end
end ASDExplicitGamma.Native
