module

public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra
public import ASDExplicitGamma.Native.OldSignedCanonicalPotentials
public import ASDExplicitGamma.Native.OldSignedEnergyPartition

/-! Exact first variation of the actual canonical fields against physical
zero-trace and zero-normal-trace variations, for the paired parent budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The actual canonical field is orthogonal to every genuine physical
parent variation. No affine data are asserted on its child restrictions. -/
theorem old_signed_canonical_variation_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    {Y : Vec 2 → BlockVec 2} (hY : ScalarVariation (openCubeSet Q) Y) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) Y=0 := by
  let M := scalarFrameRealization Q nu sigma hnu hsigma k
  let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have hrebuild : toHilbertBlockL2OfBlockField hS=M.minimizerMap P := hilbert_field_rebuild _
  have hm := scalar_variation_mem_frame_correction Q nu sigma hnu hsigma k hY
  have hh := M.minimizerMap_firstVariation P ⟨toHilbertBlockL2OfBlockField hY.1,hm⟩
  change M.energyBilin (M.minimizerMap P) (toHilbertBlockL2OfBlockField hY.1)=0 at hh
  have he := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hY.1 hS
  rw [hrebuild,M.energySymm] at he
  exact he.symm.trans hh

/-- The canonical energy is exactly its physical coarse quadratic form. -/
theorem old_signed_canonical_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)=
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
        (responseFramePlanarCoefficientField nu sigma k)) P) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have he := old_signed_energy_pairing_congr_ae Q nu sigma k
    (old_signed_canonical_affine_field_recovery Q a hEll P)
    (old_signed_canonical_affine_field_recovery Q a hEll P)
  have hh := scalar_cell_response_test_energy Q a hEll P
  rw [cube_coarseMatrix_eq_open] at hh
  exact he.trans hh

end
end ASDExplicitGamma.Native
