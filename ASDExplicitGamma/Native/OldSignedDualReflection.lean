module

public import ASDExplicitGamma.Native.OldSignedCanonicalResponseSpace

/-! The actual complementary involution J_A = R A on physical fields.
Its energy and compatibility identities underpin the paired defect budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- Actual coefficient dual reflection, with the same physical frame. -/
def oldSignedDualReflection (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2) : Vec 2 → BlockVec 2 :=
  fun x => (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (F x)).swap

/-- Reflection preserves square integrability on the actual cell. -/
theorem old_signed_dual_reflection_memL2 (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    MemBlockL2 (openCubeSet Q) (oldSignedDualReflection Q nu sigma k F) := by
  have hf := scalar_coefficient_flux_memL2 Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) hF
  exact memBlockL2_blockField (memVectorL2_snd_of_memBlockL2 hf) (memVectorL2_fst_of_memBlockL2 hf)

/-- Reflection preserves the exact physical energy pairing. -/
theorem old_signed_dual_reflection_isometry (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k (oldSignedDualReflection Q nu sigma k F)
      (oldSignedDualReflection Q nu sigma k G)=oldSignedEnergyPairing Q nu sigma k F G :=
  pairedReflect_pairingAverage_isometry
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) ⟨fun x => (F x).1,fun x => (F x).2⟩ ⟨fun x => (G x).1,fun x => (G x).2⟩

/-- Pairing with the actual reflected field removes the coefficient
exactly, leaving the complementary unweighted pairing. -/
theorem old_signed_dual_reflection_pairing (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k F (oldSignedDualReflection Q nu sigma k G)=
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (G x).swap) := by
  unfold oldSignedEnergyPairing volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact congrArg (blockVecDot (F x)) (pairedReflectState_action
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) ⟨fun y => (G y).1,fun y => (G y).2⟩ hx)

/-- The reflected actual canonical field is compatible. Its potential
is the recovered reciprocal potential and its flux is the response image. -/
theorem old_signed_reflected_canonical_compatible (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ScalarCompatible (openCubeSet Q) (oldSignedDualReflection Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  refine ⟨old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (Lp.memLp _),?_,?_⟩
  · exact IsPotentialOn.congr_ae (old_signed_reciprocal_potential_grad Q a hEll P)
      ⟨oldSignedReciprocalPotential Q a hEll P,rfl⟩
  · change IsSolenoidalOn (openCubeSet Q) (fun x =>
      (blockMatVecMul (blockCoeffField a x)
        ((oldSignedCanonicalBlockState Q nu sigma hnu hsigma k P).eval x)).1)
    exact blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace
      (a := a) (X := oldSignedCanonicalBlockState Q nu sigma hnu hsigma k P)
      (old_signed_canonical_response_space Q nu sigma hnu hsigma k P)

end
end ASDExplicitGamma.Native
