module

public import ASDExplicitGamma.Native.OldSignedFlatBounds

/-! Centering preserves the actual potential/solenoidal source class. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

private theorem old_signed_solenoidal_congr {U : Set (Vec 2)}
    {F G : Vec 2 → Vec 2} (hFG : F =ᵐ[volumeMeasureOn U] G)
    (hF : IsSolenoidalOn U F) : IsSolenoidalOn U G := by
  intro φ
  calc
    ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          exact hFG.symm.mono fun x hx => by simp [hx]
    _ = 0 := hF φ


theorem old_signed_centered_source_compatible (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F)
    (hcompat : ScalarCompatible (openCubeSet Q) F) :
    ScalarCompatible (openCubeSet Q)
      (fun x => F x - oldSignedBlockMean Q F) := by
  let U := openCubeSet Q
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  have hG : MemBlockL2 U G := hF.sub (memLp_const m)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : (volume U).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hConstPot : IsPotentialOn U (fun _ : Vec 2 => m.1) := by
    exact (H1Function.affineOnIsSobolevRegularDomain hU.isSobolevRegularDomain m.1).isPotentialOn
  have hConstSol : IsSolenoidalOn U (fun _ : Vec 2 => m.2) :=
    IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain
      hU.isSobolevRegularDomain hvol m.2
  have hGpotSum : IsPotentialOn U
      ((fun x => (F x).1) + (-1 : ℝ) • fun _ : Vec 2 => m.1) :=
    isPotentialOn_add hcompat.2.1 (isPotentialOn_smul hConstPot (-1 : ℝ))
  have hGpotAE : ((fun x => (F x).1) + (-1 : ℝ) • fun _ : Vec 2 => m.1) =ᵐ[
      volumeMeasureOn U] (fun x => (G x).1) := by
    filter_upwards with x
    ext i
    simp [G]
    ring
  have hGpot : IsPotentialOn U (fun x => (G x).1) :=
    old_signed_isPotentialOn_congr_ae hGpotSum hGpotAE
  have hGsecondAdd : IsSolenoidalOn U
      ((fun x => (F x).2) + (-1 : ℝ) • fun _ : Vec 2 => m.2) :=
    isSolenoidalOn_add_of_memVectorL2
      (memVectorL2_snd_of_memBlockL2 hF) ((memVectorL2_const m.2).const_smul (-1 : ℝ))
      hcompat.2.2 (isSolenoidalOn_smul hConstSol (-1 : ℝ))
  have hGsol : IsSolenoidalOn U (fun x => (G x).2) := by
    apply old_signed_solenoidal_congr ?_ hGsecondAdd
    filter_upwards with x
    ext i
    simp [G]
    ring
  exact ⟨hG, hGpot, hGsol⟩


end
end ASDExplicitGamma.Native
