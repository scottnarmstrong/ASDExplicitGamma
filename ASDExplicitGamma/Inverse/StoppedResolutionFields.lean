module

public import ASDExplicitGamma.Inverse.StoppedPhysicalFineBlockIndex
public import ASDExplicitGamma.Inverse.StoppedComponentStarSupport
public import ASDExplicitGamma.Inverse.StoppedDiameterCharge

/-! The literal three physical Z resolutions at a current source layer.
The preceding mesh group uses exactly one of the two coarser resolutions. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

def layerResolutionLabel (Q : TriadicCube 2) (H n : ℕ) (e : Fin 3) : ℤ :=
  Q.scale-(compatibleWhitneyMeshDepth H n:ℤ)+(e.val:ℤ)

def layerResolutionDiameter (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (τ η : ℝ)
    (n : ℕ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) (x : Vec 2) : ℝ :=
  let j := layerResolutionLabel Q H n e
  realDiameterField (q3PlanarMarks M j τ η) (physicalBlockIndex j x) ω

theorem whitney_mesh_depth_step (H n : ℕ) :
    compatibleWhitneyMeshDepth H n+1 ≤ compatibleWhitneyMeshDepth H (n+1) ∧
      compatibleWhitneyMeshDepth H (n+1) ≤ compatibleWhitneyMeshDepth H n+2 := by
  have hs := whitney_profile_step H n
  unfold compatibleWhitneyMeshDepth
  omega

theorem whitney_mesh_previous_gap (H n : ℕ) :
    compatibleWhitneyMeshDepth H (n-1) ≤ compatibleWhitneyMeshDepth H n ∧
      compatibleWhitneyMeshDepth H n-compatibleWhitneyMeshDepth H (n-1) ≤ 2 := by
  cases n with
  | zero => simp only [Nat.zero_sub,Nat.sub_self]; omega
  | succ n =>
    have hs := whitney_mesh_depth_step H n
    simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using (show
      compatibleWhitneyMeshDepth H n ≤ compatibleWhitneyMeshDepth H (n+1) ∧
      compatibleWhitneyMeshDepth H (n+1)-compatibleWhitneyMeshDepth H n ≤ 2 from by omega)

def layerPreviousResolution (H n : ℕ) : Fin 3 :=
  ⟨compatibleWhitneyMeshDepth H n-compatibleWhitneyMeshDepth H (n-1),
    by have hs := (whitney_mesh_previous_gap H n).2; omega⟩

theorem layer_previous_resolution_pos (H n : ℕ) (hn : 1 ≤ n) :
    1 ≤ (layerPreviousResolution H n).val := by
  have hs := whitney_mesh_depth_step H (n-1)
  have he : n-1+1=n := by omega
  rw [he] at hs
  change 1 ≤ compatibleWhitneyMeshDepth H n-compatibleWhitneyMeshDepth H (n-1)
  omega

theorem layer_previous_resolution_label (Q : TriadicCube 2) (H n : ℕ) :
    layerResolutionLabel Q H n (layerPreviousResolution H n)=
      Q.scale-(compatibleWhitneyMeshDepth H (n-1):ℤ) := by
  have hs := (whitney_mesh_previous_gap H n).1
  simp only [layerResolutionLabel,layerPreviousResolution,Nat.cast_sub hs]
  ring

theorem layer_resolution_protected (Q : TriadicCube 2) (H n : ℕ) (e : Fin 3) :
    layerResolutionLabel Q H n e ≤ Q.scale-(H:ℤ) := by
  have he := e.isLt
  unfold layerResolutionLabel compatibleWhitneyMeshDepth whitneyProfile
  omega

theorem layer_resolution_diameter_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (τ η : ℝ) (n : ℕ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    0 ≤ layerResolutionDiameter M Q H τ η n e ω x := ENNReal.toReal_nonneg

end
end ASDExplicitGamma.Inverse
