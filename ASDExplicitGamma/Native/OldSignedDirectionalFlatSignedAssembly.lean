module

public import ASDExplicitGamma.Native.OldSignedDirectionalGlobalFlatEnergy
public import ASDExplicitGamma.Native.OldSignedSharpGlobalFlatEnergy
public import ASDExplicitGamma.Native.OldSignedAffineFamilyAssembly

/-! The two projected flat energies and the negative Dirichlet tangent
assemble into Bflat, signed Aff and the literal local oscillation bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- The complete flat part of the actual signed trial has precisely the
AN baseline. The negative tangent is used before any upper estimate. -/
theorem old_signed_flat_signed_energy_bill_directional (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let ep := fun plus n => ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L plus n i)
      (oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L plus n i)
    let f := fun n => ep true n+ep false n-2*oldSignedFlatDirichletModeEnergy Q b L n
    Summable f ∧ (∑' n,f n)≤oldSignedFlatBoundaryEnergy Q b L+
      oldSignedFlatAffineContribution Q depth a b L+
      descendantsAverage Q depth (fun U =>
        2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*
          oldSignedFlatOscillationSize Q U b L true+
        oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2+
        2*Real.sqrt (2*oldSignedCorrectorHistory U a)*
          (oldSignedFlatL2Size Q U b L false*oldSignedFlatOscillationSize Q U b L false)+
        oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2) := by
  intro a ep f
  let aff := fun plus n => descendantsAverage Q depth (fun U => ∑ i : Fin 2,
    (let p := oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
     blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p))
  let B := fun plus : Bool => descendantsAverage Q depth (fun U => if plus then
    2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*
      oldSignedFlatOscillationSize Q U b L true+
    oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2
    else 2*Real.sqrt (2*oldSignedCorrectorHistory U a)*
      (oldSignedFlatL2Size Q U b L false*oldSignedFlatOscillationSize Q U b L false)+
    oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2)
  have hp0 := old_signed_global_plus_energy_bill_directional Q depth nu sigma hnu hsigma k b L
  have hm0 := old_signed_global_flat_energy_bill_sharp Q depth nu sigma hnu hsigma k b L false
  have hp : (∑' n,ep true n)≤(∑' n,oldSignedFlatPlusModeEnergy Q b L n)+(∑' n,aff true n)+B true := by
    simpa only [ep,aff,B,a,oldSignedFlatInput,ite_true,old_signed_flat_plus_l2_mode] using hp0.2
  have hm : (∑' n,ep false n)≤(∑' n,oldSignedFlatDirichletModeEnergy Q b L n)+(∑' n,aff false n)+B false := by
    simpa only [ep,aff,B,a,oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode] using hm0.2
  have hsD := (old_signed_flat_minus_complete_energy Q b L).1
  have hsP : Summable (ep true) := hp0.1
  have hsM : Summable (ep false) := hm0.1
  have hs : Summable f := (hsP.add hsM).sub (hsD.mul_left 2)
  have he : (∑' n,f n)=(∑' n,ep true n)+(∑' n,ep false n)-
      2*(∑' n,oldSignedFlatDirichletModeEnergy Q b L n) := by
    exact ((hsP.add hsM).tsum_sub (hsD.mul_left 2)).trans (by rw [hsP.tsum_add hsM,tsum_mul_left])
  have haff : (∑' n,aff true n)+(∑' n,aff false n)=oldSignedFlatAffineContribution Q depth a b L :=
    old_signed_flat_affine_family_sum Q depth a b L
  have hbase := old_signed_flat_boundary_energy_difference Q b L
  have hB : B true+B false=descendantsAverage Q depth (fun U =>
        2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*
          oldSignedFlatOscillationSize Q U b L true+
        oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2+
        2*Real.sqrt (2*oldSignedCorrectorHistory U a)*
          (oldSignedFlatL2Size Q U b L false*oldSignedFlatOscillationSize Q U b L false)+
        oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2) := by
    simp only [B,ite_true,Bool.false_eq_true,ite_false]
    rw [← descendantsAverage_add]
    congr 1
    funext U
    ring
  refine ⟨hs,?_⟩
  rw [he,← hB]
  linarith only [hp,hm,haff,hbase]

end
end ASDExplicitGamma.Native
