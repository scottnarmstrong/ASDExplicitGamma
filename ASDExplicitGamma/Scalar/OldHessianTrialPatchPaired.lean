module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarsePaired
public import ASDExplicitGamma.Native.OldSignedHaarCongr

/-! Paired coercivity for the literal globally patched comparison, measured
on the original fine partition even when its source patch is coarser. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Weak energy, including its mean, depends only on the cell class. -/
theorem old_hessian_vector_weak_energy_congr (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2} (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    vectorWeakHaarEnergy Q F=vectorWeakHaarEnergy Q G :=
  old_signed_coordinate_primal_sum_congr Q (Real.sqrt 3)⁻¹ h

/-- Exact nested partition for two vector fields with named local
representatives; no continuity across the coarse interfaces is asserted. -/
theorem old_hessian_paired_weak_partition (Q : TriadicCube 2) (coarse refinement : ℕ)
    (F G : Vec 2 → Vec 2)
    (f g : (D : OldSignedCellIndex Q coarse) → Vec 2 → Vec 2)
    (hf : ∀ D, F =ᵐ[volumeMeasureOn (openCubeSet D.val)] f D)
    (hg : ∀ D, G =ᵐ[volumeMeasureOn (openCubeSet D.val)] g D) :
    lemmaVTiledWeakEnergy Q (coarse+refinement) F+lemmaVTiledWeakEnergy Q (coarse+refinement) G =
      oldSignedCellAverage Q coarse (fun D =>
        lemmaVTiledWeakEnergy D.val refinement (f D)+lemmaVTiledWeakEnergy D.val refinement (g D)) := by
  unfold lemmaVTiledWeakEnergy
  rw [←descendantsAverage_add,descendantsAverage_add_eq_descendantsAverage_descendantsAverage]
  have he : oldSignedCellAverage Q coarse (fun D =>
      descendantsAverage D.val refinement (fun U => vectorWeakHaarEnergy U (f D))+
      descendantsAverage D.val refinement (fun U => vectorWeakHaarEnergy U (g D))) =
      oldSignedCellAverage Q coarse (fun D => descendantsAverage D.val refinement (fun U =>
        vectorWeakHaarEnergy U F+vectorWeakHaarEnergy U G)) := by
    unfold oldSignedCellAverage
    congr 1
    apply Finset.sum_congr rfl
    intro D _
    dsimp only
    rw [←descendantsAverage_add]
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    rw [old_hessian_vector_weak_energy_congr U
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hU) (hf D))),
      old_hessian_vector_weak_energy_congr U
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hU) (hg D)))]
  rw [he,old_signed_cell_average_eq_descendantsAverage Q coarse
    (fun D => descendantsAverage D refinement (fun U => vectorWeakHaarEnergy U F+vectorWeakHaarEnergy U G))]

/-- The literal global patch difference has paired fine weak energy at
most the same fine history times its one physical coarse patch drop. -/
theorem old_hessian_actual_patch_paired_weak (Q : TriadicCube 2) (coarse refinement : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    let L := oldSignedLocalResidual Q coarse nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    lemmaVTiledWeakEnergy Q (coarse+refinement) (fun x => (S x-L x).1)+
      lemmaVTiledWeakEnergy Q (coarse+refinement)
        (fun x => (blockMatVecMul (blockCoeffField a x) (S x-L x)).2) ≤
      oldHessianFineInverseHistory Q (coarse+refinement) nu sigma k*
        oldHessianPatchDrop Q coarse nu sigma hnu hsigma k P := by
  intro a S L
  let W := fun D : OldSignedCellIndex Q coarse => oldHessianParentCellComparison Q D.val
    (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P
  rw [old_hessian_paired_weak_partition Q coarse refinement _ _
    (fun D => (W D).potential)
    (fun D x => (blockMatVecMul (blockCoeffField a x) ((W D).eval x)).2)
    (fun D => by
      filter_upwards [old_hessian_patch_comparison_restrict Q coarse nu sigma hnu hsigma k P D] with x hx
      exact congrArg Prod.fst hx)
    (fun D => by
      filter_upwards [old_hessian_patch_comparison_restrict Q coarse nu sigma hnu hsigma k P D] with x hx
      exact congrArg (fun Z => (blockMatVecMul (blockCoeffField a x) Z).2) hx)]
  exact old_hessian_coarse_comparison_paired_fine Q coarse refinement nu sigma hnu hsigma k P

end
end ASDExplicitGamma.Scalar
