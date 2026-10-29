module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusFluxSplit
public import ASDExplicitGamma.Scalar.OldHessianTrialFullModeColumns
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalPairing

/-! Exact original source cross on each fine cell, before mode sums. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The local projected minus pairs with the full mixed source through
exactly its affine TOP flux and its centered reciprocal flux. -/
theorem old_hessian_source_cell_cross_split (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q (coarse+1)) :
    let kU := oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k
    let F := oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2
    let Z := oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L p.1 p.2) (old_signed_flat_minus_block_memL2 Q b L p.1 p.2)
    oldSignedEnergyPairing U.val nu sigma kU F Z=
      cubeAverage U.val (fun x => vecDot
        (oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L p U x)
        (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p x))+
      cubeAverage U.val (fun x => vecDot
        (oldHessianMinusOscillationColumn Q (coarse+1) nu sigma hnu hsigma k b L p U x)
        (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p x)) := by
  intro kU F Z
  let A := oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L p U
  let O := oldHessianMinusOscillationColumn Q (coarse+1) nu sigma hnu hsigma k b L p U
  let f := oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p
  have hA := old_hessian_minus_affine_spatial_column_memLp Q (coarse+1) nu sigma hnu hsigma k b L p U
  have hO := old_hessian_minus_oscillation_column_memLp Q (coarse+1) nu sigma hnu hsigma k b L p U
  have hsource := (old_hessian_mixed_bottom_source_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2).mono_measure
    (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth U.property))
  have hf (i : Fin 2) : MemLp (fun x => f x i) 2 (normalizedCubeMeasure U.val) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hsource) i)
  have hs := old_hessian_minus_flux_split Q (coarse+1) nu sigma hnu hsigma k b L p U
  have hsn : (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) Z x).2)=ᵐ[
      normalizedCubeMeasure U.val] (fun x => A x+O x) := by
    let J : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) Z x).2
    let J' : Vec 2 → Vec 2 := fun x => A x+O x
    have hJ : J=ᵐ[volume.restrict (openCubeSet U.val)] J' := hs
    rw [←volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hJ
    exact Measure.ae_smul_measure hJ _
  have hfirst x : (F x).1=0 := by
    simp only [F,oldHessianMixedBottomSource,oldHessianMixedSource,oldSignedLocalizedPotentialShear,Prod.fst_add,zero_add]
  have he : oldSignedEnergyPairing U.val nu sigma kU F Z=
      cubeAverage U.val (fun x => vecDot (A x+O x) (f x)) := by
    unfold oldSignedEnergyPairing
    rw [←cube_average_eq_volume_average_open U.val]
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,cubeAverage_eq_integral_normalizedCubeMeasure]
    apply integral_congr_ae
    filter_upwards [hsn] with x hx
    change blockVecDot (F x) (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) Z x)=_
    change vecDot (F x).1 _+vecDot (f x) _=_
    rw [hfirst,hx]
    simp only [vecDot,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he]
  simp only [vecDot,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_add (old_hessian_vector_pairing_integrable U.val A f hA hf)
    (old_hessian_vector_pairing_integrable U.val O f hO hf)

end
end ASDExplicitGamma.Scalar
