module

public import ASDExplicitGamma.Native.ParentBoundaryMixedPairing
public import ASDExplicitGamma.Native.OldSignedFlatReciprocalBudget
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles

/-! Complete actual mixed A-R and Z-R bills, with the signed flat
pairing retained separately for the exact covariance cancellation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual complete mixed remainder is bounded by the joint local
reciprocal/source budget; its signed flat pairing is retained. -/
theorem parent_boundary_actual_mixed_bill (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := fun n i => oldSignedFlatInput Q b L plus n i
    let H := fun n i => parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)
    let Z := fun n i => oldSignedFlatCellResidual Q mesh nu sigma hnu hsigma k b L plus n i U hU
    let R := fun n i => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k (H n i)
      (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))
    let f := fun n => ∑ i : Fin 2,(oldSignedEnergyPairing U nu sigma kU (Z n i) (R n i)-
      volumeAverage (openCubeSet U) (fun x => vecDot (F n i x).2 (H n i x).2))
    Summable f ∧ |∑' n,f n|≤parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L*
      (Real.sqrt (6*oldSignedCorrectorHistory U a)*oldSignedFlatL2Size Q U b L plus+
        (oldSignedResponseHistory U a+1)*oldSignedFlatOscillationSize Q U b L plus) := by
  intro Q hsub a kU F H Z R f
  let v := fun n i => vectorWeakHaarNorm U (fun x =>
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (Z n i x)).2-(F n i x).2)
  let p := fun n i => vectorPositiveHaarNorm U (fun x => (H n i x).2)
  let delta := fun n i => oldSignedEnergyPairing U nu sigma kU (Z n i) (R n i)-
    volumeAverage (openCubeSet U) (fun x => vecDot (F n i x).2 (H n i x).2)
  have hv := old_signed_actual_flat_reciprocal_series Q mesh nu sigma hnu hsigma k b L plus U hU
  have hp := parent_boundary_selected_source_budget m mesh nu sigma hnu hsigma k b L plus U hU
  have hh := old_signed_load_series_pairing_budget v p delta
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) hv.1 hp.1
    (fun n i => parent_boundary_actual_mixed_pairing m mesh nu sigma hnu hsigma k b L plus n i U hU)
  have hvbound := hv.2.trans (add_le_add (mul_le_mul_of_nonneg_left
    (old_signed_flat_mean_size_le_l2 Q mesh b L plus U hU) (Real.sqrt_nonneg _)) le_rfl)
  have hM : 0≤oldSignedResponseHistory U a := ENNReal.toReal_nonneg
  have hnonneg : 0≤Real.sqrt (6*oldSignedCorrectorHistory U a)*oldSignedFlatL2Size Q U b L plus+
      (oldSignedResponseHistory U a+1)*oldSignedFlatOscillationSize Q U b L plus :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (add_nonneg hM (by norm_num)) (Real.sqrt_nonneg _))
  refine ⟨hh.1,?_⟩
  exact hh.2.trans ((mul_le_mul hvbound hp.2 (Real.sqrt_nonneg _) hnonneg).trans_eq (mul_comm _ _))

end
end ASDExplicitGamma.Native
