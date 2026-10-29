module

public import ASDExplicitGamma.Native.ParentBoundaryMixedPairing
public import ASDExplicitGamma.Native.ParentBoundarySourceBudget
public import ASDExplicitGamma.Native.OldSignedJointReciprocalBudget
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget

/-! The dominant OLD mixed cross uses the direct sum of the actual loads. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Triadic
noncomputable section

/-- The signed A-R minus Z-R remainder has one parent source factor and
one joint reciprocal norm. All covariance and load sums precede Cauchy--Schwarz;
the signed flat parts remain explicit for the exact covariance cancellation. -/
theorem parent_boundary_joint_mixed_feedback (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := fun plus n i => oldSignedFlatInput Q b L plus n i
    let H := fun plus n i => parentBoundaryOldSource Q nu sigma hnu hsigma k b L n
      (oldSignedFlatLoad plus i)
    let Z := fun plus n i => oldSignedFlatCellResidual Q mesh nu sigma hnu hsigma k b L plus n i U hU
    let R := fun plus n i => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k (H plus n i)
      (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))
    let delta := fun plus n i => oldSignedEnergyPairing U nu sigma kU (Z plus n i) (R plus n i)-
      volumeAverage (openCubeSet U) (fun x => vecDot (F plus n i x).2 (H plus n i x).2)
    let f := fun n => (∑ i : Fin 2,delta true n i)-(∑ i : Fin 2,delta false n i)
    let P := fun plus => ∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField nu sigma kU)
      (if plus then (oldSignedBlockMean U (F plus n i)).2 else (oldSignedBlockMean U (F plus n i)).1)
    Summable f ∧ |∑' n,f n| ≤ parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L*
      (Real.sqrt (P true+P false)+
        Real.sqrt ((oldSignedInverseHistory U a+1)^2*oldSignedFlatOscillationSize Q U b L true^2+
          oldSignedInverseHistory U a*oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2)) := by
  intro Q hsub a kU F H Z R delta f P
  let g := fun plus n i => vectorWeakHaarNorm U (fun x =>
    (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) (Z plus n i) x).2-
      (F plus n i x).2)
  let v := fun n => Sum.elim (g true n) (g false n)
  let p := fun n c => vectorPositiveHaarNorm U (fun x =>
    (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c) x).2)
  let d := fun n => Sum.elim (delta true n) (fun i => -delta false n i)
  have hv := old_signed_actual_joint_reciprocal_budget Q mesh nu sigma hnu hsigma k b L U hU
  have hvs : Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,v n c^2) := by
    simpa only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hv.1
  have hps : Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,p n c^2) :=
    parent_boundary_cell_source_series Q U mesh hU nu sigma hnu hsigma k b L
  have hd (n : whiteBasisIndex) (c : BlockCoord 2) : |d n c|≤v n c*p n c := by
    cases c with
    | inl i => exact parent_boundary_actual_mixed_pairing m mesh nu sigma hnu hsigma k b L true n i U hU
    | inr i =>
      change |-delta false n i|≤g false n i*p n (.inr i)
      rw [abs_neg]
      exact parent_boundary_actual_mixed_pairing m mesh nu sigma hnu hsigma k b L false n i U hU
  have hh := old_signed_load_series_pairing_budget v p d
    (fun n c => by cases c <;> exact Real.sqrt_nonneg _)
    (fun _ _ => Real.sqrt_nonneg _) hvs hps hd
  have he (n : whiteBasisIndex) : (∑ c : BlockCoord 2,d n c)=f n := by
    simp only [d,f,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_neg_distrib,sub_eq_add_neg]
  simp_rw [he] at hh
  have hvb : Real.sqrt (∑' n : whiteBasisIndex,∑ c : BlockCoord 2,v n c^2) ≤
      Real.sqrt (P true+P false)+
        Real.sqrt ((oldSignedInverseHistory U a+1)^2*oldSignedFlatOscillationSize Q U b L true^2+
          oldSignedInverseHistory U a*oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2) := by
    simpa only [v,P,F,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,ite_true,
      Bool.false_eq_true,ite_false] using hv.2
  refine ⟨hh.1,?_⟩
  exact hh.2.trans ((mul_le_mul_of_nonneg_right hvb (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))

end
end ASDExplicitGamma.Native
