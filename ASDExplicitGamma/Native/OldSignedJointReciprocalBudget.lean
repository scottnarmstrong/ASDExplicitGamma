module

public import ASDExplicitGamma.Native.OldSignedPlusInverseReciprocalBudget
public import ASDExplicitGamma.Native.OldSignedMinusReciprocalDirectionalBudget
public import ASDExplicitGamma.Native.OldSignedTwoNormBudget

/-! Joint reciprocal square budget on the disjoint top and bottom loads. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Triadic
noncomputable section

/-- The actual mixed-cross reciprocal array keeps both load families in
one square norm, with directional affine and oscillatory direct sums. -/
theorem old_signed_actual_joint_reciprocal_budget (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let F := fun plus n i => oldSignedFlatInput Q b L plus n i
    let Z := fun plus n i => oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U hU
    let g := fun plus n i => vectorWeakHaarNorm U (fun x =>
      (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) (Z plus n i) x).2-
        (F plus n i x).2)
    let P := fun plus => ∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField nu sigma kU)
      (if plus then (oldSignedBlockMean U (F plus n i)).2 else (oldSignedBlockMean U (F plus n i)).1)
    Summable (fun n : whiteBasisIndex => (∑ i : Fin 2,g true n i^2)+(∑ i : Fin 2,g false n i^2)) ∧
    Real.sqrt (∑' n : whiteBasisIndex,((∑ i : Fin 2,g true n i^2)+(∑ i : Fin 2,g false n i^2))) ≤
      Real.sqrt (P true+P false)+
      Real.sqrt ((oldSignedInverseHistory U a+1)^2*oldSignedFlatOscillationSize Q U b L true^2+
        oldSignedInverseHistory U a*oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2) := by
  intro a kU F Z g P
  have hp := old_signed_actual_plus_reciprocal_directional_inverse_series Q depth nu sigma hnu hsigma k b L U hU
  have hm := old_signed_actual_minus_reciprocal_directional_series Q depth nu sigma hnu hsigma k b L U hU
  have hfalse (n : whiteBasisIndex) (i : Fin 2) : g false n i=
      vectorWeakHaarNorm U (fun x => (scalarCoefficientFlux
        (responseFramePlanarCoefficientField nu sigma kU) (Z false n i) x).2) := by
    simp only [g,F,oldSignedFlatInput,Bool.false_eq_true,ite_false,oldSignedFlatMinusBlock,sub_zero]
  have hps : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,g true n i^2) := hp.1
  have hms : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,g false n i^2) := by
    simpa only [hfalse] using hm.1
  have hp0 (plus : Bool) : 0≤P plus := by
    apply tsum_nonneg
    intro n
    apply Finset.sum_nonneg
    intro i _
    exact (old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma kU _).1
  have hpb : Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,g true n i^2) ≤
      Real.sqrt (P true)+(oldSignedInverseHistory U a+1)*oldSignedFlatOscillationSize Q U b L true := hp.2
  have hmb : Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,g false n i^2) ≤
      Real.sqrt (P false)+Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)*
        oldSignedFlatOscillationSize Q U b L false := by
    simpa only [hfalse,P,F,oldSignedFlatInput,Bool.false_eq_true,ite_false] using hm.2
  have hh := old_signed_two_norm_budget _ _ _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hpb hmb
  have hB : 0≤oldSignedInverseHistory U a :=
    lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hM : 0≤oldSignedResponseHistory U a := ENNReal.toReal_nonneg
  have hg0 (plus : Bool) : 0≤∑' n : whiteBasisIndex,∑ i : Fin 2,g plus n i^2 :=
    tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp only [Real.sq_sqrt (hg0 _),Real.sq_sqrt (hp0 _),mul_pow,
    Real.sq_sqrt (mul_nonneg hB hM)] at hh
  rw [← hps.tsum_add hms] at hh
  exact ⟨hps.add hms,hh⟩

end
end ASDExplicitGamma.Native
