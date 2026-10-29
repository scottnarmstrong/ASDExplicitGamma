module

public import ASDExplicitGamma.Native.OldSignedHalfGain
public import ASDExplicitGamma.Native.OldSignedGlobalPlusDirectionalFeedback

/-! The OLD plus-feedback bills with the half-gain constant `1/2 + 3^(-1/4)`
(E2 R13) in place of `1 + 3^(-1/4)`. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Variational
open ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The constructed plus first potential has the literal sharp affine
and pure-second oscillation bound in the same old-medium history. -/
theorem old_signed_actual_plus_first_directional_bound_halfgain (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := oldSignedFlatPlusBlock Q b L n i
    let m := oldSignedBlockMean U F
    let O := oldSignedBlockPositiveNorm U (F-fun _ => m)
    vectorWeakHaarNorm U
      (oldSignedCellPlusPotential Q U hsub nu sigma hnu hsigma k b L n i).toH1Function.grad ≤
      Real.sqrt (oldSignedDirectionalProxy U (responseFramePlanarCoefficientField nu sigma kU) m.2)+
        (1/2+inverseHistoryDiscount)*oldSignedInverseHistory U a*O := by
  intro a hsub kU F m O
  have hm : oldSignedBlockMean U F=(0,m.2) := by
    simp [m,F,oldSignedFlatPlusBlock,oldSignedBlockMean,cubeAverage_const]
    rfl
  have hh := old_signed_pure_second_first_directional_halfgain U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U hsub k) F
    (old_signed_flat_input_cell_memL2 Q depth b L true n i U hU)
    m.2 hm (fun _ => rfl)
    (old_signed_flat_input_cell_first_positive Q depth b L true n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L true n i U hU m.2)
  dsimp only at hh
  have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
  rw [hs.1] at hh
  rw [old_signed_cell_plus_potential_grad]
  exact hh

/-- The complete two-load first-potential norm has constant-one
mean/oscillation aggregation; convergence is part of the conclusion. -/
theorem old_signed_actual_plus_first_directional_series_halfgain (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)
    let g := fun n i => vectorWeakHaarNorm U
      (oldSignedCellPlusPotential Q U hsub nu sigma hnu hsigma k b L n i).toH1Function.grad
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,g n i^2) ∧
    Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,g n i^2) ≤
      Real.sqrt (∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField nu sigma kU) (m n i).2)+
        (1/2+inverseHistoryDiscount)*oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true := by
  intro a hsub kU m g
  let p := fun n i => oldSignedDirectionalProxy U
    (responseFramePlanarCoefficientField nu sigma kU) (m n i).2
  let v := fun n i => Real.sqrt (p n i)
  let O := fun n i => oldSignedBlockPositiveNorm U
    (oldSignedFlatPlusBlock Q b L n i-fun _ => m n i)
  have hp0 (n : whiteBasisIndex) (i : Fin 2) : 0≤p n i :=
    (old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma kU (m n i).2).1
  have hps : Summable (fun n => ∑ i : Fin 2,p n i) :=
    old_signed_actual_plus_directional_proxy_series Q depth nu sigma hnu hsigma k b L U hU
  have hvs : Summable (fun n => ∑ i : Fin 2,v n i^2) := by
    simpa only [v,Real.sq_sqrt (hp0 _ _)] using hps
  have hOs : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,O n i^2) :=
    old_signed_flat_oscillation_budget_series Q depth b L true U hU
  have hB : 0≤oldSignedInverseHistory U a :=
    lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hD : 0≤1/2+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hh := old_signed_load_series_linear_budget v O g
    (1:ℝ) ((1/2+inverseHistoryDiscount)*oldSignedInverseHistory U a)
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (by norm_num) (mul_nonneg hD hB) hvs hOs
    (fun n i => by simpa only [one_mul] using
      old_signed_actual_plus_first_directional_bound_halfgain Q depth nu sigma hnu hsigma k b L n i U hU)
  simpa only [v,Real.sq_sqrt (hp0 _ _),oldSignedFlatMeanSize,oldSignedFlatOscillationSize,
    oldSignedFlatInput,ite_true,O,m,p,one_mul] using hh


/-- The actual A feedback retains its complete directional proxy inside the
affine square root. No estimated norm or convergence is a premise. -/
theorem old_signed_actual_plus_feedback_directional_bill_halfgain (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)
    let A := fun n i => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (oldSignedFlatPlusBlock Q b L n i) (old_signed_flat_plus_block_memL2 Q b L n i)
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (A n i))
    Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k*
      (Real.sqrt (∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField nu sigma kU) (m n i).2)+
        (1/2+inverseHistoryDiscount)*oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true) := by
  intro hsub a kU m A f
  let F := fun n i => oldSignedFlatPlusBlock Q b L n i
  let hF := fun n i => old_signed_flat_plus_block_memL2 Q b L n i
  let v := fun n i => oldSignedCellPlusPotential Q U hsub nu sigma hnu hsigma k b L n i
  have hp := old_signed_actual_plus_first_directional_series_halfgain Q depth nu sigma hnu hsigma k b L U hU
  have hv (i : Fin 2) : Summable (fun n : whiteBasisIndex => vectorWeakHaarNorm U (v n i).toH1Function.grad^2) :=
    old_signed_finite_series_component _ (fun _ _ => sq_nonneg _) hp.1 i
  have heq : (∑ i : Fin 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n i).toH1Function.grad^2)=
      ∑' n : whiteBasisIndex,∑ i : Fin 2,vectorWeakHaarNorm U (v n i).toH1Function.grad^2 :=
    (Summable.tsum_finsetSum (fun i _ => hv i)).symm
  have hh := old_signed_complete_cell_correction_feedback Q U hsub nu sigma hnu hsigma k
    (fun i : Fin 2 => blockBasis (Sum.inl i)) b L F hF hv
  let fc := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((A n i : Vec 2 → BlockVec 2)-F n i))
  have hfc : fc=f := by
    funext n
    apply Finset.sum_congr rfl
    intro i _
    have hz : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (F n i)=0 := by
      funext x
      change (0,-(_ • matVecMul responsePlanarJ 0))=(0,0)
      rw [matVecMul_zero,smul_zero,neg_zero]
    rw [map_sub,hz,sub_zero]
  have hresult : Summable fc ∧ |∑' n,fc n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
        (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (Sum.inl i))).grad^2)*
      Real.sqrt (∑ i : Fin 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n i).toH1Function.grad^2) := hh
  rw [hfc,heq] at hresult
  have hg := old_signed_actual_top_reciprocal_budget Q U hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  exact ⟨hresult.1,hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hp.2
    (Real.sqrt_nonneg _) (mul_nonneg hκ (Real.sqrt_nonneg _)))⟩


/-- The actual parent top feedback is genuinely summable and obeys the
exact average of the local AN derivative bills. -/
theorem old_signed_global_plus_feedback_directional_bill_halfgain (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i))
    Summable f ∧ |∑' n,f n|≤descendantsAverage Q depth (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k*
      (Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)+
        (1/2+inverseHistoryDiscount)*oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true)) := by
  intro a f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (oldSignedFlatPlusBlock Q b L n i)
          (old_signed_flat_plus_block_memL2 Q b L n i)))
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    exact old_signed_patched_feedback_load_partition Q depth nu sigma hnu hsigma k b L n
      (fun i : Fin 2 => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedFlatPlusBlock Q b L n) (fun _ => Lp.memLp _)
      (old_signed_flat_plus_block_memL2 Q b L n)
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (old_signed_actual_plus_feedback_directional_bill_halfgain Q depth nu sigma hnu hsigma k b L U.val U.property).1)
    (fun U => by
      have hh := (old_signed_actual_plus_feedback_directional_bill_halfgain Q depth nu sigma hnu hsigma k b L U.val U.property).2
      have he := old_signed_flat_directional_proxy_cell_eq Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k b L true
      simp only [oldSignedFlatDirectionalMeanProxy,oldSignedFlatInput,ite_true] at he
      dsimp only at hh
      rw [he] at hh
      exact hh)


end
end ASDExplicitGamma.Native
