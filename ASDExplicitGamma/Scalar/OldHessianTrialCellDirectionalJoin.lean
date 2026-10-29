module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectionalTheta
public import ASDExplicitGamma.Scalar.OldHessianTrialTopDirectional

/-! Actual local TOP receivers with uniform deterministic-load payments. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Each genuine fine-cell directional history is bounded by its uniform
integrable grouped proxy, for every fixed deterministic load. -/
theorem old_hessian_actual_cell_directional_proxy_join
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) (e : Vec 2) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let k := oldHessianOldOpenCoefficient (m+129) m ω
      let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
      oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) kU) e≤
        oldHessianCellDirectionalTheta M m U e ω := by
  filter_upwards [old_hessian_actual_depth_blocks_le_bank M h hM hg N hpast m hm,
    (old_hessian_actual_cell_directional_theta M h hM hg N hpast m hm U hU e).1] with ω hb hs
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  let kU := oldSignedCellCoefficient Q U hsub k
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let aU := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) kU
  let p := 1-inverseHistoryDiscount^2
  have hp : 0≤p := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  have hEU := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 kU
  have he := old_signed_cell_frame_coefficient_ae Q U hsub M.nu (Annealed.sigmaBar M m) k
  have hactual := old_signed_directional_proxy_summable U M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 kU e
  have hterm (j : ℕ) : p*(inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax U aU j*
      vecDot e (matVecMul (oldSignedPairedDepthMatrix U j aU) e))≤oldHessianCellDirectionalTerm M m U e j ω := by
    have hInv := old_signed_inverse_depth_congr U j aU a hEU (hEll.mono (measurableSet_openCubeSet U) hsub) he
    have hMat := old_signed_paired_depth_matrix_congr U j aU a he
    rw [hInv,hMat]
    have hbj := hb j 5 (by norm_num) U hU
    norm_num only [inverseBankCap] at hbj
    have hD := (old_hessian_cell_directional_bounds M m U hU j e ω).1
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbj hD)
      (mul_nonneg hp (pow_nonneg inverse_history_discount_range.1.le (2*j)))
    convert hh using 1 <;>
      (dsimp only [oldHessianCellDirectionalTerm,oldHessianCellDepthDirectional,oldHessianLocalDepthRare,p,Q,k,a]; ring)
  have hh := (hactual.mul_left p).tsum_le_tsum hterm hs
  rw [tsum_mul_left] at hh
  exact hh

/-- Genuine TOP first and reciprocal defects on each actual fine cell are
jointly controlled by its uniform directional proxy. -/
theorem old_hessian_actual_cell_top_directional_join
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) (e : Vec 2) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let k := oldHessianOldOpenCoefficient (m+129) m ω
      let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
      let S := oldSignedFrameCanonicalField U M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 kU (e,0)
      let J := oldSignedDualReflection U M.nu (Annealed.sigmaBar M m) kU S
      vectorWeakHaarEnergy U (fun x => (S x).1-e)+vectorWeakHaarEnergy U (fun x => (J x).1)≤
        oldHessianCellDirectionalTheta M m U e ω := by
  filter_upwards [old_hessian_actual_cell_directional_proxy_join M h hM hg N hpast m hm U hU e] with ω hω
  exact (old_hessian_top_directional_weak_bound U M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 _ e).trans hω

end
end ASDExplicitGamma.Scalar
