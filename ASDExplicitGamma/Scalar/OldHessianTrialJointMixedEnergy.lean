module

public import ASDExplicitGamma.Scalar.OldHessianTrialMixedEnergy
public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski
public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy

/-! Joint bottom-load source budgets. Complete mode sums precede the
finite load aggregation, so the shared weak trace is paid only once. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

theorem old_hessian_coarse_column_bill_nonneg (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    0≤oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k e b L := by
  apply old_signed_cell_average_nonneg
  intro U
  exact mul_nonneg (sq_nonneg _) (vectorWeakHaarEnergy_nonneg U.val _)

/-- The actual mixed gradients also retain their sharper own coarse
trace payment, with the original fine inverse history unchanged. -/
theorem old_hessian_mixed_joint_coarse_trace (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (∑ i : Fin 2,lemmaVTiledWeakEnergy Q fine
      (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad) ≤
      oldHessianFineInverseHistory Q fine nu sigma k*
        descendantsAverage Q coarse (fun U =>
          traceDefect (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k) 1) := by
  have hh := old_hessian_mixed_potential_weak Q coarse fine nu sigma hnu hsigma k
  exact hh.trans (mul_le_mul_of_nonneg_left
    (old_hessian_bottom_patch_trace_bound Q coarse nu sigma hnu hsigma k)
    (old_hessian_fine_history_nonneg Q fine nu sigma k))

/-- The full source family retains its joint load norm, with no load-count
factor in either the fine row or the genuine coarse product. -/
theorem old_hessian_actual_joint_source_energy (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let E := fun (i : Fin 2) (j : whiteBasisIndex) =>
      oldHessianBrokenColumnEnergy Q (coarse+1) (fun _U x =>
        (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L j i x).2)
    (∀ i,Summable (E i)) ∧ Real.sqrt (∑ i : Fin 2,∑' j,E i j) ≤
      oldSignedSourceMultiplier Q (coarse+1) b L*
        Real.sqrt (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
          (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad)+
      Real.sqrt (∑ i : Fin 2,oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L) := by
  intro Q E
  have hs (i : Fin 2) := old_hessian_actual_mixed_source_energy n coarse nu sigma hnu hsigma k b L i
  have hn (i : Fin 2) : 0≤∑' j,E i j := tsum_nonneg (fun j =>
    old_hessian_broken_column_energy_nonneg Q (coarse+1) _)
  have ht := old_signed_finite_sqrt_energy_bound
    (fun i : Fin 2 => lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad)
    (fun i : Fin 2 => oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L)
    (fun i => Real.sqrt (∑' j,E i j))
    (old_hessian_source_multiplier_nonneg Q (coarse+1) b L) (by norm_num : (0:ℝ)≤1)
    (fun i => lemmaVTiledWeakEnergy_nonneg Q (coarse+1) _)
    (fun i => old_hessian_coarse_column_bill_nonneg Q coarse nu sigma hnu hsigma k (basisVec i) b L)
    (fun i => Real.sqrt_nonneg _) (fun i => by simpa only [one_mul] using (hs i).2)
  simp_rw [Real.sq_sqrt (hn _),one_mul] at ht
  exact ⟨fun i => (hs i).1,ht⟩

/-- Both actual projected residuals are controlled by one original fine
history and the joint source-square, before taking any expectation. -/
theorem old_hessian_actual_joint_residual_energy (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let R := fun (i : Fin 2) j => oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L j i
    let C := oldSignedSourceMultiplier Q (coarse+1) b L*
        Real.sqrt (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
          (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad)+
      Real.sqrt (∑ i : Fin 2,oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L)
    (∀ i,Summable (fun j => oldSignedEnergyPairing Q nu sigma k (R i j) (R i j))) ∧
      (∑ i : Fin 2,∑' j,oldSignedEnergyPairing Q nu sigma k (R i j) (R i j)) ≤
        oldHessianFineInverseHistory Q (coarse+1) nu sigma k*C^2 := by
  intro Q R C
  let E := fun (i : Fin 2) (j : whiteBasisIndex) =>
    oldHessianBrokenColumnEnergy Q (coarse+1) (fun _U x =>
      (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L j i x).2)
  let B := oldHessianFineInverseHistory Q (coarse+1) nu sigma k
  have hs := old_hessian_actual_joint_source_energy n coarse nu sigma hnu hsigma k b L
  have hRs (i : Fin 2) := (old_hessian_actual_mixed_residual_energy n coarse nu sigma hnu hsigma k b L i).1
  have hp (i : Fin 2) : (∑' j,oldSignedEnergyPairing Q nu sigma k (R i j) (R i j)) ≤ B*(∑' j,E i j) := by
    have hh := (hRs i).tsum_le_tsum (fun j =>
      old_hessian_actual_mixed_projection_energy n coarse (coarse+1) nu sigma hnu hsigma k b L j i)
      ((hs.1 i).mul_left B)
    rw [tsum_mul_left] at hh
    exact hh
  have hcap := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs.2 2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => tsum_nonneg (fun j =>
    old_hessian_broken_column_energy_nonneg Q (coarse+1) _)))] at hcap
  refine ⟨hRs,?_⟩
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [←Finset.mul_sum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hcap (old_hessian_fine_history_nonneg Q (coarse+1) nu sigma k))

end
end ASDExplicitGamma.Scalar
