module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseColumnBudget

/-! Joint centered residual-source norm, retaining the actual fine row and
coarse product in the same two-load Euclidean sum. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Summing both bottom loads preserves the exact centered-row coefficient
and the joint genuine coarse-column bill. -/
theorem old_hessian_actual_joint_centered_energy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let ha := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
    let v := fun i : Fin 2 => oldSignedCanonicalFirstCorrector Q a ha (0,basisVec i)
    let phi := fun i : Fin 2 => oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)
    let E := fun (i : Fin 2) j => oldHessianBrokenColumnEnergy Q (coarse+1)
      (fun U => oldHessianCenteredMixedSource Q (coarse+1) b L (v i) (phi i) U j)
    (∀ i,Summable (E i)) ∧ Real.sqrt (∑ i : Fin 2,∑' j,E i j) ≤
      mainQ3RemainderExact (diagMeshRadius Q (coarse+1)) b L.val*
        Real.sqrt (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
          (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad)+
      Real.sqrt (∑ i : Fin 2,oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L) := by
  intro a ha v phi E
  have hs (i : Fin 2) := old_hessian_actual_centered_mixed_energy Q coarse nu sigma hnu hsigma k b L i
  have hn (i : Fin 2) : 0≤∑' j,E i j := tsum_nonneg (fun j =>
    old_hessian_broken_column_energy_nonneg Q (coarse+1) _)
  have hA : 0≤mainQ3RemainderExact (diagMeshRadius Q (coarse+1)) b L.val := by
    have hr := (diagMeshRadius_pos Q (coarse+1)).le
    have hC0 : 0≤planarC0 := Real.sqrt_nonneg _
    have hC1 : 0≤planarC1 := Real.sqrt_nonneg _
    unfold mainQ3RemainderExact
    positivity
  have ht := old_signed_finite_sqrt_energy_bound
    (fun i : Fin 2 => lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad)
    (fun i : Fin 2 => oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L)
    (fun i => Real.sqrt (∑' j,E i j)) hA (by norm_num : (0:ℝ)≤1)
    (fun i => lemmaVTiledWeakEnergy_nonneg Q (coarse+1) _)
    (fun i => old_hessian_coarse_column_bill_nonneg Q coarse nu sigma hnu hsigma k (basisVec i) b L)
    (fun i => Real.sqrt_nonneg _) (fun i => by rw [one_mul]; exact (hs i).2)
  simp_rw [Real.sq_sqrt (hn _),one_mul] at ht
  exact ⟨fun i => (hs i).1,ht⟩

end
end ASDExplicitGamma.Scalar
