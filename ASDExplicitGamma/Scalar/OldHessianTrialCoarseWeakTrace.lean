module

public import ASDExplicitGamma.Scalar.OldHessianTrialWeakShift
public import ASDExplicitGamma.Native.ParentBoundaryBrokenSeries
public import ASDExplicitGamma.Native.OldSignedAffineCellResidual
public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace

/-! The genuine coarse cell-zero bottom potentials are controlled by the
same fine-depth inverse-weighted trace. Root-zero cancellation is exact. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Triadic Native Inverse Response Variational
noncomputable section

/-- The two bottom canonical first fields have their broken fine weak norm
paid by the shifted physical trace, using the actual paired projection bound. -/
theorem old_hessian_bottom_broken_weak_trace (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q 1 (fun U => ∑ i : Fin 2,vectorWeakHaarEnergy U
      (fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i) x).1)) ≤
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (1+j))
      (fun j => descendantsAverage Q (1+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  let F := fun (i : Fin 2) x =>
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i) x).1
  have hF (i j : Fin 2) : MemLp (fun x => F i x j) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2
        (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i)))) j)
  have hr := parent_boundary_broken_finite_series Q 1 F hF
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have htrace := old_signed_weak_trace_proxy_summable Q a hEll
  have hs : Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      (lemmaVInverseDepthMax Q a (1+j)*descendantsAverage Q (1+j)
        (fun U => traceDefect (openCubeSet U) a 1))) := by
    apply parent_boundary_shifted_summable _ inverse_history_discount_range.1.ne'
      (fun j => lemmaVInverseDepthMax Q a j*descendantsAverage Q j
        (fun U => traceDefect (openCubeSet U) a 1)) 1
    simpa only [mul_assoc] using htrace
  have hdepth (j : ℕ) :
      (∑ i : Fin 2,∑ l : Fin 2,energy Q (cubeProjection Q (1+j) (fun x => F i x l))) ≤
      lemmaVInverseDepthMax Q a (1+j)*descendantsAverage Q (1+j)
        (fun U => traceDefect (openCubeSet U) a 1) := by
    have hh := old_signed_bottom_paired_projection_trace_bound Q (1+j) nu sigma hnu hsigma k
    have hp : (∑ i : Fin 2,oldSignedPrimalProjectionEnergy Q (1+j) nu sigma hnu hsigma k
        (blockBasis (.inr i))) ≤
        ∑ i : Fin 2,(oldSignedPrimalProjectionEnergy Q (1+j) nu sigma hnu hsigma k (blockBasis (.inr i))+
          oldSignedReciprocalProjectionEnergy Q (1+j) nu sigma hnu hsigma k
            (blockBasis (.inr i)) (blockBasis (.inl i))) := by
      apply Finset.sum_le_sum
      intro i _
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun l _ => energy_nonneg Q _)
    apply (le_trans ?_ hp).trans hh
    exact le_of_eq (by simp only [oldSignedPrimalProjectionEnergy,blockBasis,
      Pi.zero_apply,sub_zero,F,basisVec])
  have hc : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  change descendantsAverage Q 1 (fun U => ∑ i : Fin 2,vectorWeakHaarEnergy U (F i)) ≤ _
  rw [hr.2]
  unfold rawWeakTraceProxy
  simp_rw [mul_assoc]
  change (1-inverseHistoryDiscount^2)*(∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      ∑ i : Fin 2,∑ l : Fin 2,energy Q (cubeProjection Q (1+j) (fun x => F i x l))) ≤
    (1-inverseHistoryDiscount^2)*(∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      (lemmaVInverseDepthMax Q a (1+j)*descendantsAverage Q (1+j)
        (fun U => traceDefect (openCubeSet U) a 1)))
  apply mul_le_mul_of_nonneg_left _ hc
  exact hr.1.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hdepth j)
    (pow_nonneg inverse_history_discount_range.1.le _)) hs

/-- The actual coarse cell first potentials, not a substituted parent
potential, retain the alpha² factor against the fine shifted trace. -/
theorem old_hessian_coarse_cell_weak_trace (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let kU := oldSignedCellCoefficient Q U hU k
    let aU := responseFramePlanarCoefficientField nu sigma kU
    (∑ i : Fin 2,vectorWeakHaarEnergy U
      (oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
        (fun _ => (0,basisVec i)) (memLp_const (0,basisVec i))).toH1Function.grad) ≤
      inverseHistoryDiscount^2*rawWeakTraceProxy (fun j => lemmaVInverseDepthMax U aU (1+j))
        (fun j => descendantsAverage U (1+j) (fun V => traceDefect (openCubeSet V) aU 1)) := by
  intro kU aU
  let phi := fun i : Fin 2 => oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
    (fun _ => (0,basisVec i)) (memLp_const (0,basisVec i))
  have hgrad (i : Fin 2) : (phi i).toH1Function.grad=
      (fun x => (oldSignedFrameCanonicalField U nu sigma hnu hsigma kU (0,basisVec i) x).1) := by
    rw [old_signed_cell_first_corrector_grad,old_signed_affine_cell_residual]
    funext x
    exact sub_zero _
  change (∑ i : Fin 2,vectorWeakHaarEnergy U (phi i).toH1Function.grad) ≤ _
  rw [old_hessian_h10_family_weak_shift U phi]
  simp_rw [hgrad]
  exact mul_le_mul_of_nonneg_left
    (old_hessian_bottom_broken_weak_trace U nu sigma hnu hsigma kU) (sq_nonneg _)

end
end ASDExplicitGamma.Scalar
