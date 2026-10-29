module

public import ASDExplicitGamma.Native.ParentRowFlatRootFields
public import ASDExplicitGamma.Native.ParentRowFlatPayment
public import ASDExplicitGamma.Native.ParentRowEnergyPayment
public import ASDExplicitGamma.Native.OldSignedFlatJointL2
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! Actual joint and Dirichlet covariance roots in the certified parent panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The exact joint field is the square root of twice the full variance. -/
theorem parent_row_joint_root_field (j : Fin 16) :
    (parentRowFields j).getD 8 0=Real.sqrt (2*(parentRowFields j).getD 0 0) := by
  have hh := parent_row_flat_root_field j true
  simpa only [ite_true,parentRowFlatRootValue,parent_row_variance_eq] using hh

/-- The exact minus field is the square root of the derivative-only Y clock. -/
theorem parent_row_dirichlet_root_field (j : Fin 16) :
    (parentRowFields j).getD 9 0=Real.sqrt ((parentRowFields j).getD 16 0) := by
  have hh := parent_row_flat_root_field j false
  simpa only [Bool.false_eq_true,ite_false,parentRowFlatRootValue,parent_row_y_eq] using hh

/-- The joint flat covariance root retains sqrt(theta). -/
theorem parent_row_actual_joint_root
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    Real.sqrt (2*parentBoundaryBandVariance M h n (j.val+1))≤
      Real.sqrt (theta M)*(parentRowFields j).getD 8 0 := by
  rw [parent_row_joint_root_field,←Real.sqrt_mul (cold_theta_pos M).le]
  apply Real.sqrt_le_sqrt
  exact (mul_le_mul_of_nonneg_left (parent_row_actual_variance M h hg n hstate j)
    (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

/-- The complete physical Dirichlet root uses Y rather than full variance. -/
theorem parent_row_actual_dirichlet_root
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    Real.sqrt (parentBoundaryBandDirichletEnergy M h n (j.val+1))≤
      Real.sqrt (theta M)*(parentRowFields j).getD 9 0 := by
  rw [parent_row_dirichlet_root_field,←Real.sqrt_mul (cold_theta_pos M).le]
  exact Real.sqrt_le_sqrt (parent_row_actual_dirichlet_energy M h hg n hstate j)

/-- The minus affine means are paid by the exact complete parent Dirichlet
energy after the spatial partition. -/
theorem parent_row_minus_mean_partition (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    descendantsAverage Q r (fun U => oldSignedFlatMeanSize Q U b L false^2)≤
      parentBoundaryDirichletEnergy Q b L := by
  have hh := descendantsAverage_le (fun U hU => pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (old_signed_flat_mean_size_le_l2 Q r b L false U hU) 2)
  apply hh.trans_eq
  rw [old_signed_flat_l2_size_partition,old_signed_flat_l2_size_sq]
  simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode]
  rfl

end
end ASDExplicitGamma.Native
