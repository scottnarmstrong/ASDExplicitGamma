module

public import ASDExplicitGamma.Native.OldSignedPartitionRowProduct
public import ASDExplicitGamma.Native.OldSignedRemainderCovariance
public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski

/-! AN (2.6) on the actual finite cell partition and complete physical
white family. Joint energies retain the sharp half-boundary normalization. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- The actual two-load covariance bill on the finite descendant partition. -/
def oldSignedPartitionCovarianceBill (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) : ℝ :=
  Real.sqrt (descendantsAverage Q depth (fun U => ∑ a,
    hilbertPositiveHaarNorm U (Real.sqrt 3) (oldSignedRemainderScalarCovariance Q b L plus a)^2))

/-- The complete physical AN (2.6) cell covariance estimate. The sum uses
the same remainders on every cell, rather than re-solving their boundary
problems on the cells. -/
theorem old_signed_partition_covariance_bound (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    oldSignedPartitionCovarianceBill Q depth b L plus≤
      |b| *Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
        (cubeScaleFactor Q/(3:ℝ)^depth)*planarC1*
          (Real.sqrt (mainFlatSigmaSq b L)*Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
            2*|b| *Real.sqrt (mainFlatSigmaSq b L)) := by
  have hsigma : 0≤mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
  have hm x : ‖q3Section b L h3Zero x‖≤|b| := by
    apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg b)).mp
    rw [old_signed_raw_white_norm_sq,sq_abs]
  have hd x : (∑ i,‖(fderiv ℝ (q3Section b L h3Zero) x) (basisVec i)‖^2)≤
      (Real.sqrt (mainFlatSigmaSq b L))^2 := by
    rw [old_signed_white_section_gradient_norm,Real.sq_sqrt hsigma]
  have hh := old_signed_partition_row_h1_product_bound Q depth _
    (old_signed_white_section_contDiff b L) (oldSignedRemainderKernel Q b L plus)
    (abs_nonneg b) (Real.sqrt_nonneg _) hm hd
  rw [old_signed_remainder_kernel_energy] at hh
  have hg := Real.sqrt_le_sqrt (old_signed_remainder_kernel_gradient_bound Q b L plus)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show (4:ℝ)=2^2 by norm_num,
    Real.sqrt_sq (by norm_num : (0:ℝ)≤2)] at hg
  have hR : 0≤(cubeScaleFactor Q/(3:ℝ)^depth)*planarC1*|b| :=
    mul_nonneg (mul_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))
      (Real.sqrt_nonneg _)) (abs_nonneg b)
  exact hh.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hg hR)).trans_eq (by ring))

end
end ASDExplicitGamma.Native
