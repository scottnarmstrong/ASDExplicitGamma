module

public import ASDExplicitGamma.Native.ParentBoundaryCommonSpatialClock
public import ASDExplicitGamma.Inverse.SourceQ3Drift

/-! Exact source mean-generator geometry at the whole-parent observation scale. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Every shell fresh above the source offset5 uses the whole observation
square as its source tiling. -/
theorem parent_boundary_mean_source_depth_zero (s : ℕ) (hs : 5 ≤ s) :
    pureFluxBankSourceDepth s=0 := by unfold pureFluxBankSourceDepth; omega

/-- The source stationary A-column is exactly the already-proved physical
common-center coefficient on its own observation square. -/
theorem parent_boundary_mean_own_row_scale (q : ℤ) (s : ℕ) (hs : 5 ≤ s) (b : ℝ) :
    parentBoundaryCommonRowCoefficient (originCube 2 q) (originCube 2 q) b
      (q3ModelLength (q+(s:ℤ))) 0=|b| *pureFluxCovarianceA 0 (s-1) := by
  have hs1 : 1 ≤ s := by omega
  have hr := pureFlux_bank_source_rho q s hs1
  have hd := pureFlux_bank_source_delta q s hs1
  rw [parent_boundary_mean_source_depth_zero s hs] at hd
  simp only [diagMeshRadius,pow_zero,div_one] at hd
  have he : pureFluxCovarianceDelta 0 (s-1)=pureFluxCovarianceRho 0 (s-1) := hd.symm.trans hr
  rw [parent_boundary_common_row_coefficient_shape,hr]
  unfold pureFluxCovarianceA pureFluxCovarianceAr pureFluxCovarianceBA pureFluxCovarianceCA
  rw [he]
  norm_num only [show (78/5:ℝ)/2=39/5 by norm_num,
    show (2:ℝ)*(78/5)=156/5 by norm_num,
    show (2:ℝ)*((3432/5)+(78/5)^2)=46488/25 by norm_num]

/-- The physical mean covariance coefficient has the source1.856 A-column
bound, before any annealed bank or numerical estimate is inserted. -/
theorem parent_boundary_mean_mu_row (q : ℤ) (s : ℕ) (hs : 5 ≤ s) (b sigma : ℝ) :
    (b^2/sigma^2)*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1)) ≤
      (232/125:ℝ)*(parentBoundaryCommonRowCoefficient (originCube 2 q) (originCube 2 q)
        (b/sigma) (q3ModelLength (q+(s:ℤ))) 0)^2 := by
  have hr := pureFlux_covariance_rows_order 0 (s-1)
  have hmu := parent_boundary_common_covariance_mu_cap _ _ hr.1 hr.2
  apply (mul_le_mul_of_nonneg_left hmu (div_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq
  rw [parent_boundary_mean_own_row_scale q s hs,mul_pow,sq_abs,div_pow]
  ring

/-- The source deterministic mixed direction has the exact whole-square
second-moment coefficient. -/
theorem parent_boundary_mean_kn_shape (rho : ℝ) :
    lemmaVH2kn rho rho=(78/5:ℝ)*rho^2*((1/4:ℝ)+(36/25:ℝ)/Real.sqrt 2+(57/200:ℝ)*Real.sqrt 2) := by
  unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
  ring

/-- Complete finite mixed-direction summation is the actual normalized
second spatial clock, retaining all individual shell amplitudes. -/
theorem parent_boundary_mean_kn_sum
    (M : ABKModel 2) (h : ℝ) (P : TriadicCube 2) (n : ℤ) (height : ℕ) :
    (∑ i : Fin height,(q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2*
      lemmaVH2kn (cubeScaleFactor P/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
        (cubeScaleFactor P/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val))=
      ((78/5:ℝ)*((1/4:ℝ)+(36/25:ℝ)/Real.sqrt 2+(57/200:ℝ)*Real.sqrt 2))*
        parentBoundaryCommonSpatialClock M h P n height 2 := by
  simp_rw [parent_boundary_mean_kn_shape]
  unfold parentBoundaryCommonSpatialClock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end ASDExplicitGamma.Native
