module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredMinusEnergy
public import ASDExplicitGamma.Scalar.OldHessianTrialWhiteMeanVariance
public import ASDExplicitGamma.Native.OldSignedDescendantMinkowski

/-! Exact joint Frobenius covariance bill over all fine cells and loads.
The boundary term costs Bflat/2 and the oscillation keeps the sharp pi. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Actual deterministic two-load covariance-error energy on one cell. -/
def oldHessianCovarianceErrorCellEnergy (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) : ℝ :=
  ∑ i : Fin 2,∑ k : Fin 2,(oldHessianMeanCovarianceError Q U b L k i)^2

/-- Joint four-coordinate bill, without a coordinate-count loss. -/
theorem old_hessian_covariance_error_cell_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) :
    Real.sqrt (oldHessianCovarianceErrorCellEnergy Q U b L) ≤
      |b| * Real.sqrt (∑ i : Fin 2,∑ k : Fin 2,
        hilbertEnergy U (oldSignedRemainderKernel Q b L false (i,k)).toFun)+
      (cubeScaleFactor U/Real.pi)*Real.sqrt (mainFlatSigmaSq b L)*
        Real.sqrt (∑ i : Fin 2,∑ k : Fin 2,hilbertEnergy U (fun x =>
          (oldHessianMinusKernel Q b L i k).toFun x-
            hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)) := by
  let C := (cubeScaleFactor U/Real.pi)*Real.sqrt (mainFlatSigmaSq b L)
  have hC : 0≤C := mul_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' U).le Real.pi_pos.le)
    (Real.sqrt_nonneg _)
  have hv := Real.sqrt_le_sqrt (old_hessian_white_mean_variance U b L)
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq
    (div_nonneg (Triadic.cubeScaleFactor_pos' U).le Real.pi_pos.le)] at hv
  have hh := old_signed_finite_sqrt_energy_bound
    (fun a : Fin 2 × Fin 2 => hilbertEnergy U (oldSignedRemainderKernel Q b L false a).toFun)
    (fun a : Fin 2 × Fin 2 => hilbertEnergy U (fun x =>
      (oldHessianMinusKernel Q b L a.1 a.2).toFun x-
        hilbertCubeAverage U (oldHessianMinusKernel Q b L a.1 a.2).toFun))
    (fun a : Fin 2 × Fin 2 => |oldHessianMeanCovarianceError Q U b L a.2 a.1|)
    (abs_nonneg b) hC (fun a => hilbertEnergy_nonneg U _) (fun a => hilbertEnergy_nonneg U _)
    (fun a => abs_nonneg _) (fun a =>
      (old_hessian_frozen_covariance_error_entry_bound Q depth b L U hU a.1 a.2).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hv (Real.sqrt_nonneg _))))
  simpa only [oldHessianCovarianceErrorCellEnergy,Fintype.sum_prod_type,sq_abs] using hh

/-- The actual full harmonic kernel energy partitions to precisely half
Bflat, before any source tail or outward numerical cap is used. -/
theorem old_hessian_boundary_kernel_partition (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    descendantsAverage Q depth (fun U => ∑ i : Fin 2,∑ k : Fin 2,
      hilbertEnergy U (oldSignedRemainderKernel Q b L false (i,k)).toFun)=
        oldSignedFlatBoundaryEnergy Q b L/2 := by
  calc
    _ = ∑ i : Fin 2,∑ k : Fin 2,hilbertEnergy Q
        (oldSignedRemainderKernel Q b L false (i,k)).toFun := by
      simp_rw [Homogenization.descendantsAverage_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact (hilbertEnergy_eq_descendantsAverage Q depth
        ((oldSignedRemainderKernel Q b L false (i,k)).memL2_normalized Q)).symm
    _ = _ := by simpa only [Fintype.sum_prod_type] using old_signed_remainder_kernel_energy Q b L false

/-- The full actual frozen covariance error has the source's joint
boundary-plus-oscillation Frobenius bound, with no extra load factor. -/
theorem old_hessian_covariance_error_frobenius (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Real.sqrt (descendantsAverage Q depth (fun U => oldHessianCovarianceErrorCellEnergy Q U b L)) ≤
      |b| * Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
      (cubeScaleFactor Q/(3:ℝ)^depth/Real.pi)*Real.sqrt (mainFlatSigmaSq b L)*
        Real.sqrt (descendantsAverage Q depth (fun U => oldSignedFlatOscillationSize Q U b L false^2)) := by
  let E := fun U => ∑ i : Fin 2,∑ k : Fin 2,hilbertEnergy U (oldSignedRemainderKernel Q b L false (i,k)).toFun
  let G := fun U => ∑ i : Fin 2,∑ k : Fin 2,hilbertEnergy U (fun x =>
    (oldHessianMinusKernel Q b L i k).toFun x-hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)
  let c := fun U => Real.sqrt (oldHessianCovarianceErrorCellEnergy Q U b L)
  let C := (cubeScaleFactor Q/(3:ℝ)^depth/Real.pi)*Real.sqrt (mainFlatSigmaSq b L)
  have hC : 0≤C := mul_nonneg
    (div_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (pow_nonneg (by norm_num : (0:ℝ)≤3) depth)) Real.pi_pos.le)
    (Real.sqrt_nonneg _)
  have hc (U : TriadicCube 2) : 0≤oldHessianCovarianceErrorCellEnergy Q U b L :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hh := old_signed_descendant_sqrt_energy_bound Q depth E G c (abs_nonneg b) hC
    (fun U _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg U _)))
    (fun U _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg U _)))
    (fun U _ => Real.sqrt_nonneg _) (fun U hU => by
      have ht := old_hessian_covariance_error_cell_bound Q depth b L U hU
      rw [cubeScaleFactor_descendant_eq_div_pow hU] at ht
      exact ht)
  simp only [c,Real.sq_sqrt (hc _)] at hh
  rw [old_hessian_boundary_kernel_partition] at hh
  have hg : descendantsAverage Q depth G ≤
      descendantsAverage Q depth (fun U => oldSignedFlatOscillationSize Q U b L false^2) :=
    descendantsAverage_le (fun U hU => old_hessian_centered_minus_kernel_energy Q depth b L U hU)
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) hC))

end
end ASDExplicitGamma.Scalar
