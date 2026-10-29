module

public import ASDExplicitGamma.Native.OldSignedFlatJointL2
public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceVector
public import ASDExplicitGamma.Native.OldSignedFlatCovarianceFeedback

/-! Deterministic flat and covariance profiles for the actual OLD partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Variational
noncomputable section

/-- Actual flat harmonic energy is nonnegative and at most twice the variance. -/
theorem old_signed_flat_boundary_energy_bounds (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    0≤oldSignedFlatBoundaryEnergy Q b L ∧ oldSignedFlatBoundaryEnergy Q b L≤2*b^2 := by
  refine ⟨tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun k _ => energy_nonneg Q _))),?_⟩
  rw [oldSignedFlatBoundaryEnergy,(old_signed_flat_boundary_energy_trace Q b L).tsum_eq]
  have hn : 0≤∑' n,oldSignedFlatDirichletModeEnergy Q b L n :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _)))
  linarith only [hn]

/-- The minus flat L2 energy is at most one variance, by its exact remainder. -/
theorem old_signed_flat_minus_l2_cap (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) : oldSignedFlatL2Size Q Q b L false^2≤b^2 := by
  rw [old_signed_flat_l2_size_sq]
  simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode]
  have hr : 0≤∑' n,oldSignedFlatMinusRemainderModeEnergy Q b L n :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _)))
  rw [(old_signed_flat_minus_complete_energy Q b L).2.2.tsum_eq] at hr
  exact sub_nonneg.mp hr

/-- The entire spatial minus flat energy is bounded by one variance. -/
theorem old_signed_flat_minus_partition_l2_cap (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    descendantsAverage Q r (fun U => oldSignedFlatL2Size Q U b L false^2)≤b^2 := by
  rw [old_signed_flat_l2_size_partition]
  exact old_signed_flat_minus_l2_cap Q b L

/-- The covariance beta is paid after the full spatial contraction; it does
not require any false pointwise boundary energy cap on individual cells. -/
theorem old_signed_covariance_beta_partition_cap (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    Real.sqrt (descendantsAverage Q r (fun U => oldSignedCovarianceBeta Q U b L plus^2))≤
      b^2+3*(cubeScaleFactor Q/(3:ℝ)^r)*planarC1* |b| *Real.sqrt (mainFlatSigmaSq b L) := by
  have hs (U : TriadicCube 2) : oldSignedCovarianceBeta Q U b L plus^2=
      ∑ i : Fin 2,vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  simp_rw [hs]
  have hh := old_signed_covariance_beta_bound Q r b L plus
  have hb : Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)≤|b| := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨abs_nonneg _,?_⟩
    rw [sq_abs]
    linarith only [(old_signed_flat_boundary_energy_bounds Q b L).2]
  have hc : 0≤(cubeScaleFactor Q/(3:ℝ)^r)*planarC1 :=
    mul_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity)) (Real.sqrt_nonneg _)
  apply hh.trans
  calc
    _ ≤ |b| * |b| +(cubeScaleFactor Q/(3:ℝ)^r)*planarC1*
        (Real.sqrt (mainFlatSigmaSq b L)* |b| +2* |b| *Real.sqrt (mainFlatSigmaSq b L)) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg b))
        (mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)) le_rfl) hc)
    _ = _ := by rw [←sq_abs b]; ring

end
end ASDExplicitGamma.Native
