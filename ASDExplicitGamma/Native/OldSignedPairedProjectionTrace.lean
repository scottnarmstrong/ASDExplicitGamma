module

public import ASDExplicitGamma.Native.OldSignedPairedProjection

/-! Directional paired projection budgets summed over the two orthogonal
loads. Each pair is charged one complete four-load trace average. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- Signed linearity of the actual finite descendant average. -/
theorem old_signed_descendants_average_sub (Q : TriadicCube 2) (depth : ℕ)
    (f g : TriadicCube 2 → ℝ) :
    descendantsAverage Q depth (fun U => f U-g U)=
      descendantsAverage Q depth f-descendantsAverage Q depth g := by
  unfold descendantsAverage
  dsimp only
  rw [Finset.sum_sub_distrib,mul_sub]

/-- The two bottom loads and their reciprocal defects share one trace budget. -/
theorem old_signed_bottom_paired_projection_trace_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ i : Fin 2, (oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k (blockBasis (.inr i))+
      oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k (blockBasis (.inr i)) (blockBasis (.inl i)))) ≤
      lemmaVInverseDepthMax Q a depth * descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  intro a
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    old_signed_paired_projection_exact_bound Q depth nu sigma hnu hsigma k (blockBasis (.inr i)) (blockBasis (.inl i)))
  apply hh.trans_eq
  simp only [blockBasis_pairing,blockMatEntry]
  have hc (i : Fin 2) : blockVecDot (blockBasis (.inr i)) (blockBasis (.inl i)).swap=1 := by
    simp [blockBasis,blockVecDot,vecDot,Pi.single_apply]
  simp_rw [hc]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [← Homogenization.descendantsAverage_sum,← Homogenization.descendantsAverage_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  dsimp only [a]
  simp only [traceDefect,inv_one,one_mul,Matrix.trace,Matrix.diag_apply]
  rw [old_signed_descendants_average_sub,descendantsAverage_add,descendantsAverage_const]
  ring

/-- The two top loads and their reciprocal defects share the same trace budget. -/
theorem old_signed_top_paired_projection_trace_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ i : Fin 2, (oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k (blockBasis (.inl i))+
      oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k (blockBasis (.inl i)) (blockBasis (.inr i)))) ≤
      lemmaVInverseDepthMax Q a depth * descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  intro a
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    old_signed_paired_projection_exact_bound Q depth nu sigma hnu hsigma k (blockBasis (.inl i)) (blockBasis (.inr i)))
  apply hh.trans_eq
  simp only [blockBasis_pairing,blockMatEntry]
  have hc (i : Fin 2) : blockVecDot (blockBasis (.inl i)) (blockBasis (.inr i)).swap=1 := by
    simp [blockBasis,blockVecDot,vecDot,Pi.single_apply]
  simp_rw [hc]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [← Homogenization.descendantsAverage_sum,← Homogenization.descendantsAverage_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  dsimp only [a]
  simp only [traceDefect,inv_one,one_mul,Matrix.trace,Matrix.diag_apply]
  rw [old_signed_descendants_average_sub,descendantsAverage_add,descendantsAverage_const]
  norm_num

end
end ASDExplicitGamma.Native
