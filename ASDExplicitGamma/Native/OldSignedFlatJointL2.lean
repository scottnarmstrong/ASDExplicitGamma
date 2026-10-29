module

public import ASDExplicitGamma.Native.OldSignedFlatL2Partition

/-! Exact joint flat L2 energy for the disjoint OLD source families. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main
noncomputable section

/-- The complete flat size squared is its genuine nonnegative energy sum. -/
theorem old_signed_flat_l2_size_sq (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    oldSignedFlatL2Size Q U b L plus^2=
      ∑' n : whiteBasisIndex,∑ i : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus n i) := by
  apply Real.sq_sqrt
  apply tsum_nonneg
  intro n
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => energy_nonneg U _))
    (Finset.sum_nonneg (fun _ _ => energy_nonneg U _))

/-- Exact finite-parent Hodge identity: the joint physical flat covariance
norm is 2v, including the harmonic boundary remainder. -/
theorem old_signed_joint_flat_l2_identity (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    oldSignedFlatL2Size Q Q b L true^2+oldSignedFlatL2Size Q Q b L false^2=2*b^2 := by
  rw [old_signed_flat_l2_size_sq,old_signed_flat_l2_size_sq]
  simp only [oldSignedFlatInput,ite_true,Bool.false_eq_true,ite_false,
    old_signed_flat_plus_l2_mode,old_signed_flat_minus_l2_mode]
  rw [(old_signed_flat_plus_energy_trace Q b L).tsum_eq]
  ring

/-- The complete physical squared flat size partitions exactly. -/
theorem old_signed_flat_l2_size_partition (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    descendantsAverage Q depth (fun U => oldSignedFlatL2Size Q U b L plus^2)=
      oldSignedFlatL2Size Q Q b L plus^2 := by
  let f := fun n (U : OldSignedCellIndex Q depth) => ∑ i : Fin 2,
    oldSignedBlockL2Energy U.val (oldSignedFlatInput Q b L plus n i)
  have hs := old_signed_cell_average_series Q depth f
    (fun U => old_signed_flat_l2_budget_series Q depth b L plus U.val U.property)
  have he (n : whiteBasisIndex) : oldSignedCellAverage Q depth (f n)=
      ∑ i : Fin 2,oldSignedBlockL2Energy Q (oldSignedFlatInput Q b L plus n i) := by
    dsimp only [f]
    rw [old_signed_cell_average_eq_descendantsAverage Q depth (fun U =>
      ∑ i : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus n i))]
    exact (old_signed_flat_l2_mode_partition Q depth b L plus n).symm
  rw [←old_signed_cell_average_eq_descendantsAverage]
  simp_rw [old_signed_flat_l2_size_sq]
  rw [←hs.2]
  simp_rw [he]

/-- The joint affine mean budget under the actual spatial weights is at
most 2v. This retains the exact finite-parent Hodge energy identity. -/
theorem old_signed_joint_flat_mean_partition_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    descendantsAverage Q depth (fun U => oldSignedFlatMeanSize Q U b L true^2+
      oldSignedFlatMeanSize Q U b L false^2)≤2*b^2 := by
  have hh := old_signed_cell_average_mono Q depth (fun U => add_le_add
    (pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (old_signed_flat_mean_size_le_l2 Q depth b L true U.val U.property) 2)
    (pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (old_signed_flat_mean_size_le_l2 Q depth b L false U.val U.property) 2))
  change oldSignedCellAverage Q depth (fun U => oldSignedFlatMeanSize Q U.val b L true^2+
    oldSignedFlatMeanSize Q U.val b L false^2)≤oldSignedCellAverage Q depth
      (fun U => oldSignedFlatL2Size Q U.val b L true^2+oldSignedFlatL2Size Q U.val b L false^2) at hh
  rw [old_signed_cell_average_eq_descendantsAverage Q depth (fun U =>
    oldSignedFlatMeanSize Q U b L true^2+oldSignedFlatMeanSize Q U b L false^2),
    old_signed_cell_average_eq_descendantsAverage Q depth (fun U =>
      oldSignedFlatL2Size Q U b L true^2+oldSignedFlatL2Size Q U b L false^2),descendantsAverage_add Q depth
      (fun U => oldSignedFlatL2Size Q U b L true^2) (fun U => oldSignedFlatL2Size Q U b L false^2),
    old_signed_flat_l2_size_partition,old_signed_flat_l2_size_partition,
    old_signed_joint_flat_l2_identity] at hh
  exact hh

end
end ASDExplicitGamma.Native
