module

public import ASDExplicitGamma.Native.OldSignedCovarianceCellPairing

/-! Exact partition and joint cell bounds for the covariance pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual scalar L2 pairing is the exact descendant average. -/
theorem old_signed_pairing_partition (Q : TriadicCube 2) (j : ℕ) (f g : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q f g=descendantsAverage Q j (fun U => pairing U f g) := by
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _
    (integrableOn_of_integrable_normalizedCubeMeasure Q (hf.integrable_mul hg))

/-- Absolute value may be taken after exact finite cell averaging. -/
theorem old_signed_abs_descendant_average_le (Q : TriadicCube 2) (j : ℕ)
    (f : TriadicCube 2 → ℝ) :
    |descendantsAverage Q j f|≤descendantsAverage Q j (fun U => |f U|) := by
  classical
  unfold descendantsAverage
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- Joint covariance pairing is bounded cellwise by beta times the local
weak error. This retains the actual old error and covariance on the same
cell; no independence or maximum replaces their product. -/
theorem old_signed_covariance_partition_pairing_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (r : Fin 2 → Vec 2 → Vec 2)
    (hr : ∀ i k,MemLp (fun x => r i x k) 2 (normalizedCubeMeasure Q)) :
    |∑ i : Fin 2,∑ k : Fin 2,pairing Q (fun x => r i x k)
      (fun x => oldSignedRemainderCovarianceField Q b L plus i x k)|≤
      descendantsAverage Q depth (fun U =>
        Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (r i)^2)*
          Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U
            (oldSignedRemainderCovarianceField Q b L plus i)^2)) := by
  classical
  have he i k := old_signed_pairing_partition Q depth (fun x => r i x k)
    (fun x => oldSignedRemainderCovarianceField Q b L plus i x k) (hr i k)
    (old_signed_covariance_cell_membership Q Q (Set.Subset.refl _) b L plus i k).1
  have hsum : (∑ i : Fin 2,∑ k : Fin 2,pairing Q (fun x => r i x k)
      (fun x => oldSignedRemainderCovarianceField Q b L plus i x k))=
      descendantsAverage Q depth (fun U => ∑ i : Fin 2,∑ k : Fin 2,
        pairing U (fun x => r i x k) (fun x => oldSignedRemainderCovarianceField Q b L plus i x k)) := by
    simp_rw [he]
    simp_rw [Homogenization.descendantsAverage_sum Q depth Finset.univ]
  rw [hsum]
  apply (old_signed_abs_descendant_average_le Q depth _).trans
  apply descendantsAverage_le_descendantsAverage
  intro U hU
  exact old_signed_covariance_cell_pairing_bound Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) b L plus r
    (fun i k => hilbert_memLp_descendant hU (hr i k))

end
end ASDExplicitGamma.Native
