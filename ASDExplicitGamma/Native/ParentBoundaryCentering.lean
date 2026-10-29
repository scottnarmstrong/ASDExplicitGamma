module

public import ASDExplicitGamma.Native.OldSignedFlatCovarianceFeedback
public import ASDExplicitGamma.Triadic.DiagBessel

/-! Center the actual complete flat covariance before estimating its pairing.
The deterministic parent mean is retained as a matrix, so no unproved
isotropy identification or small covariance cap is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- Actual parent mean of the complete finite-square flat contraction. -/
def parentBoundaryFlatMean (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i k : Fin 2) : ℝ :=
  -(b^2/2)*(if k=i then 1 else 0) +
    ∫ x,oldSignedRemainderCovarianceField Q b L plus i x k ∂normalizedCubeMeasure Q

/-- Centering the full flat contraction cancels its whole-plane constant
and subtracts the actual parent mean of its remainder. -/
def parentBoundaryCenteredCovariance (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i : Fin 2) (x : Vec 2) : Vec 2 :=
  fun k => oldSignedRemainderCovarianceField Q b L plus i x k -
    ∫ y,oldSignedRemainderCovarianceField Q b L plus i y k ∂normalizedCubeMeasure Q

/-- The centered physical covariance is L2 and positive-Haar on every
fine cell; subtracting a parent constant preserves all positive increments. -/
theorem parent_boundary_centered_membership (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (i k : Fin 2) :
    MemLp (fun x => parentBoundaryCenteredCovariance Q b L plus i x k)
      2 (normalizedCubeMeasure U) ∧
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => parentBoundaryCenteredCovariance Q b L plus i x k))) := by
  have hs := old_signed_covariance_cell_membership Q U hU b L plus i k
  refine ⟨hs.1.sub (memLp_const _),?_⟩
  unfold parentBoundaryCenteredCovariance
  simp_rw [diagIncrement_succ_sub_const U _ hs.1]
  exact hs.2

/-- Exact complete mode contraction with an arbitrary L2 physical test.
The parent mean is separated before any absolute value or norm bound. -/
theorem parent_boundary_centered_flat_integral (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i k : Fin 2)
    (r : Vec 2 → ℝ) (hr : MemLp r 2 (normalizedCubeMeasure Q)) :
    HasSum (fun n : whiteBasisIndex => ∫ x,r x*
      q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => oldSignedFlatCoordinate Q b L plus n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      (parentBoundaryFlatMean Q b L plus i k *
        (∫ x,r x ∂normalizedCubeMeasure Q) +
        ∫ x,r x*parentBoundaryCenteredCovariance Q b L plus i x k
          ∂normalizedCubeMeasure Q) := by
  have hs := old_signed_flat_covariance_integral Q b L plus i k r hr
  have hm := (old_signed_covariance_cell_membership Q Q (Set.Subset.refl _) b L plus i k).1
  have he : (∫ x,r x*parentBoundaryCenteredCovariance Q b L plus i x k
      ∂normalizedCubeMeasure Q) =
      (∫ x,r x*oldSignedRemainderCovarianceField Q b L plus i x k ∂normalizedCubeMeasure Q) -
        (∫ x,r x ∂normalizedCubeMeasure Q)*
          (∫ x,oldSignedRemainderCovarianceField Q b L plus i x k ∂normalizedCubeMeasure Q) := by
    simp only [parentBoundaryCenteredCovariance,mul_sub]
    have hi : Integrable (fun x => r x*oldSignedRemainderCovarianceField Q b L plus i x k)
        (normalizedCubeMeasure Q) := hr.integrable_mul hm
    rw [integral_sub hi ((hr.integrable one_le_two).mul_const
        (∫ x,oldSignedRemainderCovarianceField Q b L plus i x k ∂normalizedCubeMeasure Q)),
      integral_mul_const]
  convert hs using 1
  rw [he]
  unfold parentBoundaryFlatMean
  ring

/-- Two-load positive-Haar size of the actual centered covariance. -/
def parentBoundaryCenteredBeta (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U
    (parentBoundaryCenteredCovariance Q b L plus i)^2)

/-- The centered covariance pairs jointly with the SAME actual local
errors, with constant one and no independence assertion. -/
theorem parent_boundary_centered_partition_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (r : Fin 2 → Vec 2 → Vec 2)
    (hr : ∀ i k,MemLp (fun x => r i x k) 2 (normalizedCubeMeasure Q)) :
    |∑ i : Fin 2,∑ k : Fin 2,pairing Q (fun x => r i x k)
      (fun x => parentBoundaryCenteredCovariance Q b L plus i x k)| ≤
      descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L plus *
        Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (r i)^2)) := by
  classical
  have he i k := old_signed_pairing_partition Q depth (fun x => r i x k)
    (fun x => parentBoundaryCenteredCovariance Q b L plus i x k) (hr i k)
    (parent_boundary_centered_membership Q Q (Set.Subset.refl _) b L plus i k).1
  have hsum : (∑ i : Fin 2,∑ k : Fin 2,pairing Q (fun x => r i x k)
      (fun x => parentBoundaryCenteredCovariance Q b L plus i x k)) =
      descendantsAverage Q depth (fun U => ∑ i : Fin 2,∑ k : Fin 2,
        pairing U (fun x => r i x k)
          (fun x => parentBoundaryCenteredCovariance Q b L plus i x k)) := by
    simp_rw [he]
    simp_rw [Homogenization.descendantsAverage_sum Q depth Finset.univ]
  rw [hsum]
  apply (old_signed_abs_descendant_average_le Q depth _).trans
  apply descendantsAverage_le_descendantsAverage
  intro U hU
  have hh := old_signed_load_haar_pairing_bound U r
    (parentBoundaryCenteredCovariance Q b L plus)
    (fun i k => hilbert_memLp_descendant hU (hr i k))
    (fun i k => (parent_boundary_centered_membership Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) b L plus i k).1)
    (fun i k => (parent_boundary_centered_membership Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) b L plus i k).2)
  exact hh.trans_eq (mul_comm _ _)

end
end ASDExplicitGamma.Native
