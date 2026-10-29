module

public import ASDExplicitGamma.Native.OldSignedCovarianceCellMembership
public import ASDExplicitGamma.Native.OldSignedVectorHaarPairing

/-! Joint constant-one cellwise weak/positive covariance pairing. The
actual covariance and old-gradient errors remain on the same cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Aggregate genuine constant-one vector duality over the two load
coordinates without introducing a factor from their count. -/
theorem old_signed_load_haar_pairing_bound (U : TriadicCube 2)
    (r f : Fin 2 → Vec 2 → Vec 2)
    (hr : ∀ i k,MemLp (fun x => r i x k) 2 (normalizedCubeMeasure U))
    (hf : ∀ i k,MemLp (fun x => f i x k) 2 (normalizedCubeMeasure U))
    (hs : ∀ i k,Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => f i x k)))) :
    |∑ i : Fin 2,∑ k : Fin 2,pairing U (fun x => r i x k) (fun x => f i x k)|≤
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (r i)^2)*
        Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U (f i)^2) := by
  have hcs := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i : Fin 2 => sq_nonneg (vectorWeakHaarNorm U (r i)))
    (fun i : Fin 2 => sq_nonneg (vectorPositiveHaarNorm U (f i)))
  have hk i : 0≤vectorWeakHaarNorm U (r i) := Real.sqrt_nonneg _
  have hp i : 0≤vectorPositiveHaarNorm U (f i) := Real.sqrt_nonneg _
  simp_rw [Real.sqrt_sq (hk _),Real.sqrt_sq (hp _)] at hcs
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun i _ => old_signed_vector_haar_pairing_bound U (r i) (f i)
      (hr i) (hf i) (hs i))).trans hcs)

/-- The actual physical covariance field obeys the joint cell pairing
bound. Positive membership is proved from the parent H1 kernel internally. -/
theorem old_signed_covariance_cell_pairing_bound (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (r : Fin 2 → Vec 2 → Vec 2)
    (hr : ∀ i k,MemLp (fun x => r i x k) 2 (normalizedCubeMeasure U)) :
    |∑ i : Fin 2,∑ k : Fin 2,pairing U (fun x => r i x k)
      (fun x => oldSignedRemainderCovarianceField Q b L plus i x k)|≤
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (r i)^2)*
        Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i)^2) :=
  old_signed_load_haar_pairing_bound U r (oldSignedRemainderCovarianceField Q b L plus) hr
    (fun i k => (old_signed_covariance_cell_membership Q U hU b L plus i k).1)
    (fun i k => (old_signed_covariance_cell_membership Q U hU b L plus i k).2)

end
end ASDExplicitGamma.Native
