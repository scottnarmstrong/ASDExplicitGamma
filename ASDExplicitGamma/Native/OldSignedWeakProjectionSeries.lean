module

public import ASDExplicitGamma.Native.OldSignedPairedProjectionTrace

/-! Complete weak-Haar energy as a summable geometric projection series.
This public form reuses the representation proved for the affine corrector. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Actual square-integrable vector fields have a complete, summable weak
projection representation with the intrinsic quarter-discount weights. -/
theorem old_signed_vector_weak_projection_series
    (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i : Fin 2,
      MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      (∑ i, energy Q (cubeProjection Q j (fun x => F x i)))) ∧
    vectorWeakHaarEnergy Q F =
      (1 - Scalar.inverseHistoryDiscount ^ 2) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          (∑ i, energy Q (cubeProjection Q j (fun x => F x i))) := by
  classical
  let α := Scalar.inverseHistoryDiscount
  have hq : (1 : ℝ) < Real.sqrt 3 := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hBaseSq : Scalar.sourceHaarBase ^ 2 = Real.sqrt 3 := by
    rw [Scalar.sourceHaarBase, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    norm_num
  have hBaseInv : Scalar.sourceHaarBase⁻¹ = α := by
    dsimp [α]
    exact Scalar.inverse_history_discount_eq.symm
  have hInvSqrt : (Real.sqrt 3)⁻¹ = α ^ 2 := by
    have h := congrArg (fun x : ℝ => x⁻¹) hBaseSq
    rw [← inv_pow, hBaseInv] at h
    exact h.symm
  have hCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      ((Real.sqrt 3)⁻¹) ^ j * energy Q (cubeProjection Q j (fun x => F x i))) :=
    summable_weighted_projections Q hq (hF i)
  have hAlphaCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * energy Q (cubeProjection Q j (fun x => F x i))) := by
    simpa only [hInvSqrt, ← pow_mul] using hCoordSummable i
  let e (j : ℕ) := ∑ i, energy Q (cubeProjection Q j (fun x => F x i))
  have hEnergySummable : Summable (fun j : ℕ => α ^ (2 * j) * e j) := by
    simp_rw [e, Finset.mul_sum]
    exact summable_sum fun i hi => hAlphaCoordSummable i
  have hRep : vectorWeakHaarEnergy Q F =
      (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ,
        ((Real.sqrt 3)⁻¹) ^ j *
          (∑ i, energy Q (cubeProjection Q j (fun x => F x i))) := by
    simp_rw [vectorWeakHaarEnergy, dualEnergy_eq Q hq (hF _)]
    rw [← Finset.mul_sum,
      ← Summable.tsum_finsetSum (fun i _ => hCoordSummable i)]
    congr 1
    exact tsum_congr fun j => (Finset.mul_sum _ _ _).symm
  refine ⟨?_, ?_⟩
  · simpa [α, e] using hEnergySummable
  · rw [hRep, hInvSqrt]
    congr 1
    apply tsum_congr
    intro j
    have hpow : (α ^ 2) ^ j = α ^ (2 * j) := by rw [← pow_mul]
    rw [hpow]

end
end ASDExplicitGamma.Native
