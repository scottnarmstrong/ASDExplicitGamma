module

public import ASDExplicitGamma.Native.OldSignedWeakProjectionSeries
public import ASDExplicitGamma.Native.OldSignedHistoryBounds
public import ASDExplicitGamma.Cold.CoarseGramDefect

/-! The complete paired trace proxy is a genuine convergent real series
for each physical uniformly elliptic response coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- No infinite inverse-weighted trace tail is hidden by a real-valued sum. -/
theorem old_signed_weak_trace_proxy_summable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax Q a j*
      descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hα := inverse_history_discount_range
  have hT (j : ℕ) : 0 ≤ descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1) := by
    apply descendantsAverage_nonneg
    intro U hU
    exact Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  have hs := (old_signed_trace_depth_series_summable Q a hEll).mul_left (4*2*lam⁻¹)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg hα.1.le _) (lemmaVInverseDepthMax_nonneg Q a j))
      (hT j)
  · intro j
    have hp : inverseHistoryDiscount^(2*j) ≤ inverseHistoryDiscount^j := by
      exact pow_le_pow_of_le_one hα.1.le hα.2.le (by omega)
    have hm := mul_le_mul hp (lemmaVInverseDepthMax_le_uniform Q hEll j)
      (lemmaVInverseDepthMax_nonneg Q a j) (pow_nonneg hα.1.le j)
    have ht := mul_le_mul_of_nonneg_right hm (hT j)
    exact ht.trans_eq (by simp only [Fintype.card_fin]; ring)

/-- A finite family of actual weak-Haar energies is its complete projection
series. Summability precedes every finite/infinite interchange. -/
theorem old_signed_finite_weak_projection_series {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (F : ι → Vec 2 → Vec 2)
    (hF : ∀ c i,MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      ∑ c,∑ i,energy Q (cubeProjection Q j (fun x => F c x i))) ∧
    (∑ c,vectorWeakHaarEnergy Q (F c))=(1-inverseHistoryDiscount^2)*
      ∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        ∑ c,∑ i,energy Q (cubeProjection Q j (fun x => F c x i)) := by
  classical
  have hs (c : ι) := old_signed_vector_weak_projection_series Q (F c) (hF c)
  constructor
  · simp_rw [Finset.mul_sum]
    exact summable_sum (fun c _ => by simpa only [Finset.mul_sum] using (hs c).1)
  · simp_rw [(fun c => (hs c).2)]
    rw [← Finset.mul_sum,← Summable.tsum_finsetSum (fun c _ => (hs c).1)]
    congr 1
    exact tsum_congr (fun j => (Finset.mul_sum _ _ _).symm)

end
end ASDExplicitGamma.Native
