module

public import ASDExplicitGamma.Native.OldSignedTiledParentWeak
public import ASDExplicitGamma.Native.OldSignedPrimalTraceGap
public import ASDExplicitGamma.Native.OldSignedPhysicalFluxTrace

/-! Tiled parent primal error with the parent trace term kept. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Generic tiled weak bound with an arbitrary nonnegative depth trace `T`
dominated termwise by the physical trace. -/
theorem old_signed_tiled_weak_trace_bound_anchor {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (mesh : ℕ) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : ι → Vec 2 → Vec 2)
    (hF : ∀ c i, MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q))
    (T : ℕ → ℝ)
    (hT0 : ∀ j, 0 ≤ lemmaVInverseDepthMax Q a (mesh + j) * T j)
    (hTle : ∀ j, T j ≤ descendantsAverage Q (mesh + j)
      (fun U => traceDefect (openCubeSet U) a 1))
    (hb0 : ∀ j, 0 ≤ lemmaVInverseDepthMax Q a (mesh + j))
    (hdepth : ∀ j, (∑ c, ∑ i, energy Q (cubeProjection Q (mesh + j) (fun x => F c x i))) ≤
      lemmaVInverseDepthMax Q a (mesh + j) * T j) :
    descendantsAverage Q mesh (fun U => ∑ c, vectorWeakHaarEnergy U (F c)) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (mesh + j)) T := by
  have hr := old_signed_tiled_weak_projection_series Q mesh F hF
  have hs := old_signed_shifted_weak_trace_proxy_summable Q mesh a hEll
  have hα := inverse_history_discount_range
  have hc : 0 ≤ 1 - inverseHistoryDiscount ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)
  have hsT : Summable (fun j : ℕ => inverseHistoryDiscount ^ (2 * j) *
      lemmaVInverseDepthMax Q a (mesh + j) * T j) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hs
    · have := hT0 j
      have h2 := pow_nonneg hα.1.le (2 * j)
      rw [mul_assoc]; exact mul_nonneg h2 this
    · have := mul_le_mul_of_nonneg_left (hTle j) (hb0 j)
      have h2 := pow_nonneg hα.1.le (2 * j)
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left this h2
  rw [hr.2]
  apply mul_le_mul_of_nonneg_left _ hc
  apply hr.1.tsum_le_tsum _ hsT
  intro j
  have := mul_le_mul_of_nonneg_left (hdepth j) (pow_nonneg hα.1.le (2 * j))
  simpa [mul_assoc] using this

/-- The tiled parent primal error, with the term `traceDefect Q a 1`
subtracted from every depth trace. -/
theorem old_signed_tiled_parent_primal_weak_anchor_bound
    (Q : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q mesh (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k ^ 2) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (mesh + j))
        (fun j => descendantsAverage Q (mesh + j) (fun U => traceDefect (openCubeSet U) a 1) -
          traceDefect (openCubeSet Q) a 1) := by
  intro a
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  simp_rw [old_signed_primal_error_size_sq]
  apply old_signed_tiled_weak_trace_bound_anchor Q mesh a hEll
  · intro c i
    have hm := (memVectorL2_fst_of_memBlockL2
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c)))).sub
      (memVectorL2_const (blockBasis c).1)
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hm i)
  · intro j
    exact mul_nonneg (lemmaVInverseDepthMax_nonneg Q a _)
      (sub_nonneg.mpr (old_signed_parent_trace_le_child Q _ nu sigma hnu hsigma k))
  · intro j
    exact sub_le_self _ (Cold.coarse_square_traceDefect_nonneg Q hEll)
  · intro j
    exact lemmaVInverseDepthMax_nonneg Q a _
  · intro j
    exact old_signed_primal_projection_trace_gap Q (mesh + j) nu sigma hnu hsigma k

end
end ASDExplicitGamma.Native
