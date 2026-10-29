module

public import ASDExplicitGamma.Native.OldSignedTiledHistoryPayment
public import ASDExplicitGamma.Native.OldSignedSourceSizeBound

/-! The actual parent and OLD-source energies share one tiled history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Gaussian Algsuperdiff.Section3
noncomputable section

/-- The complete tiled weak proxy is nonnegative. -/
theorem old_signed_actual_tiled_weak_proxy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedActualTiledWeakProxy M n r t ω :=
  mul_nonneg
    (sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le))
    (tsum_nonneg (fun j => old_signed_tiled_history_term_nonneg M n r t ht j ω))

/-- The literal spatial primal, reciprocal and complete OLD-source energies
are bounded by the same physical history. No moment estimate is assumed. -/
theorem old_signed_actual_tiled_profile_bounds (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t : ℝ) (_ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := oldSignedPartialResponseCoefficient n 1 t ω
    let V := fun U => oldSignedPrimalErrorSize Q U M.nu sigma M.nu_pos hsigma k
    let G := fun U => oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos hsigma k
    let d := fun U => oldSignedOldSourceSize Q U r M.nu sigma M.nu_pos hsigma k b L
    descendantsAverage Q r (fun U => V U^2) ≤ oldSignedActualTiledWeakProxy M n r t ω ∧
      descendantsAverage Q r (fun U => V U^2+G U^2) ≤ 2*oldSignedActualTiledWeakProxy M n r t ω ∧
      descendantsAverage Q r (fun U => d U^2) ≤
        oldSignedSourceMultiplier Q r b L^2*oldSignedActualTiledWeakProxy M n r t ω := by
  intro Q sigma hsigma k V G d
  have hv := old_signed_tiled_parent_primal_weak_bound Q r M.nu sigma M.nu_pos hsigma k
  have hvg := old_signed_tiled_parent_paired_weak_bound Q r M.nu sigma M.nu_pos hsigma k
  change descendantsAverage Q r (fun U => V U^2) ≤
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q (oldSignedPartialFrameField M n 1 t ω) (r+j))
      (fun j => descendantsAverage Q (r+j) (fun U => traceDefect (openCubeSet U)
        (oldSignedPartialFrameField M n 1 t ω) 1)) at hv
  change descendantsAverage Q r (fun U => V U^2+G U^2) ≤
    2*rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q (oldSignedPartialFrameField M n 1 t ω) (r+j))
      (fun j => descendantsAverage Q (r+j) (fun U => traceDefect (openCubeSet U)
        (oldSignedPartialFrameField M n 1 t ω) 1)) at hvg
  simp_rw [Q,old_signed_one_shell_trace_depth] at hv hvg
  refine ⟨hv,hvg,?_⟩
  have hd := old_signed_source_size_partition_bound n r M.nu sigma M.nu_pos hsigma k b L
  exact hd.trans (mul_le_mul_of_nonneg_left hv (sq_nonneg _))

end
end ASDExplicitGamma.Native
