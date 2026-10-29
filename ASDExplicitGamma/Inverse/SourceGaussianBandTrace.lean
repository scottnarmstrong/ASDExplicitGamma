module

public import ASDExplicitGamma.Gaussian.BandFactor
public import ASDExplicitGamma.Gaussian.CovarianceTrace

/-! Absolute covariance-trace decomposition of a physical finite Gaussian
band. This is the shell-sum adapter for the simultaneous source heat path. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
noncomputable section

/-- The physical band's covariance trace is the finite sum of its shell
traces, with all infinite directional sums absolutely convergent. -/
theorem source_gaussian_band_covariance_trace_sum
    {b : ℕ} [NeZero b] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin b → ℕ → GaussianFactorL2 ℕ)
    (hv : ∀ i, Summable (fun j => ‖v i j‖^2))
    (T : Fin b → GaussianFactorL2 ℕ →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ) (x : E) :
    modelCovarianceTrace Φ (fun j => bandFactor T (bandDirections v j)) x =
      ∑ i, modelCovarianceTrace Φ (fun j => T i (v i j)) x := by
  let B := fderiv ℝ (fderiv ℝ Φ) x
  let H := fun j => bandFactor T (bandDirections v j)
  have hH : Summable (fun j => ‖H j‖^2) :=
    summable_sq_norm_gaussianDirections (bandDirections_summable v hv) (bandFactor T)
  have hs (i : Fin b) : Summable (fun j => B (T i (v i j)) (T i (v i j))) :=
    summable_bilinear_images (summable_sq_norm_gaussianDirections (hv i) (T i)) B
      (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  have hband : Summable (fun j => B (H j) (H j)) :=
    summable_bilinear_images hH B (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  have hp : Summable (fun p : Fin b × ℕ => B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2))) := by
    apply (bandIndex b).summable_iff.mp
    simpa only [Function.comp_def,H,bandDirections,bandFactor_single] using hband
  have hleft : modelCovarianceTrace Φ H x = ∑' j, B (H j) (H j) :=
    modelCovarianceTrace_eq_bilinearTraceMap H hH hΦ x
  have hright (i : Fin b) : modelCovarianceTrace Φ (fun j => T i (v i j)) x =
      ∑' j, B (T i (v i j)) (T i (v i j)) :=
    modelCovarianceTrace_eq_bilinearTraceMap _ (summable_sq_norm_gaussianDirections (hv i) (T i)) hΦ x
  rw [hleft]
  simp_rw [hright]
  simp only [H,bandDirections,bandFactor_single]
  rw [(bandIndex b).tsum_eq (fun p : Fin b × ℕ => B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2))),
    hp.tsum_prod' hs,tsum_fintype]

end
end ASDExplicitGamma.Inverse
