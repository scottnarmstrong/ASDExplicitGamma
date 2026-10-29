module

public import ASDExplicitGamma.Native.OldSignedActualMinusMeanProxy
public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! Annealed square-root payment for the actual minus affine covariance means. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The literal covariance-mean proxy is nonnegative samplewise. -/
theorem old_signed_actual_minus_mean_proxy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedActualMinusMeanProxy M n r U hU t b L ω := by
  apply tsum_nonneg
  intro i
  apply Finset.sum_nonneg
  intro c _
  exact (old_signed_directional_proxy_nonneg_le U M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 _ _).1

end
end ASDExplicitGamma.Native
