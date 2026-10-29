module

public import ASDExplicitGamma.Native.ParentHistoryRestoration
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! Exact source endpoint envelope for the actual complete physical history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Literal source HH envelope after the centered-history drift and sharp
Gaussian/rare inverse restoration, with the original reserve unchanged. -/
def parentHistorySourceEnvelope (height r : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt ((3:ℝ)^((3:ℝ)*(r:ℝ)/20)+t*parentBoundaryCommonSourceDelta gammaZero height r)+
    Real.sqrt (2*t*parentBoundaryCommonSourceVariance gammaZero height)*
      ((3:ℝ)^((1:ℝ)/4)*Real.sqrt (3683/2500:ℝ)+
        (105:ℝ)^((1:ℝ)/8)*Real.sqrt (3/10^46:ℝ)))^2

/-- The actual common-center variance retains one exact source theta. -/
theorem parent_history_band_variance_theta
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (height : ℕ) :
    parentBoundaryCommonBandVariance M h n height ≤
      theta M*parentBoundaryCommonSourceVariance gammaZero height := by
  have he : parentBoundaryCommonBandVariance M h n height=parentBoundaryBandVariance M h n height := by
    unfold parentBoundaryCommonBandVariance parentBoundaryBandVariance
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have hi : nativeSourceBandIndex n height i=n+((i.val+1:ℕ):ℤ) := by
      dsimp only [nativeSourceBandIndex]
      push_cast
      ring
    rw [hi,div_pow]
  rw [he]
  exact (parent_boundary_band_variance_clock M h n height hstate).trans
    (parent_boundary_common_source_variance_theta M hg height)

/-- The COMPLETE actual physical L2 history has the source HH envelope
with exactly one theta. This is the direct source consumer for the
boundary-fixed OLD parent row; no history estimate is an assumption. -/
theorem parent_history_physical_endpoint_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (parentBoundaryBandMaxTraceHistory M n height P t) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*parentHistorySourceEnvelope height r t) := by
  let U := (3:ℝ)^((3:ℝ)*(r:ℝ)/20)+t*parentBoundaryCommonSourceDelta gammaZero height r
  let K := (3:ℝ)^((1:ℝ)/4)*Real.sqrt (3683/2500:ℝ)+
    (105:ℝ)^((1:ℝ)/8)*Real.sqrt (3/10^46:ℝ)
  let V := parentBoundaryCommonBandVariance M h n height
  let V0 := parentBoundaryCommonSourceVariance gammaZero height
  let H := eLpNorm (parentBoundaryCommonCenteredMaxHistory M P n height t) 20 (Cutoff.cutoffSampleLaw M).toMeasure
  have htheta := (cold_theta_pos M).le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hU : 0 ≤ U := by
    have hd := parent_boundary_common_source_delta_nonneg gammaZero (by norm_num [gammaZero]) le_rfl height r
    dsimp only [U]
    positivity
  have hC := parent_boundary_common_centered_history_endpoint_L20 M h hM hg P n r hr hP hstate height hheight hpast t ht0 ht1
  have hCreal : H.toReal ≤ theta M*U := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hC).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg htheta hU))
  have hV := parent_history_band_variance_theta M h hg n hstate height
  have hVroot : Real.sqrt (2*t*V) ≤ Real.sqrt (theta M)*Real.sqrt (2*t*V0) := by
    have hscaled := mul_le_mul_of_nonneg_left hV (mul_nonneg (by norm_num : (0:ℝ)≤2) ht0)
    have he : (2*t)*(theta M*V0)=theta M*(2*t*V0) := by ring
    exact (Real.sqrt_le_sqrt (hscaled.trans_eq he)).trans_eq (Real.sqrt_mul htheta _)
  have hCroot : Real.sqrt H.toReal ≤ Real.sqrt (theta M)*Real.sqrt U :=
    (Real.sqrt_le_sqrt hCreal).trans_eq (Real.sqrt_mul htheta _)
  have hsum : Real.sqrt H.toReal+Real.sqrt (2*t*V)*K ≤
      Real.sqrt (theta M)*(Real.sqrt U+Real.sqrt (2*t*V0)*K) :=
    (add_le_add hCroot (mul_le_mul_of_nonneg_right hVroot hK)).trans_eq (by ring)
  have hleft0 : 0 ≤ Real.sqrt H.toReal+Real.sqrt (2*t*V)*K := by positivity
  have hsquare := pow_le_pow_left₀ hleft0 hsum 2
  have hrestore := parent_history_physical_restore M h hM hg P n r hr hP height hheight hpast t ht0 ht1
  apply hrestore.trans (ENNReal.ofReal_le_ofReal (hsquare.trans_eq ?_))
  rw [mul_pow,Real.sq_sqrt htheta]
  rfl

end
end ASDExplicitGamma.Native
