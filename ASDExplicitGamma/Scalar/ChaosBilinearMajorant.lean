module

public import ASDExplicitGamma.Scalar.ChaosBilinearCutoff
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! An integrable source majorant for the infinite Gaussian quadratic-envelope passage. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance instChaosInfiniteGaussianProbability : IsProbabilityMeasure Gaussian.standardGaussianInfinitePi := by
  unfold Gaussian.standardGaussianInfinitePi
  infer_instance

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The operator norm appearing in the source bilinear estimate is nonnegative. -/
theorem gaussian_bilinear_opNorm_nonnegative (B : V →L[ℝ] V →L[ℝ] W) : 0≤‖B‖ := by
  convert norm_nonneg B using 1

/-- A deterministic polynomial in the existing Gaussian fast-subsequence envelope. -/
noncomputable def gaussianBilinearMajorant (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) (omega : ℕ → ℝ) : ℝ :=
  ‖m‖+‖B‖*(Gaussian.gaussianFastEnvelope hA omega)^2+‖B‖*(∑' i,‖v i‖^2)

/-- The majorant has the fourth moment needed to dominate the squared envelope. -/
theorem memLp_gaussian_bilinear_majorant [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V]
    (m : W) (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    MemLp (gaussianBilinearMajorant m B v hA) 4 Gaussian.standardGaussianInfinitePi := by
  have hE : MemLp (Gaussian.gaussianFastEnvelope hA) 8 Gaussian.standardGaussianInfinitePi := by
    convert Gaussian.memLp_gaussianFastEnvelope hA (p := 8) (by norm_num) using 1
    norm_num
  have hE2 := hE.norm_rpow_div 2
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
    show (8:ℝ≥0∞)/2=4 by
      symm
      apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
      norm_num] at hE2
  have h := ((memLp_const ‖m‖).add (hE2.const_mul ‖B‖)).add (memLp_const (‖B‖*(∑' i,‖v i‖^2)))
  unfold gaussianBilinearMajorant
  convert h using 1

/-- The actual centered quadratic cutoffs are dominated uniformly by this majorant. -/
theorem ae_gaussian_bilinear_partial_le_majorant [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V]
    (m : W) (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    ∀ᵐ omega ∂Gaussian.standardGaussianInfinitePi,∀ k,
      ‖m+gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega‖≤
        gaussianBilinearMajorant m B v hA omega := by
  filter_upwards [Gaussian.ae_norm_gaussianFastPartialSum_le_envelope hA] with omega henv
  intro k
  let X := Gaussian.gaussianPartialSum v (Gaussian.gaussianFastIndex hA k) omega
  have hX : ‖X‖≤Gaussian.gaussianFastEnvelope hA omega := henv k
  have hbil : ‖B X X‖≤‖B‖*(Gaussian.gaussianFastEnvelope hA omega)^2 := by
    have h := B.le_opNorm₂ X X
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg X) hX 2)
      (gaussian_bilinear_opNorm_nonnegative B)
    nlinarith only [h,hs]
  have htrace := gaussian_bilinear_partial_trace_norm_le B v hA (Gaussian.gaussianFastIndex hA k)
  have h1 := norm_add_le m (gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega)
  have h2 := norm_sub_le (B X X) (∑ i ∈ Finset.range (Gaussian.gaussianFastIndex hA k),B (v i) (v i))
  change ‖m+gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega‖≤
    ‖m‖+‖B‖*(Gaussian.gaussianFastEnvelope hA omega)^2+‖B‖*(∑' i,‖v i‖^2)
  change ‖gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega‖≤_ at h2
  linarith only [h1,h2,hbil,htrace]

end ASDExplicitGamma.Scalar
