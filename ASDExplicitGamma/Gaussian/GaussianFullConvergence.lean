module

public import ASDExplicitGamma.Gaussian.GaussianMartingale
public import ASDExplicitGamma.Gaussian.MartingaleFullConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Full almost-sure convergence of the square-summable Hilbert Gaussian series -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- Every scalar standard Gaussian real moment is finite. -/
theorem gauss_scalarGaussianLpMoment_lt_top {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) < ∞ := by
  have hm := memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have he := eLpNorm_eq_eLpNorm' (by positivity : ENNReal.ofReal p ≠ 0)
    ENNReal.ofReal_ne_top hm.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] at he
  rw [← he]
  exact hm.eLpNorm_lt_top

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  (v : ℕ → V) (hs : Summable (fun j => ‖v j‖ ^ 2))

include hs

omit [CompleteSpace V] in
/-- The full family of approximations has the same Gaussian moment bound as its finite sums. -/
theorem gaussianPartialSum_eLpNorm_le {p : ℝ} (hp : 2 ≤ p) (N : ℕ) :
    eLpNorm (gaussianPartialSum v N) (ENNReal.ofReal p) standardGaussianInfinitePi ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal (Real.sqrt (∑' j, ‖v j‖ ^ 2)) := by
  have hm := (memLp_gaussianPartialSum v hp hs N).aestronglyMeasurable
  rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
  have hh := eLpNorm'_gaussianPartialSum_sub_le (v := v) (n := 0) (m := N) (Nat.zero_le N) hp
  have hz : (fun ω => gaussianPartialSum v N ω - gaussianPartialSum v 0 ω) = gaussianPartialSum v N := by
    funext ω
    simp only [gaussianPartialSum, Finset.range_zero, Finset.sum_empty, sub_zero]
  rw [hz, Finset.range_zero, Finset.sdiff_empty] at hh
  apply hh.trans
  refine mul_le_mul_right ?_ _
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact hs.sum_le_tsum (Finset.range N) (fun _ _ => sq_nonneg _)

/-- Unlike a Banach squared-norm summability assertion, this uses the Hilbert series construction
and the actual independent Gaussian martingale to prove almost-sure convergence of every sum. -/
theorem ae_tendsto_gaussianPartialSum :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun N => gaussianPartialSum v N ω) atTop (𝓝 (gaussianSeriesLimit v hs ω)) := by
  let B := eLpNorm' (id : ℝ → ℝ) 2 (gaussianReal 0 1) * ENNReal.ofReal (Real.sqrt (∑' j, ‖v j‖ ^ 2))
  have hB : B ≠ ∞ := ENNReal.mul_ne_top (gauss_scalarGaussianLpMoment_lt_top (p := 2) (by norm_num)).ne ENNReal.ofReal_ne_top
  let R : ℝ≥0 := B.toNNReal
  have hR (n : ℕ) : eLpNorm (gaussianPartialSum v (n + 1)) 1 standardGaussianInfinitePi ≤ R := by
    rw [show (R : ℝ≥0∞) = B from ENNReal.coe_toNNReal hB]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (by simpa only [ENNReal.ofReal_ofNat] using gaussianPartialSum_eLpNorm_le v hs (by norm_num : (2 : ℝ) ≤ 2) (n + 1))
  have hpos (n : ℕ) : 1 ≤ gaussianFastIndex hs n := by
    have hbase : 1 ≤ gaussianFastIndex hs 0 := by simp [gaussianFastIndex]
    exact hbase.trans ((gaussianFastIndex_strictMono hs).monotone (Nat.zero_le n))
  let ns := fun n => gaussianFastIndex hs n - 1
  have hns : Tendsto ns atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [((gaussianFastIndex_strictMono hs).tendsto_atTop).eventually (eventually_ge_atTop (b + 1))] with n hn
    change b ≤ gaussianFastIndex hs n - 1
    omega
  have hsub : ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun n => gaussianPartialSum v (ns n + 1) ω) atTop (𝓝 (gaussianSeriesLimit v hs ω)) := by
    filter_upwards [ae_tendsto_gaussianSeriesLimit v hs] with ω hω
    convert hω using 1
    funext n
    rw [show ns n + 1 = gaussianFastIndex hs n from Nat.sub_add_cancel (hpos n)]
    rfl
  have hfull := martingale_ae_tendsto_of_subseq standardGaussianInfinitePi
    (fun n ω => gaussianPartialSum v (n + 1) ω) (gaussianPartialSum_martingale v) R hR
    (gaussianSeriesLimit v hs) ns hns hsub
  have hp : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega
  filter_upwards [hfull] with ω hω
  have hh := hω.comp hp
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [Nat.sub_add_cancel hn]

end
end ASDExplicitGamma.Gaussian
