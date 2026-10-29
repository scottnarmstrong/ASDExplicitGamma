module

public import ASDExplicitGamma.Scalar.GaussianProductVectors
public import ASDExplicitGamma.Gaussian.RealizationSeries
public import ASDExplicitGamma.Gaussian.DerivativeLawMoments
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Gaussian.ShellFrameClock
public import ASDExplicitGamma.Model.Q3DerivativeMoments
public import Algsuperdiff.Section3

/-! Finite white-noise truncations obey the vector Wick bound with explicit mode variances. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3

private theorem measurable_gaussianScalarPartialSum
    (a : ℕ → ℝ) (N : ℕ) :
    Measurable (gaussianScalarPartialSum a N) := by
  unfold gaussianScalarPartialSum
  exact Finset.measurable_sum _ (fun n hn =>
    (measurable_pi_apply n).mul measurable_const)

private theorem gaussianScalarPartialSum_hasGaussianLaw
    (a : ℕ → ℝ) (N : ℕ) :
    HasGaussianLaw (gaussianScalarPartialSum a N) standardGaussianInfinitePi := by
  have hm : AEMeasurable (gaussianScalarPartialSum a N) standardGaussianInfinitePi := by
    exact (measurable_gaussianScalarPartialSum a N).aemeasurable
  have hlaw := map_gaussianScalarPartialSum a N
  exact ⟨hm, by rw [hlaw]; infer_instance⟩

private theorem gaussianScalarPartialSum_mean
    (a : ℕ → ℝ) (N : ℕ) :
    (∫ ω, gaussianScalarPartialSum a N ω ∂standardGaussianInfinitePi) = 0 := by
  have hm : AEMeasurable (gaussianScalarPartialSum a N) standardGaussianInfinitePi := by
    exact (measurable_gaussianScalarPartialSum a N).aemeasurable
  simpa using integral_of_map_gaussianReal hm (map_gaussianScalarPartialSum a N)

private theorem gaussianScalarPartialSum_second_moment
    (a : ℕ → ℝ) (N : ℕ) :
    (∫ ω, (gaussianScalarPartialSum a N ω) ^ 2 ∂standardGaussianInfinitePi) =
      ∑ n ∈ Finset.range N, (a n) ^ 2 := by
  have hm : AEMeasurable (gaussianScalarPartialSum a N) standardGaussianInfinitePi := by
    exact (measurable_gaussianScalarPartialSum a N).aemeasurable
  have h := integral_sq_of_map_gaussianReal_zero hm
    (map_gaussianScalarPartialSum a N)
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun n hn => sq_nonneg (a n))] at h
  exact h

/-- The finite q3 Wick contraction for one scalar and a finite vector of
linear white-noise modes. No independence between the resulting fields is
needed; only their shared standard Gaussian coordinates are used. -/
theorem centered_gaussian_finite_mode_product_bound
    {κ : Type*} [Fintype κ]
    (N : ℕ) (a : ℕ → ℝ) (b : κ → ℕ → ℝ) :
    (∫ ω, (gaussianScalarPartialSum a N ω) ^ 2 *
      (∑ i, (gaussianScalarPartialSum (b i) N ω) ^ 2)
      ∂standardGaussianInfinitePi) ≤
      3 * (∑ n ∈ Finset.range N, (a n) ^ 2) *
        (∑ i, ∑ n ∈ Finset.range N, (b i n) ^ 2) := by
  let X : Unit → (ℕ → ℝ) → ℝ := fun _ => gaussianScalarPartialSum a N
  let Y : κ → (ℕ → ℝ) → ℝ := fun i => gaussianScalarPartialSum (b i) N
  have hwick := centered_gaussian_vector_product_bound standardGaussianInfinitePi X Y
    (fun _ => gaussianScalarPartialSum_hasGaussianLaw a N)
    (fun i => gaussianScalarPartialSum_hasGaussianLaw (b i) N)
    (fun _ => gaussianScalarPartialSum_mean a N)
    (fun i => gaussianScalarPartialSum_mean (b i) N)
  calc
    _ ≤ 3 *
        (∫ ω, (gaussianScalarPartialSum a N ω) ^ 2 ∂standardGaussianInfinitePi) *
        (∑ i, ∫ ω, (gaussianScalarPartialSum (b i) N ω) ^ 2
          ∂standardGaussianInfinitePi) := by
      simpa [X, Y] using hwick
    _ = 3 * (∑ n ∈ Finset.range N, (a n) ^ 2) *
        (∑ i, ∑ n ∈ Finset.range N, (b i n) ^ 2) := by
      rw [gaussianScalarPartialSum_second_moment]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact gaussianScalarPartialSum_second_moment (b i) N

/-- A finite common-noise Wick bound for one component of the spatial
product gradient. The two derivative terms remain correlated: the estimate
uses only the finite Gaussian fourth-moment bound. -/
theorem centered_gaussian_finite_mode_product_gradient_component_bound
    (N : ℕ) (a b da db : ℕ → ℝ)
    (hleft : Integrable (fun ω =>
      (gaussianScalarPartialSum da N ω * gaussianScalarPartialSum b N ω +
        gaussianScalarPartialSum a N ω * gaussianScalarPartialSum db N ω) ^ 2)
      standardGaussianInfinitePi)
    (hfirst : Integrable (fun ω =>
      gaussianScalarPartialSum da N ω ^ 2 * gaussianScalarPartialSum b N ω ^ 2)
      standardGaussianInfinitePi)
    (hsecond : Integrable (fun ω =>
      gaussianScalarPartialSum a N ω ^ 2 * gaussianScalarPartialSum db N ω ^ 2)
      standardGaussianInfinitePi)
    (hright : Integrable (fun ω =>
      2 * (gaussianScalarPartialSum da N ω ^ 2 * gaussianScalarPartialSum b N ω ^ 2) +
        2 * (gaussianScalarPartialSum a N ω ^ 2 * gaussianScalarPartialSum db N ω ^ 2))
      standardGaussianInfinitePi) :
    (∫ ω,
      (gaussianScalarPartialSum da N ω * gaussianScalarPartialSum b N ω +
        gaussianScalarPartialSum a N ω * gaussianScalarPartialSum db N ω) ^ 2
      ∂standardGaussianInfinitePi) ≤
      6 * (∑ n ∈ Finset.range N, (da n) ^ 2) *
        (∑ n ∈ Finset.range N, (b n) ^ 2) +
      6 * (∑ n ∈ Finset.range N, (a n) ^ 2) *
        (∑ n ∈ Finset.range N, (db n) ^ 2) := by
  have hpoint : ∀ ω,
      (gaussianScalarPartialSum da N ω * gaussianScalarPartialSum b N ω +
        gaussianScalarPartialSum a N ω * gaussianScalarPartialSum db N ω) ^ 2 ≤
      2 * (gaussianScalarPartialSum da N ω ^ 2 * gaussianScalarPartialSum b N ω ^ 2) +
        2 * (gaussianScalarPartialSum a N ω ^ 2 * gaussianScalarPartialSum db N ω ^ 2) := by
    intro ω
    nlinarith [sq_nonneg
      (gaussianScalarPartialSum da N ω * gaussianScalarPartialSum b N ω -
        gaussianScalarPartialSum a N ω * gaussianScalarPartialSum db N ω)]
  have hmono := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall hpoint)
  have hwickFirst :
      (∫ ω, gaussianScalarPartialSum da N ω ^ 2 *
        gaussianScalarPartialSum b N ω ^ 2 ∂standardGaussianInfinitePi) ≤
        3 * (∑ n ∈ Finset.range N, (da n) ^ 2) *
          (∑ n ∈ Finset.range N, (b n) ^ 2) := by
    simpa using centered_gaussian_finite_mode_product_bound N da (fun _ : Unit => b)
  have hwickSecond :
      (∫ ω, gaussianScalarPartialSum a N ω ^ 2 *
        gaussianScalarPartialSum db N ω ^ 2 ∂standardGaussianInfinitePi) ≤
        3 * (∑ n ∈ Finset.range N, (a n) ^ 2) *
          (∑ n ∈ Finset.range N, (db n) ^ 2) := by
    simpa using centered_gaussian_finite_mode_product_bound N a (fun _ : Unit => db)
  calc
    _ ≤ ∫ ω,
        2 * (gaussianScalarPartialSum da N ω ^ 2 * gaussianScalarPartialSum b N ω ^ 2) +
          2 * (gaussianScalarPartialSum a N ω ^ 2 * gaussianScalarPartialSum db N ω ^ 2)
        ∂standardGaussianInfinitePi := hmono
    _ = 2 * (∫ ω, gaussianScalarPartialSum da N ω ^ 2 *
          gaussianScalarPartialSum b N ω ^ 2 ∂standardGaussianInfinitePi) +
        2 * (∫ ω, gaussianScalarPartialSum a N ω ^ 2 *
          gaussianScalarPartialSum db N ω ^ 2 ∂standardGaussianInfinitePi) := by
      rw [integral_add (hfirst.const_mul 2) (hsecond.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 6 * (∑ n ∈ Finset.range N, (da n) ^ 2) *
          (∑ n ∈ Finset.range N, (b n) ^ 2) +
        6 * (∑ n ∈ Finset.range N, (a n) ^ 2) *
          (∑ n ∈ Finset.range N, (db n) ^ 2) := by
      nlinarith [hwickFirst, hwickSecond]

/-- The finite product-gradient Wick estimate, with integrability of its
degree-four Gaussian terms discharged from their finite Gaussian laws. -/
theorem centered_gaussian_finite_mode_product_gradient_component_bound_auto
    (N : ℕ) (a b da db : ℕ → ℝ) :
    Integrable (fun ω =>
      (gaussianScalarPartialSum da N ω * gaussianScalarPartialSum b N ω +
        gaussianScalarPartialSum a N ω * gaussianScalarPartialSum db N ω) ^ 2)
      standardGaussianInfinitePi ∧
    (∫ ω,
      (gaussianScalarPartialSum da N ω * gaussianScalarPartialSum b N ω +
        gaussianScalarPartialSum a N ω * gaussianScalarPartialSum db N ω) ^ 2
      ∂standardGaussianInfinitePi) ≤
      6 * (∑ n ∈ Finset.range N, (da n) ^ 2) *
        (∑ n ∈ Finset.range N, (b n) ^ 2) +
      6 * (∑ n ∈ Finset.range N, (a n) ^ 2) *
        (∑ n ∈ Finset.range N, (db n) ^ 2) := by
  have instHolderFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv, ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul] <;> norm_num⟩
  let A := gaussianScalarPartialSum da N
  let B := gaussianScalarPartialSum b N
  let C := gaussianScalarPartialSum a N
  let D := gaussianScalarPartialSum db N
  have hA4 : MemLp A 4 standardGaussianInfinitePi :=
    gaussianScalarPartialSum_hasGaussianLaw da N |>.memLp (by norm_num)
  have hB4 : MemLp B 4 standardGaussianInfinitePi :=
    gaussianScalarPartialSum_hasGaussianLaw b N |>.memLp (by norm_num)
  have hC4 : MemLp C 4 standardGaussianInfinitePi :=
    gaussianScalarPartialSum_hasGaussianLaw a N |>.memLp (by norm_num)
  have hD4 : MemLp D 4 standardGaussianInfinitePi :=
    gaussianScalarPartialSum_hasGaussianLaw db N |>.memLp (by norm_num)
  have hAB : MemLp (A * B) 2 standardGaussianInfinitePi := hA4.fun_mul hB4
  have hCD : MemLp (C * D) 2 standardGaussianInfinitePi := hC4.fun_mul hD4
  have hsum : MemLp (A * B + C * D) 2 standardGaussianInfinitePi := hAB.add hCD
  have hleft : Integrable (fun ω => (A ω * B ω + C ω * D ω) ^ 2)
      standardGaussianInfinitePi := by
    simpa only [Pi.add_apply, Pi.mul_apply] using hsum.integrable_sq
  have hA2 : MemLp (fun ω => A ω ^ 2) 2 standardGaussianInfinitePi := by
    simpa only [pow_two] using hA4.fun_mul hA4
  have hB2 : MemLp (fun ω => B ω ^ 2) 2 standardGaussianInfinitePi := by
    simpa only [pow_two] using hB4.fun_mul hB4
  have hC2 : MemLp (fun ω => C ω ^ 2) 2 standardGaussianInfinitePi := by
    simpa only [pow_two] using hC4.fun_mul hC4
  have hD2 : MemLp (fun ω => D ω ^ 2) 2 standardGaussianInfinitePi := by
    simpa only [pow_two] using hD4.fun_mul hD4
  have hfirst : Integrable (fun ω => A ω ^ 2 * B ω ^ 2) standardGaussianInfinitePi :=
    hA2.integrable_mul hB2
  have hsecond : Integrable (fun ω => C ω ^ 2 * D ω ^ 2) standardGaussianInfinitePi :=
    hC2.integrable_mul hD2
  have hright : Integrable (fun ω => 2 * (A ω ^ 2 * B ω ^ 2) +
      2 * (C ω ^ 2 * D ω ^ 2)) standardGaussianInfinitePi := by
    exact (hfirst.const_mul 2).add (hsecond.const_mul 2)
  refine ⟨?_, ?_⟩
  · simpa only [A, B, C, D, Pi.add_apply, Pi.mul_apply] using hleft
  · exact centered_gaussian_finite_mode_product_gradient_component_bound
      N a b da db (by simpa only [A, B, C, D, Pi.add_apply, Pi.mul_apply] using hleft)
      (by simpa only [A, B, Pi.mul_apply] using hfirst)
      (by simpa only [C, D, Pi.mul_apply] using hsecond)
      (by simpa only [A, B, C, D, Pi.add_apply, Pi.mul_apply] using hright)

/-- The value modes of the physical q3 H³ factor have the exact pointwise
variance, before spatial averaging or any projection estimate. -/
theorem q3_value_mode_variance
    {a b c d β : ℝ} (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (x : closedRectangle a b c d) :
    (∑' n : ℕ,
      (q3H3RangeValue a b c d β L
        (q3H3Directions a b c d β L whiteBasis n) x) ^ 2) = β ^ 2 := by
  have hcov := q3H3Directions_covariance a b c d β hab hcd L whiteBasis x x
  simpa [pow_two, ASDExplicitGamma.Model.q3Cov_at_zero] using hcov

end ASDExplicitGamma.Scalar
