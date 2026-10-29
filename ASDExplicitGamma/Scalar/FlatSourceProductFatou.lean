module

public import ASDExplicitGamma.Scalar.FlatSourceSpatialWick
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! A lower-semicontinuity adapter for passing spatial Gaussian products from
finite modes to an L²-valued limit. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

/-- The squared norm of an `L²` representative is the integral of its
pointwise squared norm. This form keeps the spatial integral explicit for
the finite-mode Wick estimate. -/
theorem lp_two_norm_sq_eq_integral
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (μ : Measure X) (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ x, inner ℝ (f x) (f x) ∂μ := rfl
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact real_inner_self_eq_norm_sq (f x)

/-- The spatial squared norm of an `L∞` scalar times an `L²` vector is the
integral of the pointwise squared product. -/
theorem lp_smul_norm_sq_eq_integral
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (f : Lp ℝ ∞ μ) (g : Lp E 2 μ) :
    ‖f • g‖ ^ 2 = ∫ x, (f x) ^ 2 * ‖g x‖ ^ 2 ∂μ := by
  rw [lp_two_norm_sq_eq_integral]
  calc
    ∫ x, ‖(f • g : Lp E 2 μ) x‖ ^ 2 ∂μ =
        ∫ x, ‖f x • g x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_lpSMul (r := 2) f g] with x hx
      have hx' : (f • g : Lp E 2 μ) x = f x • g x := by
        simpa only [Pi.smul_apply'] using hx
      exact congrArg (fun z : E => ‖z‖ ^ 2) hx'
    _ = ∫ x, (f x) ^ 2 * ‖g x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        ‖f x • g x‖ ^ 2 = (|f x| * ‖g x‖) ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = |f x| ^ 2 * ‖g x‖ ^ 2 := mul_pow _ _ _
        _ = (f x) ^ 2 * ‖g x‖ ^ 2 := by rw [sq_abs]

/-- Multiplication of an `L∞` scalar factor and an `L²` vector factor is
continuous in the two Lp norms. -/
theorem lp_product_tendsto_of_tendsto
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X)
    (fseq : ℕ → Lp ℝ ∞ μ) (f : Lp ℝ ∞ μ)
    (gseq : ℕ → Lp E 2 μ) (g : Lp E 2 μ)
    (hf : Tendsto fseq atTop (𝓝 f))
    (hg : Tendsto gseq atTop (𝓝 g)) :
    Tendsto (fun n => fseq n • gseq n) atTop (𝓝 (f • g)) := by
  have hfd : Tendsto (fun n => ‖fseq n - f‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => fseq n - f) atTop (𝓝 0) := by
      simpa using hf.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))
    simpa using hsub.norm
  have hgn : Tendsto (fun n => ‖gseq n‖) atTop (𝓝 ‖g‖) := hg.norm
  have hgd : Tendsto (fun n => ‖gseq n - g‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => gseq n - g) atTop (𝓝 0) := by
      simpa using hg.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g))
    simpa using hsub.norm
  have hsum : Tendsto
      (fun n => ‖fseq n - f‖ * ‖gseq n‖ + ‖f‖ * ‖gseq n - g‖)
      atTop (𝓝 0) := by
    have hfirst := hfd.mul hgn
    have hsecond : Tendsto (fun n => ‖f‖ * ‖gseq n - g‖) atTop
        (𝓝 (‖f‖ * 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖f‖) atTop (𝓝 ‖f‖)).mul hgd
    simpa using hfirst.add hsecond
  have hidentity (n : ℕ) :
      fseq n • gseq n - f • g =
        (fseq n - f) • gseq n + f • (gseq n - g) := by
    have hsplitF : fseq n = (fseq n - f) + f := by abel
    have hsplitG : gseq n = g + (gseq n - g) := by abel
    calc
      fseq n • gseq n - f • g =
          ((fseq n - f) • gseq n + f • gseq n) - f • g := by
            rw [← Lp.smul_add]
            congr 1
            exact congrArg (fun a : Lp ℝ ∞ μ => a • gseq n) hsplitF
      _ = (fseq n - f) • gseq n + (f • gseq n - f • g) := by abel
      _ = (fseq n - f) • gseq n + f • (gseq n - g) := by
            congr 1
            calc
              f • gseq n - f • g = f • (g + (gseq n - g)) - f • g := by
                congr 1
                exact congrArg (fun z : Lp E 2 μ => f • z) hsplitG
              _ = f • (gseq n - g) := by rw [Lp.add_smul]; abel
  have hbound (n : ℕ) :
      ‖fseq n • gseq n - f • g‖ ≤
        ‖fseq n - f‖ * ‖gseq n‖ + ‖f‖ * ‖gseq n - g‖ := by
    rw [hidentity n]
    calc
      _ ≤ ‖(fseq n - f) • gseq n‖ + ‖f • (gseq n - g)‖ := norm_add_le _ _
      _ ≤ ‖fseq n - f‖ * ‖gseq n‖ + ‖f‖ * ‖gseq n - g‖ :=
        add_le_add (Lp.norm_smul_le _ _) (Lp.norm_smul_le _ _)
  have hnorm : Tendsto (fun n => ‖fseq n • gseq n - f • g‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hbound hsum
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end ASDExplicitGamma.Scalar
