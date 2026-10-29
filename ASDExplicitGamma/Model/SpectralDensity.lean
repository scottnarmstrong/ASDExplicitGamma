module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

open MeasureTheory Complex
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Uniqueness of the Fourier transform for an integrable real density.
The two positive measures with densities `|f| + f` and `|f| - f` are finite,
so characteristic-function uniqueness applies without normalization. -/
theorem ae_eq_zero_of_integral_mul_exp_eq_zero_real
    {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : Integrable f μ)
    (hzero : ∀ t : E, ∫ x, (f x : ℂ) * exp ((inner ℝ x t : ℂ) * I) ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  let p : E → ℝ := fun x => ‖f x‖ + f x
  let n : E → ℝ := fun x => ‖f x‖ - f x
  have hp : Integrable p μ := hf.norm.add hf
  have hn : Integrable n μ := hf.norm.sub hf
  have hp0 (x : E) : 0 ≤ p x := by
    dsimp [p]
    have := neg_abs_le (f x)
    linarith
  have hn0 (x : E) : 0 ≤ n x := by
    dsimp [n]
    exact sub_nonneg.mpr (le_abs_self (f x))
  let P := μ.withDensity (fun x => ENNReal.ofReal (p x))
  let N := μ.withDensity (fun x => ENNReal.ofReal (n x))
  have hP : IsFiniteMeasure P := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp0)).mp
      hp.hasFiniteIntegral).ne
  have hN : IsFiniteMeasure N := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn0)).mp
      hn.hasFiniteIntegral).ne
  have heq : P = N := by
    apply Measure.ext_of_charFun
    funext t
    have hprod (g : E → ℝ) (hg : Integrable g μ) :
        Integrable (fun x => (g x : ℂ) * exp ((inner ℝ x t : ℂ) * I)) μ := by
      apply hg.ofReal.mul_bdd
        ((BoundedContinuousFunction.innerProbChar t).continuous.aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun x => (norm_exp_ofReal_mul_I _).le
    rw [charFun_apply, charFun_apply]
    change (∫ x, exp ((inner ℝ x t : ℂ) * I) ∂P) =
      ∫ x, exp ((inner ℝ x t : ℂ) * I) ∂N
    dsimp [P, N]
    rw [integral_withDensity_eq_integral_toReal_smul₀
        hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀
        hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hp0 _), ENNReal.toReal_ofReal (hn0 _),
      Complex.real_smul]
    apply sub_eq_zero.mp
    rw [← integral_sub (hprod p hp) (hprod n hn)]
    calc
      (∫ x, (p x : ℂ) * exp ((inner ℝ x t : ℂ) * I) -
          (n x : ℂ) * exp ((inner ℝ x t : ℂ) * I) ∂μ) =
          ∫ x, (2 : ℂ) * ((f x : ℂ) * exp ((inner ℝ x t : ℂ) * I)) ∂μ := by
        congr 1
        funext x
        dsimp [p, n]
        push_cast
        ring
      _ = 0 := by rw [integral_const_mul, hzero t, mul_zero]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [hae] with x hx
  have hpn : p x = n x := by
    simpa only [ENNReal.toReal_ofReal (hp0 x), ENNReal.toReal_ofReal (hn0 x)] using
      congrArg ENNReal.toReal hx
  change f x = 0
  dsimp [p, n] at hpn
  linarith

/-- Uniqueness for complex integrable densities, by real and imaginary parts. -/
theorem ae_eq_zero_of_integral_mul_exp_eq_zero
    {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℂ}
    (hf : Integrable f μ)
    (hzero : ∀ t : E, ∫ x, f x * exp ((inner ℝ x t : ℂ) * I) ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  have hprod (g : E → ℂ) (hg : Integrable g μ) (t : E) :
      Integrable (fun x => g x * exp ((inner ℝ x t : ℂ) * I)) μ := by
    apply hg.mul_bdd
      ((BoundedContinuousFunction.innerProbChar t).continuous.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => (norm_exp_ofReal_mul_I _).le
  have hfconj : Integrable (fun x => (starRingEnd ℂ) (f x)) μ := by
    have h := Complex.conjCLE.toContinuousLinearMap.integrable_comp hf
    simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using h
  have hc (t : E) :
      ∫ x, (starRingEnd ℂ) (f x) * exp ((inner ℝ x t : ℂ) * I) ∂μ = 0 := by
    have h := congrArg (starRingEnd ℂ) (hzero (-t))
    rw [← integral_conj] at h
    simpa [map_mul, ← Complex.exp_conj, inner_neg_right] using h
  have hr (t : E) : ∫ x, ((f x).re : ℂ) * exp ((inner ℝ x t : ℂ) * I) ∂μ = 0 := by
    have h : (∫ x, (f x + (starRingEnd ℂ) (f x)) *
        exp ((inner ℝ x t : ℂ) * I) ∂μ) = 0 := by
      simp_rw [add_mul]
      rw [integral_add (hprod f hf t) (hprod _ hfconj t), hzero t, hc t, add_zero]
    simp_rw [Complex.add_conj, ofReal_mul, ofReal_ofNat, mul_assoc] at h
    rw [integral_const_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hi (t : E) : ∫ x, ((f x).im : ℂ) * exp ((inner ℝ x t : ℂ) * I) ∂μ = 0 := by
    have h : (∫ x, (f x - (starRingEnd ℂ) (f x)) *
        exp ((inner ℝ x t : ℂ) * I) ∂μ) = 0 := by
      simp_rw [sub_mul]
      rw [integral_sub (hprod f hf t) (hprod _ hfconj t), hzero t, hc t, sub_self]
    have heq (x : E) : (f x - (starRingEnd ℂ) (f x)) *
        exp ((inner ℝ x t : ℂ) * I) =
        (2 * I) * (((f x).im : ℂ) * exp ((inner ℝ x t : ℂ) * I)) := by
      rw [Complex.sub_conj]
      push_cast
      ring
    simp_rw [heq] at h
    rw [integral_const_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hre := ae_eq_zero_of_integral_mul_exp_eq_zero_real hf.re hr
  have him := ae_eq_zero_of_integral_mul_exp_eq_zero_real hf.im hi
  filter_upwards [hre, him] with x hx hy
  exact Complex.ext hx hy

/-- Characters span a dense subspace of `L²` for every finite Borel measure.
In particular the result applies to a finite spectral measure with a density. -/
theorem exponential_span_dense (μ : Measure E) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (fun t : E =>
      BoundedContinuousFunction.toLp 2 μ ℂ
        (BoundedContinuousFunction.innerProbChar t)))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  have hzero (t : E) : ∫ x, f x * exp ((inner ℝ x t : ℂ) * I) ∂μ = 0 := by
    have hinner := hf _ (Submodule.subset_span (Set.mem_range_self (-t)))
    rw [L2.inner_def] at hinner
    have hcoe := BoundedContinuousFunction.coeFn_toLp 2 μ ℂ
      (BoundedContinuousFunction.innerProbChar (-t))
    have heq : (∫ x, inner ℂ
        ((BoundedContinuousFunction.toLp 2 μ ℂ
          (BoundedContinuousFunction.innerProbChar (-t))) x) (f x) ∂μ) =
        ∫ x, f x * exp ((inner ℝ x t : ℂ) * I) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx, RCLike.inner_apply, BoundedContinuousFunction.innerProbChar_apply]
      simp [← Complex.exp_conj, inner_neg_right]
    exact heq.symm.trans hinner
  apply Lp.ext
  exact (ae_eq_zero_of_integral_mul_exp_eq_zero
    (MemLp.integrable (by norm_num) (Lp.memLp f)) hzero).trans
      (Lp.coeFn_zero ℂ 2 μ).symm

/-- Rescaling the frequency parameter by any nonzero real number preserves density. -/
theorem exponential_span_dense_rescale (μ : Measure E) [IsFiniteMeasure μ]
    (a : ℝ) (ha : a ≠ 0) :
    (Submodule.span ℂ (Set.range (fun t : E =>
      BoundedContinuousFunction.toLp 2 μ ℂ
        (BoundedContinuousFunction.innerProbChar (a • t))))).topologicalClosure = ⊤ := by
  have hrange : Set.range (fun t : E =>
      BoundedContinuousFunction.toLp 2 μ ℂ
        (BoundedContinuousFunction.innerProbChar (a • t))) =
      Set.range (fun t : E => BoundedContinuousFunction.toLp 2 μ ℂ
        (BoundedContinuousFunction.innerProbChar t)) := by
    apply Set.ext
    intro f
    constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_range_self (a • t)
    · rintro ⟨t, rfl⟩
      refine ⟨a⁻¹ • t, ?_⟩
      dsimp only
      rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [hrange]
  exact exponential_span_dense μ

end ASDExplicitGamma.Model
