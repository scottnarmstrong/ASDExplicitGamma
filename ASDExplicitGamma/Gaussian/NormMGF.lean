module

public import ASDExplicitGamma.Gaussian.NormConcentration
public import ASDExplicitGamma.Gaussian.NonnegativeFatou

/-! # Sharp exponential moments of finite Gaussian Banach norms -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- Increasing finite linear maxima pass their centered MGF bound to their integrable limit.
Only positive exponential parameters are needed for the upper norm fluctuation. -/
theorem integral_exp_centered_le_of_linearMaximum_limit {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L lam : ℝ} (hlam : 0 ≤ lam)
    (hcoeff : ∀ j, ‖WithLp.toLp 2 (a j)‖ ≤ L)
    (g : (Fin n → ℝ) → ℝ) (hg : Integrable g (standardGaussianPi n))
    (hle : ∀ N x, gaussianFiniteMaximum (Nat.succ_pos N) (fun i => a i.val) x ≤ g x)
    (hlim : ∀ x, Tendsto
      (fun N => gaussianFiniteMaximum (Nat.succ_pos N) (fun i => a i.val) x) atTop (𝓝 (g x))) :
    Integrable (fun x => Real.exp (lam * (g x - ∫ y, g y ∂standardGaussianPi n)))
      (standardGaussianPi n) ∧
    (∫ x, Real.exp (lam * (g x - ∫ y, g y ∂standardGaussianPi n)) ∂standardGaussianPi n) ≤
      Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  let μ := standardGaussianPi n
  let F (N : ℕ) := gaussianFiniteMaximum (Nat.succ_pos N) (fun i => a i.val)
  let m := ∫ y, g y ∂μ
  let mN (N : ℕ) := ∫ y, F N y ∂μ
  have hfinite (N : ℕ) := integral_exp_centered_le_of_gaussianFiniteMaximum
    (Nat.succ_pos N) (fun i => a i.val) (lam := lam) (fun i => hcoeff i.val)
  have hm (N : ℕ) : mN N ≤ m := integral_mono (hfinite N).1 hg (hle N)
  let c (N : ℕ) := Real.exp (lam * (mN N - m))
  have hc (N : ℕ) : c N ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr (hm N))
  have he (N : ℕ) : (fun x => Real.exp (lam * (F N x - m))) =
      fun x => c N * Real.exp (lam * (F N x - mN N)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  apply integrable_integral_le_of_ae_tendsto_nonneg μ
    (f := fun N x => Real.exp (lam * (F N x - m)))
  · intro N
    rw [he N]
    exact (hfinite N).2.2.1.const_mul _
  · intro N
    exact ae_of_all _ fun x => (Real.exp_pos _).le
  · exact Real.continuous_exp.comp_aestronglyMeasurable
      ((hg.aestronglyMeasurable.sub aestronglyMeasurable_const).const_mul lam)
  · exact ae_of_all _ fun x => Real.continuous_exp.continuousAt.tendsto.comp
      ((hlim x).sub_const m |>.const_mul lam)
  · intro N
    rw [he N, integral_const_mul]
    calc
      _ ≤ c N * Real.exp (lam ^ 2 * L ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hfinite N).2.2.2 (Real.exp_pos _).le
      _ ≤ 1 * Real.exp (lam ^ 2 * L ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (hc N) (Real.exp_pos _).le
      _ = _ := one_mul _

/-- The centered norm of a finite Gaussian covariance image has the sharp upper MGF bound. -/
theorem integral_exp_centered_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] E)
    {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hT : ‖T‖ ≤ L) :
    Integrable (fun x : Fin n → ℝ => Real.exp (lam * (‖T (WithLp.toLp 2 x)‖ -
      ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n))) (standardGaussianPi n) ∧
    (∫ x : Fin n → ℝ, Real.exp (lam * (‖T (WithLp.toLp 2 x)‖ -
      ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n)) ∂standardGaussianPi n) ≤
      Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  obtain ⟨a, hcoeff, hform⟩ := exists_norming_gaussian_linearForms T hT
  have hint := (measure_centered_tail_norm_le T hL (le_refl (0 : ℝ)) hT).1
  apply integral_exp_centered_le_of_linearMaximum_limit a hlam hcoeff _ hint
  · intro N x
    unfold gaussianFiniteMaximum
    apply Finset.sup'_le
    intro i hi
    rw [hform]
    exact normingSequence_apply_le E i.val _
  · intro x
    apply tendsto_order.mpr
    constructor
    · intro b hb
      rw [norm_eq_iSup_normingSequence E] at hb
      obtain ⟨k, hk⟩ := lt_ciSup_iff (bddAbove_def.mpr
        ⟨‖T (WithLp.toLp 2 x)‖, by rintro y ⟨j, rfl⟩; exact normingSequence_apply_le E j _⟩) |>.mp hb
      filter_upwards [eventually_ge_atTop k] with N hN
      apply hk.trans_le
      rw [← hform]
      unfold gaussianFiniteMaximum
      exact Finset.le_sup' (fun i : Fin (N + 1) => gaussianFiniteLinearForm (a i.val) x)
        (Finset.mem_univ ⟨k, by omega⟩)
    · intro b hb
      filter_upwards with N
      apply lt_of_le_of_lt _ hb
      unfold gaussianFiniteMaximum
      apply Finset.sup'_le
      intro i hi
      rw [hform]
      exact normingSequence_apply_le E i.val _

end ASDExplicitGamma.Gaussian
