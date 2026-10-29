module

public import ASDExplicitGamma.Model.Q3Moments
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

open Filter Topology

namespace ASDExplicitGamma.Model

private noncomputable def polynomialJoinJet (p q : Polynomial ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then ((Polynomial.derivative^[n]) p).eval x
  else ((Polynomial.derivative^[n]) q).eval x

private theorem polynomialJoinJet_hasDerivAt (p q : Polynomial ℝ) (n : ℕ)
    (hn : ((Polynomial.derivative^[n]) p).eval 0 = ((Polynomial.derivative^[n]) q).eval 0)
    (hn' : ((Polynomial.derivative^[n + 1]) p).eval 0 =
      ((Polynomial.derivative^[n + 1]) q).eval 0) (x : ℝ) :
    HasDerivAt (polynomialJoinJet p q n) (polynomialJoinJet p q (n + 1) x) x := by
  have hpd := Polynomial.hasDerivAt ((Polynomial.derivative^[n]) p) x
  have hqd := Polynomial.hasDerivAt ((Polynomial.derivative^[n]) q) x
  simp only [Function.iterate_succ_apply'] at hn'
  by_cases hx : x = 0
  · subst x
    have hl : HasDerivWithinAt (polynomialJoinJet p q n)
        (((Polynomial.derivative^[n]) p).derivative.eval 0) (Set.Iic 0) 0 := by
      apply hpd.hasDerivWithinAt.congr_of_mem
      · intro y hy
        change y ≤ 0 at hy
        simp only [polynomialJoinJet, ite_eq_left hy]
      · exact le_rfl
    have hr : HasDerivWithinAt (polynomialJoinJet p q n)
        (((Polynomial.derivative^[n]) p).derivative.eval 0) (Set.Ici 0) 0 := by
      rw [hn']
      apply hqd.hasDerivWithinAt.congr_of_mem
      · intro y hy
        by_cases hy0 : y = 0
        · subst y
          simp only [polynomialJoinJet, le_refl, ite_true]
          exact hn
        · simp only [polynomialJoinJet, ite_eq_right (not_le.mpr (lt_of_le_of_ne hy (Ne.symm hy0)))]
      · exact le_rfl
    have hd := hl.union hr
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hd
    simpa only [polynomialJoinJet, le_refl, ite_true, Function.iterate_succ_apply'] using hd
  · rcases lt_or_gt_of_ne hx with hx | hx
    · simp only [polynomialJoinJet, ite_eq_left hx.le, Function.iterate_succ_apply']
      apply HasDerivAt.congr_of_eventuallyEq hpd
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp only [polynomialJoinJet, ite_eq_left hy.le]
    · simp only [polynomialJoinJet, ite_eq_right (not_le.mpr hx), Function.iterate_succ_apply']
      apply HasDerivAt.congr_of_eventuallyEq hqd
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp only [polynomialJoinJet, ite_eq_right (not_le.mpr hy)]

private theorem iteratedDeriv_polynomialJoinJet (p q : Polynomial ℝ) (N : ℕ)
    (h : ∀ k ≤ N, ((Polynomial.derivative^[k]) p).eval 0 =
      ((Polynomial.derivative^[k]) q).eval 0) :
    ∀ n ≤ N, iteratedDeriv n (polynomialJoinJet p q 0) = polynomialJoinJet p q n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih (by omega)]
    funext x
    exact (polynomialJoinJet_hasDerivAt p q n (h n (by omega)) (h (n + 1) hn) x).deriv

private noncomputable def covarianceRight : Polynomial ℝ :=
  1 - Polynomial.C (39 / 5) * Polynomial.X ^ 2 + Polynomial.C (143 / 5) * Polynomial.X ^ 4 -
    Polynomial.C (429 / 5) * Polynomial.X ^ 6 + Polynomial.C (429 / 5) * Polynomial.X ^ 7 -
    Polynomial.C (143 / 5) * Polynomial.X ^ 9 + Polynomial.C (39 / 5) * Polynomial.X ^ 11 -
    Polynomial.X ^ 13

private noncomputable def covarianceLeft : Polynomial ℝ :=
  1 - Polynomial.C (39 / 5) * Polynomial.X ^ 2 + Polynomial.C (143 / 5) * Polynomial.X ^ 4 -
    Polynomial.C (429 / 5) * Polynomial.X ^ 6 - Polynomial.C (429 / 5) * Polynomial.X ^ 7 +
    Polynomial.C (143 / 5) * Polynomial.X ^ 9 - Polynomial.C (39 / 5) * Polynomial.X ^ 11 +
    Polynomial.X ^ 13

private theorem covariance_jets_match (k : ℕ) (hk : k ≤ 6) :
    ((Polynomial.derivative^[k]) covarianceLeft).eval 0 =
      ((Polynomial.derivative^[k]) covarianceRight).eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative, Polynomial.coeff_iterate_derivative]
  interval_cases k <;>
    norm_num [covarianceLeft, covarianceRight, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_one]

private theorem q3Cov_eventually_polynomialJoin :
    q3Cov =ᶠ[𝓝 (0 : ℝ)] polynomialJoinJet covarianceLeft covarianceRight 0 := by
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with x hx
  by_cases hx0 : x ≤ 0
  · have h := q3Cov_eq_polynomial_on_unit_interval (-x) (by linarith only [hx0]) (by linarith only [hx.1])
    rw [q3Cov_even] at h
    rw [h]
    simp only [polynomialJoinJet, ite_eq_left hx0, Function.iterate_zero, id_eq,
      covarianceLeft, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    ring
  · rw [q3Cov_eq_polynomial_on_unit_interval x (by linarith) hx.2.le]
    simp only [polynomialJoinJet, ite_eq_right hx0, Function.iterate_zero, id_eq,
      covarianceRight, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]

/-- The ordinary, two-sided covariance derivatives at zero. -/
theorem q3Cov_iteratedDeriv_values :
    iteratedDeriv 2 q3Cov 0 = -(78 / 5 : ℝ) ∧
      iteratedDeriv 4 q3Cov 0 = 3432 / 5 ∧ iteratedDeriv 6 q3Cov 0 = -(61776 : ℝ) := by
  have heq (n : ℕ) (hn : n ≤ 6) : iteratedDeriv n q3Cov 0 =
      ((Polynomial.derivative^[n]) covarianceLeft).eval 0 := by
    rw [q3Cov_eventually_polynomialJoin.iteratedDeriv_eq n,
      iteratedDeriv_polynomialJoinJet covarianceLeft covarianceRight 6 covariance_jets_match n hn]
    simp only [polynomialJoinJet, le_refl, ite_true]
  rw [heq 2 (by norm_num), heq 4 (by norm_num), heq 6 (by norm_num)]
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [covarianceLeft, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_one]

/-- The squared derivative norms agree with the ordinary covariance derivatives. -/
theorem q3Cov_derivative_norm_identities :
    -iteratedDeriv 2 q3Cov 0 = ∫ x, q3KernelD1 x ^ 2 ∧
      iteratedDeriv 4 q3Cov 0 = ∫ x, q3KernelD2 x ^ 2 ∧
      -iteratedDeriv 6 q3Cov 0 = ∫ x, q3KernelD3 x ^ 2 := by
  obtain ⟨h₂, h₄, h₆⟩ := q3Cov_iteratedDeriv_values
  rw [h₂, h₄, h₆, q3KernelD1_sq_integral_exact, q3KernelD2_sq_integral_exact,
    q3KernelD3_sq_integral_exact]
  norm_num

end ASDExplicitGamma.Model
