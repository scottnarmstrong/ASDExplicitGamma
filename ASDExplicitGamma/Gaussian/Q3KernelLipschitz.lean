module

public import ASDExplicitGamma.Gaussian.H3KernelRegularity

/-! # Lipschitz control through the last continuous q3 derivative -/

@[expose] public section

open Set Filter ASDExplicitGamma.Model
open scoped Topology NNReal

namespace ASDExplicitGamma.Gaussian

private theorem q3Second_clamp (x : ℝ) :
    q3SecondPolynomial (projIcc (-(1 / 2 : ℝ)) (1 / 2) (by norm_num) x) = q3KernelD2 x := by
  rw [q3Second_eq_indicator]
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [projIcc_of_mem _ hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    have hh : x ≤ -(1 / 2 : ℝ) ∨ (1 / 2 : ℝ) ≤ x := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      exact hx.imp le_of_lt le_of_lt
    rcases hh with hh | hh
    · rw [projIcc_of_le_left _ hh]
      norm_num [q3SecondPolynomial]
    · rw [projIcc_of_right_le _ hh]
      norm_num [q3SecondPolynomial]

/-- The second derivative remains globally Lipschitz, despite the jumps of its derivative. -/
theorem q3KernelD2_lipschitz : ∃ C : ℝ≥0, LipschitzWith C q3KernelD2 := by
  have hQ : Continuous q3ThirdPolynomial := by
    unfold q3ThirdPolynomial
    fun_prop
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-(1 / 2 : ℝ)) (1 / 2))).bddAbove_image hQ.norm.continuousOn
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hp : LipschitzOnWith C q3SecondPolynomial (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    apply (convex_Icc (-(1 / 2 : ℝ)) (1 / 2)).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => (q3SecondPolynomial_hasDerivAt x).differentiableAt)
    intro x hx
    change ‖deriv q3SecondPolynomial x‖ ≤ max B 0
    rw [(q3SecondPolynomial_hasDerivAt x).deriv]
    exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  refine ⟨C, ?_⟩
  have hh := hp.to_restrict.comp (LipschitzWith.projIcc (show -(1 / 2 : ℝ) ≤ 1 / 2 by norm_num))
  have he : (Icc (-(1 / 2 : ℝ)) (1 / 2)).domRestrict q3SecondPolynomial ∘
      projIcc (-(1 / 2 : ℝ)) (1 / 2) (by norm_num) = q3KernelD2 :=
    funext q3Second_clamp
  simpa only [mul_one, he] using hh

/-- Off the two cutoffs, the weak third derivative is also the genuine classical derivative. -/
theorem q3KernelD2_hasDerivAt {x : ℝ} (hx : |x| ≠ 1 / 2) :
    HasDerivAt q3KernelD2 (q3KernelD3 x) x := by
  rcases lt_or_gt_of_ne hx with hi | ho
  · have he : q3KernelD2 =ᶠ[𝓝 x] q3SecondPolynomial := by
      filter_upwards [continuous_abs.continuousAt.eventually (eventually_lt_nhds hi)] with y hy
      rw [q3Second_eq_indicator, indicator_of_mem]
      simpa only [mem_Icc, abs_le] using hy.le
    simpa only [q3KernelD3, ite_eq_left hi, q3ThirdPolynomial] using
      (q3SecondPolynomial_hasDerivAt x).congr_of_eventuallyEq he
  · have he : q3KernelD2 =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [continuous_abs.continuousAt.eventually (eventually_gt_nhds ho)] with y hy
      rw [q3Second_eq_indicator, indicator_of_notMem]
      simpa only [mem_Icc, ← abs_le] using not_le.mpr hy
    simpa only [q3KernelD3, ite_eq_right (not_lt.mpr ho.le)] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

/-- Every derivative kernel vanishes outside the same fixed compact interval. -/
theorem q3Derivative_eq_zero {x : ℝ} (hx : 1 / 2 < |x|) (r : Fin 4) :
    q3Derivative r x = 0 := by
  have hp : 1 - 4 * x ^ 2 ≤ 0 := by nlinarith [sq_abs x]
  fin_cases r <;> simp [q3Derivative, q3Kernel, q3KernelD1, q3KernelD2,
    q3KernelD3, max_eq_right hp] <;> intro h <;> linarith

/-- The continuous derivative levels are globally Lipschitz. -/
theorem q3Derivative_lipschitz (r : Fin 4) (hr : r.val ≤ 2) :
    ∃ C : ℝ≥0, LipschitzWith C (q3Derivative r) := by
  fin_cases r
  · simpa [q3Derivative] using q3Kernel_first_lipschitz.1
  · simpa [q3Derivative] using q3Kernel_first_lipschitz.2
  · simpa [q3Derivative] using q3KernelD2_lipschitz
  · norm_num at hr

/-- All four derivative kernels have a finite uniform bound. -/
theorem q3Derivative_bounded (r : Fin 4) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖q3Derivative r x‖ ≤ B := by
  by_cases hr : r.val ≤ 2
  · obtain ⟨C, hC⟩ := q3Derivative_lipschitz r hr
    have hs : HasCompactSupport (q3Derivative r) := by
      apply HasCompactSupport.intro (K := Icc (-(1 / 2 : ℝ)) (1 / 2)) isCompact_Icc
      intro x hx
      apply q3Derivative_eq_zero
      have hh : ¬ |x| ≤ 1 / 2 := by simpa only [mem_Icc, abs_le] using hx
      exact lt_of_not_ge hh
    obtain ⟨B, hB⟩ := hC.continuous.bounded_above_of_compact_support hs
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  · have he : r = 3 := Fin.ext (by omega)
    subst r
    have hP : Continuous q3ThirdPolynomial := by unfold q3ThirdPolynomial; fun_prop
    obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-(1 / 2 : ℝ)) (1 / 2))).bddAbove_image hP.norm.continuousOn
    refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
    change ‖q3KernelD3 x‖ ≤ max B 0
    rw [q3Third_eq_indicator]
    by_cases hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)
    · rw [indicator_of_mem hx]
      exact (hB ⟨x, Ioo_subset_Icc_self hx, rfl⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, norm_zero]
      exact le_max_right _ _

/-- The last possible derivative failure is confined to the two kernel cutoffs. -/
theorem q3Derivative_hasDerivAt (r : Fin 4) (hr : r.val ≤ 2) {x : ℝ}
    (hx : |x| ≠ 1 / 2) :
    HasDerivAt (q3Derivative r) (q3Derivative ⟨r.val + 1, by omega⟩ x) x := by
  fin_cases r
  · simpa [q3Derivative] using q3Kernel_hasDerivAt x
  · simpa [q3Derivative] using gauss_q3KernelD1_hasDerivAt x
  · simpa [q3Derivative] using q3KernelD2_hasDerivAt hx
  · norm_num at hr

end ASDExplicitGamma.Gaussian
