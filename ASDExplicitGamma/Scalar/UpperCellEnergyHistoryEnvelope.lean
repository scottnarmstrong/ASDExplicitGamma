module

public import ASDExplicitGamma.Scalar.UpperCellEnergySmallComparison
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Selecting a descendant depth converts local sensitivity into a linear envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section

/-- The actual depth choice is finite, and its cost is linear in the original
sensitivity parameter after squaring the square-root history weight. -/
theorem upper_cell_history_depth_choice {x q : ℝ}
    (hx : 2/5 < x) (hq : 1 < q) (hq2 : q ≤ 2) :
    ∃ j : ℕ, x/q^j ≤ 2/5 ∧ q^j ≤ 5*x := by
  obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near
    (show (1:ℝ) ≤ (5/2)*x by linarith) hq
  refine ⟨n+1, ?_, ?_⟩
  · apply (div_le_iff₀ (pow_pos (lt_trans zero_lt_one hq) _)).mpr
    linarith only [hnext]
  · rw [pow_succ]
    have hh := mul_le_mul hn hq2 (le_trans (by norm_num) hq.le)
      (show 0 ≤ (5/2:ℝ)*x by linarith)
    linarith only [hh]

/-- A proved local response comparison at every descendant depth yields the
source baseline-preserving envelope 1+3x. This analytic lemma exposes the
all-depth comparison input; the physical application must prove that input. -/
theorem upper_cell_history_linear_envelope {E x q : ℝ}
    (hx : 0 ≤ x) (hq : 1 < q) (hq2 : q ≤ 2)
    (hdepth : ∀ j : ℕ, x/q^j ≤ 2/5 →
      E ≤ Real.sqrt (q^j)*(1+(5/4:ℝ)*(x/q^j))) :
    E ≤ 1+3*x := by
  by_cases hsmall : x ≤ 2/5
  · have hh := hdepth 0 (by simpa using hsmall)
    simp only [pow_zero,div_one,Real.sqrt_one,one_mul] at hh
    linarith only [hh,hx]
  obtain ⟨j,hj,hcost⟩ := upper_cell_history_depth_choice (lt_of_not_ge hsmall) hq hq2
  have hq0 := lt_trans zero_lt_one hq
  have hcap : 1+(5/4:ℝ)*(x/q^j) ≤ 3/2 := by linarith only [hj]
  have he : E ≤ Real.sqrt (q^j)*(3/2) := (hdepth j hj).trans
    (mul_le_mul_of_nonneg_left hcap (Real.sqrt_nonneg _))
  by_cases hE : E ≤ 0
  · linarith only [hE,hx]
  have hE0 := (lt_of_not_ge hE).le
  have hesq := pow_le_pow_left₀ hE0 he 2
  rw [mul_pow,Real.sq_sqrt (pow_nonneg hq0.le _)] at hesq
  have hsquare : E^2 ≤ (1+3*x)^2 := by
    nlinarith only [hesq,hcost,sq_nonneg (1-3*x)]
  exact (sq_le_sq₀ hE0 (by positivity)).mp hsquare

end
end ASDExplicitGamma.Scalar
