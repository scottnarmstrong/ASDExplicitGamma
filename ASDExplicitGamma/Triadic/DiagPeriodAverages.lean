module

public import ASDExplicitGamma.Triadic.DiagPeriodReflection
public import ASDExplicitGamma.Triadic.DiagNodalParity

/-! Exact period-to-parent averaging for the source nodal energy budgets. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators Fin.CommRing

noncomputable section

/-- Embed an original cell in the first half of each period coordinate. -/
def diagPeriodEmbed {N : ℕ} (k : Fin 2 → Fin N) : Fin 2 → Fin (2*N) :=
  fun i => diagReflectionEquiv N (Sum.inl (k i))

/-- Offset in the affine cell-center face reflection. -/
def diagPeriodReflectionOffset (N : ℕ) [NeZero (2*N)] (i : Fin 2) : Fin 2 → Fin (2*N) :=
  fun a => if a = i then -1 else 0

theorem diagPeriodReflection_eq_affine (N : ℕ) [NeZero (2*N)] (i : Fin 2)
    (k : Fin 2 → Fin (2*N)) : diagPeriodReflection N i k =
      diagPeriodLinearReflection N i k + diagPeriodReflectionOffset N i := by
  funext a
  by_cases ha : a = i <;> simp [diagPeriodReflection, diagPeriodLinearReflection,
    diagPeriodReflectionOffset, ha, sub_eq_add_neg]

theorem diagPeriodLinearReflection_axis (N : ℕ) [NeZero (2*N)] (i a : Fin 2) :
    diagPeriodLinearReflection N i (diagPeriodLag N (diagAxisLag a)) =
      if decide (a=i) then -diagPeriodLag N (diagAxisLag a) else diagPeriodLag N (diagAxisLag a) := by
  funext b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [diagPeriodLinearReflection, diagPeriodLag, diagAxisLag]

/-- Every reflection-invariant scalar cell budget has four identical copies. -/
theorem diagPeriodGrid_even_sum {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (F : (Fin 2 → Fin (2*N)) → ℝ)
    (hF : ∀ i k, F (diagPeriodReflection N i k) = F k) :
    (∑ k, F k) = 4 * ∑ k : Fin 2 → Fin N, F (diagPeriodEmbed k) := by
  let E (t : Fin N) := diagReflectionEquiv N (Sum.inl t)
  have hr (b t : Fin (2*N)) : diagPeriodReflection N 0 (diagMeshLine 0 b t) =
      diagMeshLine 0 b (-t-1) := by
    funext a
    fin_cases a <;> simp [diagPeriodReflection, diagMeshLine]
  have hs (b : Fin (2*N)) :
      (∑ t : Fin (2*N), F (diagMeshLine 0 b t)) =
        2 * ∑ t : Fin N, F (diagMeshLine 0 b (E t)) := by
    apply diagPeriod_even_sum hN
    intro t
    rw [← hr]
    exact hF 0 _
  have ht (b : Fin (2*N)) (t : Fin N) :
      diagPeriodReflection N 1 (diagMeshLine 0 b (E t)) =
        diagMeshLine 0 (-b-1) (E t) := by
    funext a
    fin_cases a <;> simp [diagPeriodReflection, diagMeshLine]
  have hb : (∑ b : Fin (2*N), ∑ t : Fin N, F (diagMeshLine 0 b (E t))) =
      2 * ∑ b : Fin N, ∑ t : Fin N, F (diagMeshLine 0 (E b) (E t)) := by
    apply diagPeriod_even_sum hN
    intro b
    apply Finset.sum_congr rfl
    intro t _
    rw [← ht]
    exact hF 1 _
  rw [← diagGridLine_sum 0 1 (by decide)]
  simp_rw [hs]
  rw [← Finset.mul_sum, hb]
  have he (b t : Fin N) : diagMeshLine 0 (E b) (E t) = diagPeriodEmbed (diagMeshLine 0 b t) := by
    funext a
    fin_cases a <;> simp [diagPeriodEmbed, diagMeshLine, E]
  simp_rw [he]
  rw [diagGridLine_sum 0 1 (by decide) (fun k => F (diagPeriodEmbed k))]
  ring

/-- The actual odd-grid residual budget has exactly four parent copies. -/
theorem diagSourceGrid_residual_budget_sum {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (m : (Fin 2 → Fin N) → ℝ) :
    let F := diagNodalResidualBudget (diagPeriodLag N) (diagAxisLag 0) (diagAxisLag 1) (diagOddGrid N m)
    (∑ k, F k) = 4 * ∑ k : Fin 2 → Fin N, F (diagPeriodEmbed k) := by
  intro F
  apply diagPeriodGrid_even_sum hN
  intro i k
  rw [diagPeriodReflection_eq_affine]
  apply diagNodalResidualBudget_parity _ _ _ _ _ (decide (0=i)) (decide (1=i))
    (diagPeriodLinearReflection_axis N i 0) (diagPeriodLinearReflection_axis N i 1)
  intro x
  rw [← diagPeriodReflection_eq_affine]
  exact diagOddGrid_reflection hN m i x

/-- The actual odd-grid gradient budget has exactly four parent copies. -/
theorem diagSourceGrid_gradient_budget_sum {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (m : (Fin 2 → Fin N) → ℝ) (i s : Fin 2) :
    let F := diagNodalGradientBudget (diagPeriodLag N) (diagAxisLag i) (diagAxisLag s) (diagOddGrid N m)
    (∑ k, F k) = 4 * ∑ k : Fin 2 → Fin N, F (diagPeriodEmbed k) := by
  intro F
  apply diagPeriodGrid_even_sum hN
  intro a k
  rw [diagPeriodReflection_eq_affine]
  apply diagNodalGradientBudget_parity _ _ _ _ _ (decide (i=a)) (decide (s=a))
    (diagPeriodLinearReflection_axis N a i) (diagPeriodLinearReflection_axis N a s)
  intro x
  rw [← diagPeriodReflection_eq_affine]
  exact diagOddGrid_reflection hN m a x

end

end ASDExplicitGamma.Triadic
