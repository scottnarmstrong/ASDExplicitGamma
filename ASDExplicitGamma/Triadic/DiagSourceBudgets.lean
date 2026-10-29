module

public import ASDExplicitGamma.Triadic.DiagPeriodAverages

/-! Source broken weak energy bounds for the actual nodal cell coefficient budgets. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators Fin.CommRing

noncomputable section

/-- The sharp half-gain coefficient budget on the original source cells. -/
theorem diagSourceResidualBudget_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    ((N:ℝ)⁻¹)^2 * ∑ k : Fin 2 → Fin N,
      diagNodalResidualBudget (diagPeriodLag N) (diagAxisLag 0) (diagAxisLag 1)
        (diagOddGrid N (diagSourceMeans Q j u.toH1Function)) (diagPeriodEmbed k) ≤
      diagMeshRadius Q j ^ 2 / 4 *
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  intro N instPeriodNonzero
  let f := diagOddGrid N (diagSourceMeans Q j u.toH1Function)
  let r := diagMeshRadius Q j
  have hr : r ≠ 0 := (diagMeshRadius_pos Q j).ne'
  have hN : 0 < N := pow_pos (by norm_num) j
  have hc : 0 ≤ ((N:ℝ)⁻¹)^2/4 := by positivity
  have hres := mul_le_mul_of_nonneg_left
    (diagNodalResidualBudget_contracts (diagPeriodLag N) (diagAxisLag 0) (diagAxisLag 1) f) hc
  rw [diagSourceGrid_residual_budget_sum hN] at hres
  have hsource := mul_le_mul_of_nonneg_left (diagSourceGrid_difference_energy Q j u)
    (by positivity : 0 ≤ r^2/4)
  have hid : r^2/4 * (((N:ℝ)⁻¹)^2/4 * ∑ i : Fin 2,
      ∑ k : Fin 2 → Fin (2*N), ((f (k+diagPeriodLag N (diagAxisLag i))-f k)/r)^2) =
      ((N:ℝ)⁻¹)^2/4 * ((1/4:ℝ)*∑ k : Fin 2 → Fin (2*N),
        ((f k-f (k+diagPeriodLag N (diagAxisLag 0)))^2+
          (f k-f (k+diagPeriodLag N (diagAxisLag 1)))^2)) := by
    simp only [div_pow, ← Finset.sum_div, Fin.sum_univ_two, Finset.sum_add_distrib]
    have hs (i : Fin 2) : (∑ k : Fin 2 → Fin (2*N),
        (f (k+diagPeriodLag N (diagAxisLag i))-f k)^2) =
        ∑ k, (f k-f (k+diagPeriodLag N (diagAxisLag i)))^2 := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs, hs]
    field_simp [hr]
  change r^2/4 * (((N:ℝ)⁻¹)^2/4 * ∑ i : Fin 2,
    ∑ k : Fin 2 → Fin (2*N), ((f (k+diagPeriodLag N (diagAxisLag i))-f k)/r)^2) ≤ _ at hsource
  rw [hid] at hsource
  have hchain := hres.trans hsource
  convert hchain using 1
  ring

/-- Both positive-gradient coefficient budgets obey the sharp source weak bound. -/
theorem diagSourceGradientBudget_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    ((N:ℝ)⁻¹)^2 / diagMeshRadius Q j ^ 2 * ∑ k : Fin 2 → Fin N, ∑ i : Fin 2,
      diagNodalGradientBudget (diagPeriodLag N) (diagAxisLag i) (diagAxisLag (diagOtherCoordinate i))
        (diagOddGrid N (diagSourceMeans Q j u.toH1Function)) (diagPeriodEmbed k) ≤
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  intro N instPeriodNonzero
  let f := diagOddGrid N (diagSourceMeans Q j u.toH1Function)
  let r := diagMeshRadius Q j
  have hN : 0 < N := pow_pos (by norm_num) j
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin 2) _ =>
    diagNodalGradientBudget_contracts (diagPeriodLag N) (diagAxisLag i)
      (diagAxisLag (diagOtherCoordinate i)) f
  dsimp only [f] at hsum
  simp_rw [diagSourceGrid_gradient_budget_sum hN] at hsum
  have hc : 0 ≤ ((N:ℝ)⁻¹)^2 / (4*r^2) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hc
  have hrow : ((N:ℝ)⁻¹)^2/r^2 * ∑ k : Fin 2 → Fin N, ∑ i : Fin 2,
      diagNodalGradientBudget (diagPeriodLag N) (diagAxisLag i)
        (diagAxisLag (diagOtherCoordinate i)) f (diagPeriodEmbed k) ≤
      ((N:ℝ)⁻¹)^2/4 * ∑ i : Fin 2, ∑ k : Fin 2 → Fin (2*N),
        ((f (k+diagPeriodLag N (diagAxisLag i))-f k)/r)^2 := by
    convert hscaled using 1
    · rw [← Finset.mul_sum, Finset.sum_comm]
      ring
    · simp only [div_pow, ← Finset.sum_div]
      have hs (i : Fin 2) : (∑ k : Fin 2 → Fin (2*N),
          (f (k+diagPeriodLag N (diagAxisLag i))-f k)^2) =
          ∑ k, (f k-f (k+diagPeriodLag N (diagAxisLag i)))^2 := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      simp_rw [hs]
      ring
  exact hrow.trans (diagSourceGrid_difference_energy Q j u)

end

end ASDExplicitGamma.Triadic
