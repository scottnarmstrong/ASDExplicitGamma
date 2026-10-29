module

public import ASDExplicitGamma.Triadic.DiagSourceCellBounds
public import ASDExplicitGamma.Triadic.DiagSourceBudgets

/-! Scalar broken positive energy and the sharp actual source interpolation gains. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators Fin.CommRing

noncomputable section

/-- The square of the source scalar broken P norm, with normalized cell measure
and a normalized disjoint tile average. -/
def diagTiledScalarPositiveEnergy (Q : TriadicCube 2) (j : ℕ) (f : Vec 2 → ℝ) : ℝ :=
  descendantsAverage Q j (fun R => primalEnergy R (Real.sqrt 3) f)

/-- The actual H10 interpolant's broken positive gradient energy has constant one. -/
theorem diagInterpolant_h10_gradient_energy_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j u.toH1Function).grad ≤
      ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  let N := 3^j
  let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
  let f := diagOddGrid N (diagSourceMeans Q j u.toH1Function)
  let B (i : Fin 2) (k : Fin 2 → Fin N) := diagNodalGradientBudget (diagPeriodLag N)
    (diagAxisLag i) (diagAxisLag (diagOtherCoordinate i)) f (diagPeriodEmbed k)
  unfold ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy
  rw [diagDescendantsAverage_eq_grid_average]
  unfold vectorPositiveHaarEnergy
  calc
    _ ≤ ((N:ℝ)⁻¹)^2 * ∑ k : Fin 2 → Fin N, ∑ i : Fin 2, B i k/diagMeshRadius Q j^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum fun i _ => diagInterpolant_h10_cell_gradient_bound Q j u k i
    _ = ((N:ℝ)⁻¹)^2/diagMeshRadius Q j^2 * ∑ k : Fin 2 → Fin N, ∑ i : Fin 2, B i k := by
      simp only [← Finset.sum_div]
      ring
    _ ≤ _ := diagSourceGradientBudget_le Q j u

/-- The actual scalar interpolated-minus-cell-mean field has the sharp half-gain. -/
theorem diagInterpolant_h10_mean_positive_energy_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    diagTiledScalarPositiveEnergy Q j
      (fun x => (diagInterpolant Q j u.toH1Function).toFun x-cubeProjection Q j u.toH1Function.toFun x) ≤
      diagMeshRadius Q j^2/4 * ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  let N := 3^j
  let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
  let f := diagOddGrid N (diagSourceMeans Q j u.toH1Function)
  let B (k : Fin 2 → Fin N) := diagNodalResidualBudget (diagPeriodLag N)
    (diagAxisLag 0) (diagAxisLag 1) f (diagPeriodEmbed k)
  unfold diagTiledScalarPositiveEnergy
  rw [diagDescendantsAverage_eq_grid_average]
  calc
    _ ≤ ((N:ℝ)⁻¹)^2 * ∑ k : Fin 2 → Fin N, B k := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun k _ => diagInterpolant_h10_cell_residual_positive_bound Q j u k
    _ ≤ _ := diagSourceResidualBudget_le Q j u

/-- The full positive energy of an H1 cell dominates its L2 energy. -/
theorem diagH1_energy_le_primalEnergy (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    energy Q u.toFun ≤ primalEnergy Q (Real.sqrt 3) u.toFun := by
  have hq : 1 < Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3), Real.sqrt_nonneg (3:ℝ)]
  rw [primalEnergy_eq_abel Q hq u.memL2_normalizedCubeMeasure
    (positiveHaarResidualSeries_summable Q u.memL2_normalizedCubeMeasure
      u.grad_memL2_normalizedCubeMeasure u.hasWeakGradient)]
  apply le_add_of_nonneg_right
  exact mul_nonneg (sub_nonneg.mpr hq.le) (tsum_nonneg fun k =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (energy_nonneg Q _))

/-- The same sharp half-gain holds for the actual global normalized L2 energy. -/
theorem diagInterpolant_h10_mean_L2_energy_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    energy Q (fun x => (diagInterpolant Q j u.toH1Function).toFun x-cubeProjection Q j u.toH1Function.toFun x) ≤
      diagMeshRadius Q j^2/4 * ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  let e := fun x => (diagInterpolant Q j u.toH1Function).toFun x-cubeProjection Q j u.toH1Function.toFun x
  have he : MemLp e 2 (normalizedCubeMeasure Q) :=
    (diagInterpolant Q j u.toH1Function).memL2_normalizedCubeMeasure.sub
      (projection_memLp Q j u.toH1Function.toFun 2)
  rw [energy_eq_descendantsAverage Q j he, diagDescendantsAverage_eq_grid_average]
  have hpoint (k : Fin 2 → Fin (3^j)) : energy (diagMeshCell Q j k) e ≤
      primalEnergy (diagMeshCell Q j k) (Real.sqrt 3) e := by
    rw [diagEnergy_congr_ae _ (diagInterpolant_h10_minus_mean_ae Q j u k),
      diagPrimalEnergy_congr_ae _ _ (diagInterpolant_h10_minus_mean_ae Q j u k)]
    exact diagH1_energy_le_primalEnergy _ (diagBilinearH1 _ _)
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpoint k) (sq_nonneg _))
  simpa only [diagTiledScalarPositiveEnergy, diagDescendantsAverage_eq_grid_average] using
    diagInterpolant_h10_mean_positive_energy_le Q j u

end

end ASDExplicitGamma.Triadic
