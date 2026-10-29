module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import ASDExplicitGamma.Gaussian.RioTwoSum
public import ASDExplicitGamma.Cold.MatrixFrobeniusTriangle

/-! # Exact variance addition for actual independent centered matrices -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Matrix second moments add exactly for independent centered matrix-valued variables.
Independence is consumed through measurable entry projections. -/
theorem matrixFrobeniusL2_independent_sum_sq {Ω ι n : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype n] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {Y : ι → Ω → Matrix n n ℝ}
    (hY : ∀ a i j, MemLp (fun ω => Y a ω i j) 2 ℙ)
    (hIndep : ProbabilityTheory.iIndepFun Y ℙ)
    (hCenter : ∀ a i j, (∫ ω, Y a ω i j ∂ℙ) = 0) :
    (matrixFrobeniusL2 ℙ (fun ω => ∑ a, Y a ω))^2 = ∑ a, (matrixFrobeniusL2 ℙ (Y a))^2 := by
  classical
  rw [matrixFrobeniusL2_sq]
  simp_rw [matrixFrobeniusL2_sq]
  have hsum (i j : n) : MemLp (fun ω => (∑ a, Y a ω) i j) 2 ℙ := by
    simpa only [Matrix.sum_apply] using memLp_finsetSum Finset.univ (fun a _ => hY a i j)
  rw [integral_matrixFrobeniusSq ℙ _ hsum]
  simp_rw [integral_matrixFrobeniusSq ℙ _ (hY _)]
  simp only [Matrix.sum_apply]
  have he (i j : n) := Gaussian.rio_integral_centered_sum_sq (ℙ := ℙ) Finset.univ
    (fun a => hY a i j) (hIndep.comp (fun _ A => A i j)
      (fun _ => (measurable_pi_apply j).comp (measurable_pi_apply i))) (fun a => hCenter a i j)
  simp_rw [he]
  calc
    _ = ∑ i, ∑ a, ∑ j, ∫ ω, Y a ω i j ^ 2 ∂ℙ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The sharp independent centered matrix-sum bound has no dimension loss. -/
theorem matrixFrobeniusL2_independent_sum_le {Ω ι n : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype n] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {Y : ι → Ω → Matrix n n ℝ} {v : ℝ}
    (hY : ∀ a i j, MemLp (fun ω => Y a ω i j) 2 ℙ)
    (hIndep : ProbabilityTheory.iIndepFun Y ℙ)
    (hCenter : ∀ a i j, (∫ ω, Y a ω i j ∂ℙ) = 0)
    (hv : 0 ≤ v) (hcap : ∀ a, matrixFrobeniusL2 ℙ (Y a) ≤ v) :
    matrixFrobeniusL2 ℙ (fun ω => ∑ a, Y a ω) ≤ Real.sqrt (Fintype.card ι : ℝ)*v := by
  have he := matrixFrobeniusL2_independent_sum_sq hY hIndep hCenter
  have hc : (∑ a, (matrixFrobeniusL2 ℙ (Y a))^2) ≤ (Fintype.card ι:ℝ)*v^2 := by
    calc
      _ ≤ ∑ _ : ι, v^2 := Finset.sum_le_sum (fun a _ =>
        (sq_le_sq₀ (Real.sqrt_nonneg _) hv).mpr (hcap a))
      _ = _ := by simp
  have hr : (Real.sqrt (Fintype.card ι:ℝ)*v)^2 = (Fintype.card ι:ℝ)*v^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hv)).mp
    (by change (matrixFrobeniusL2 ℙ (fun ω => ∑ a, Y a ω))^2 ≤ _; rw [he,hr]; exact hc)

end ASDExplicitGamma.Cold
