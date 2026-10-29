module

public import ASDExplicitGamma.Gaussian.Q3RealizationLaw
public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance

/-! # The physical q3 shell covariance, with its actual spatial and amplitude scales -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

noncomputable def q3ModelLength (k : ℤ) : {l : ℝ // 0 < l} := ⟨3 ^ k, zpow_pos (by norm_num) k⟩

noncomputable def q3ModelAmplitude (M : ABKModel 2) (h : ℝ) (k : ℤ) : ℝ :=
  h * Real.rpow 3 (M.gamma * (k : ℝ))

/-- The actual scaled shell has exactly the covariance of the physical white-noise H³ factor. -/
theorem shellMarginalLaw_finite_observation (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) {K : Set (Vec 2)} {ι : Type} [Fintype ι]
    (x : ι → K) (t : ι → ℝ) :
    (ShellField.shellMarginalLaw M.P k).toMeasure.map (fun j => ∑ i, t i * j (x i) 1 0) =
      gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, t i * t j *
        (q3ModelAmplitude M h k ^ 2 * q3Cov (((x i).1 0 - (x j).1 0) / (q3ModelLength k).1) *
          q3Cov (((x i).1 1 - (x j).1 1) / (q3ModelLength k).1)))) := by
  let A : ℝ := Real.rpow 3 (M.gamma * (k : ℝ))
  let s : ℝ := ((3 : ℝ) ^ k)⁻¹
  let x' : ι → (univ : Set (Vec 2)) := fun i => ⟨s • (x i).1, mem_univ _⟩
  have hz := zeroShellLaw_map_finite_q3_observation M h hM x' (fun i => t i * A)
  have hm : Measurable (fun j : ShellField 2 => ∑ i, t i * j (x i) 1 0) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (ShellField.measurable_eval_entry (x i).1 1 0)
  rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map,
    Measure.map_map hm (ShellField.measurable_triadicScale M.gamma k)]
  have he : (fun j : ShellField 2 => ∑ i, t i * ShellField.triadicScale M.gamma k j (x i) 1 0) =
      fun j => ∑ i, (t i * A) * j (x' i) 1 0 := by
    funext j
    apply Finset.sum_congr rfl
    intro i _
    simp only [ShellField.triadicScale_apply, Matrix.smul_apply, smul_eq_mul, x', A, s]
    ring
  change (ShellField.zeroShellLaw M.P).toMeasure.map
    (fun j : ShellField 2 => ∑ i, t i * ShellField.triadicScale M.gamma k j (x i) 1 0) = _
  rw [he, hz]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he₀ : ((x' i).1 - (x' j).1) 0 = ((x i).1 0 - (x j).1 0) / (q3ModelLength k).1 := by
    simp only [x', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, q3ModelLength, s]
    ring
  have he₁ : ((x' i).1 - (x' j).1) 1 = ((x i).1 1 - (x j).1 1) / (q3ModelLength k).1 := by
    simp only [x', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, q3ModelLength, s]
    ring
  simp only [q3CovarianceKernel, he₀, he₁, q3ModelAmplitude, A]
  ring

end ASDExplicitGamma.Gaussian
