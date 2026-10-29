module

public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Statements.ShellVarianceSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions

namespace ASDExplicitGamma.Model

/-- The scalar stream observable associated with a finite weighted set of points. -/
def shellStreamObservable (n : ℕ) (x : Fin n → Homogenization.Vec 2)
    (t : Fin n → ℝ) (j : ShellField 2) : ℝ :=
  ∑ i, t i * j (x i) 1 0

/-- The frozen shell coordinates are independent under the prefix law. -/
theorem shellLevels_independent (M : Algsuperdiff.Section3.ABKModel 2) :
    iIndepFun
      (fun k : ℤ => fun F : ℤ → ShellField 2 => F k)
      M.P.toMeasure :=
  M.shellPrefix.independent

/-- Every finite linear combination of level-`k` stream values is the
zero-shell Gaussian observable after the exact triadic amplitude and spatial
rescaling. Its variance is the product-q3 covariance evaluated at scale
`3^k`. -/
theorem shellStream_linearCombination_law
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ)
    (n : ℕ) (x : Fin n → Homogenization.Vec 2) (t : Fin n → ℝ) :
    Measure.map (shellStreamObservable n x t)
        (ShellField.shellMarginalLaw M.P k).toMeasure =
      gaussianReal 0 (Real.toNNReal (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        ∑ i, ∑ j, t i * t j *
          q3Cov (((3 : ℝ) ^ k)⁻¹ * ((x i - x j) 0)) *
          q3Cov (((3 : ℝ) ^ k)⁻¹ * ((x i - x j) 1)))) := by
  let amp : ℝ := Real.rpow 3 (M.gamma * (k : ℝ))
  let scale : ℝ := (3 : ℝ) ^ k
  let x' : Fin n → Homogenization.Vec 2 := fun i => scale⁻¹ • x i
  have hAmpSq : amp ^ 2 = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
    dsimp [amp]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (k : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hscale :
      ∀ i j, (x' i - x' j) = scale⁻¹ • (x i - x j) := by
    intro i j
    ext r
    simp [x', scale, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcoeff : ∀ i j, (amp * t i) * (amp * t j) = amp ^ 2 * (t i * t j) := by
    intro i j
    ring
  have hvar : h ^ 2 * (∑ i, ∑ j, (amp * t i) * (amp * t j) *
        q3Cov ((x' i - x' j) 0) * q3Cov ((x' i - x' j) 1)) =
      h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        ∑ i, ∑ j, t i * t j *
          q3Cov (scale⁻¹ * ((x i - x j) 0)) *
          q3Cov (scale⁻¹ * ((x i - x j) 1)) := by
    simp_rw [hscale, Pi.smul_apply, smul_eq_mul]
    simp_rw [hcoeff]
    have hsum :
        (∑ i, ∑ j, amp ^ 2 * (t i * t j *
          q3Cov (scale⁻¹ * ((x i - x j) 0)) *
          q3Cov (scale⁻¹ * ((x i - x j) 1)))) =
        amp ^ 2 * ∑ i, ∑ j, t i * t j *
          q3Cov (scale⁻¹ * ((x i - x j) 0)) *
          q3Cov (scale⁻¹ * ((x i - x j) 1)) := by
      simp_rw [Finset.mul_sum]
    calc
      _ = h ^ 2 * (∑ i, ∑ j, amp ^ 2 * (t i * t j *
          q3Cov (scale⁻¹ * ((x i - x j) 0)) *
          q3Cov (scale⁻¹ * ((x i - x j) 1)))) := by
            congr 2
            funext i
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = h ^ 2 * (amp ^ 2 * (∑ i, ∑ j, t i * t j *
          q3Cov (scale⁻¹ * ((x i - x j) 0)) *
          q3Cov (scale⁻¹ * ((x i - x j) 1)))) := by rw [hsum]
      _ = _ := by rw [hAmpSq]; ring
  have hEvalMeas : Measurable (shellStreamObservable n x t) := by
    unfold shellStreamObservable
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.mul (ShellField.measurable_eval_entry (x i) 1 0)
  calc
    Measure.map (shellStreamObservable n x t)
        (ShellField.shellMarginalLaw M.P k).toMeasure =
        Measure.map (fun j => shellStreamObservable n x t
          (ShellField.triadicScale M.gamma k j))
          (ShellField.zeroShellLaw M.P).toMeasure := by
      rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map,
        Measure.map_map hEvalMeas (ShellField.measurable_triadicScale M.gamma k)]
      rfl
    _ = Measure.map (shellStreamObservable n x' (amp • t))
        (ShellField.zeroShellLaw M.P).toMeasure := by
      apply Measure.map_congr
      filter_upwards with j
      simp only [shellStreamObservable,
        ShellField.triadicScale_apply, amp, x', scale, Pi.smul_apply,
        Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = gaussianReal 0 (Real.toNNReal (h ^ 2 *
          ∑ i, ∑ j, (amp * t i) * (amp * t j) *
            q3Cov ((x' i - x' j) 0) * q3Cov ((x' i - x' j) 1))) :=
      hM.2 n x' (amp • t)
    _ = _ := by rw [hvar]

/-- The variance sum reindexed downward from level `m` is the frozen geometric
formula. The index `n` corresponds to the shell level `m - n`, so this is the
one-sided shell sum over all integer levels at most `m`. -/
noncomputable def shellVarianceSeries (h γ : ℝ) (m : ℤ) : ℕ → ℝ :=
  fun n => h ^ 2 * (3 : ℝ) ^ (2 * γ * ((m : ℝ) - (n : ℝ)))

theorem shellVarianceSeries_eq_shellVarianceSum
    (h γ : ℝ) (m : ℤ) (hγ : 0 < γ) :
    ∑' n : ℕ, shellVarianceSeries h γ m n =
      shellVarianceSum h γ m := by
  let r : ℝ := (3 : ℝ) ^ (-(2 * γ))
  have hr₀ : 0 ≤ r := by positivity
  have hr₁ : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm (n : ℕ) : shellVarianceSeries h γ m n =
      (h ^ 2 * (3 : ℝ) ^ (2 * γ * (m : ℝ))) * r ^ n := by
    dsimp [shellVarianceSeries, r]
    have hexp : 2 * γ * ((m : ℝ) - (n : ℝ)) =
        (2 * γ * (m : ℝ)) + (-2 * γ) * (n : ℝ) := by
      ring
    rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  calc
    ∑' n : ℕ, shellVarianceSeries h γ m n =
        ∑' n : ℕ, (h ^ 2 * (3 : ℝ) ^ (2 * γ * (m : ℝ))) * r ^ n :=
      tsum_congr hterm
    _ = (h ^ 2 * (3 : ℝ) ^ (2 * γ * (m : ℝ))) * ∑' n : ℕ, r ^ n :=
      tsum_mul_left
    _ = shellVarianceSum h γ m := by
      rw [tsum_geometric_of_lt_one hr₀ hr₁]
      simp [shellVarianceSum, r, div_eq_mul_inv]

end ASDExplicitGamma.Model
end
