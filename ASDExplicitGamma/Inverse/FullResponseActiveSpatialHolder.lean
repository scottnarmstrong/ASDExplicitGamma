module

public import ASDExplicitGamma.Inverse.FullResponseWaveCubeAverage

/-! Spatial fourth-moment pairing for the active full-response wave and
resolution-density terms. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory
open ASDExplicitGamma.Triadic.Support.ProjectedPoincare
open scoped ENNReal

noncomputable section

/-- On one normalized cube, the square of the wave mean is bounded by the
square root of its fourth spatial moment. -/
theorem cube_average_mean_square_le_fourth_sqrt
    (Q : TriadicCube 2) (f : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hf2 : MemLp (fun x => f x ^ 2) 2 (normalizedCubeMeasure Q)) :
    (cubeAverage Q f) ^ 2 ≤
      Real.sqrt (cubeAverage Q (fun x => f x ^ 4)) := by
  have hmean := cubeAverage_sq_le Q hf
  have hfour := cubeAverage_sq_le Q hf2
  have hfour' : (cubeAverage Q (fun x => f x ^ 2)) ^ 2 ≤
      cubeAverage Q (fun x => f x ^ 4) := by
    have heq : (fun x : Vec 2 => (f x ^ 2) ^ 2) = fun x => f x ^ 4 := by
      funext x
      ring
    rw [heq] at hfour
    exact hfour
  have hmean2 : 0 ≤ cubeAverage Q (fun x => f x ^ 2) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg (fun x => by positivity)
  calc
    (cubeAverage Q f) ^ 2 ≤ cubeAverage Q (fun x => f x ^ 2) := hmean
    _ = Real.sqrt ((cubeAverage Q (fun x => f x ^ 2)) ^ 2) := by
      rw [Real.sqrt_sq hmean2]
    _ ≤ Real.sqrt (cubeAverage Q (fun x => f x ^ 4)) :=
      Real.sqrt_le_sqrt hfour'

/-- The local wave-mean square times a local density second moment is
controlled by the geometric mean of the two fourth moments. This is the
single-cube input for the active spatial aggregation. -/
theorem cube_average_wave_density_product_le_fourth
    (Q : TriadicCube 2) (f g : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hf2 : MemLp (fun x => f x ^ 2) 2 (normalizedCubeMeasure Q))
    (hg2 : MemLp (fun x => g x ^ 2) 2 (normalizedCubeMeasure Q)) :
    (cubeAverage Q f) ^ 2 * cubeAverage Q (fun x => g x ^ 2) ≤
      Real.sqrt (cubeAverage Q (fun x => f x ^ 4) *
        cubeAverage Q (fun x => g x ^ 4)) := by
  have hwave := cube_average_mean_square_le_fourth_sqrt Q f hf hf2
  have hdensitySq := cubeAverage_sq_le Q hg2
  have hg2nonneg : 0 ≤ cubeAverage Q (fun x => g x ^ 2) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg (fun x => by positivity)
  have hdensity : cubeAverage Q (fun x => g x ^ 2) ≤
      Real.sqrt (cubeAverage Q (fun x => g x ^ 4)) := by
    have heq : (fun x : Vec 2 => (g x ^ 2) ^ 2) = fun x => g x ^ 4 := by
      funext x
      ring
    rw [heq] at hdensitySq
    calc
      cubeAverage Q (fun x => g x ^ 2) =
          Real.sqrt ((cubeAverage Q (fun x => g x ^ 2)) ^ 2) := by
            rw [Real.sqrt_sq hg2nonneg]
      _ ≤ Real.sqrt (cubeAverage Q (fun x => g x ^ 4)) :=
        Real.sqrt_le_sqrt hdensitySq
  have hf4nonneg : 0 ≤ cubeAverage Q (fun x => f x ^ 4) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg (fun x => by positivity)
  have hg4nonneg : 0 ≤ cubeAverage Q (fun x => g x ^ 4) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg (fun x => by positivity)
  calc
    _ ≤ Real.sqrt (cubeAverage Q (fun x => f x ^ 4)) *
        Real.sqrt (cubeAverage Q (fun x => g x ^ 4)) :=
      mul_le_mul hwave hdensity hg2nonneg (Real.sqrt_nonneg _)
    _ = _ := (Real.sqrt_mul hf4nonneg (cubeAverage Q (fun x => g x ^ 4))).symm

/-- Weighted Cauchy--Schwarz for the spatial cube sum. It keeps the exact
physical weights on each cube and introduces no count or supremum factor. -/
theorem weighted_finset_sqrt_product_le
    {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) :
    (∑ i ∈ s, w i * Real.sqrt (a i * b i)) ≤
      Real.sqrt (∑ i ∈ s, w i * a i) *
        Real.sqrt (∑ i ∈ s, w i * b i) := by
  have hcs := Real.sum_sqrt_mul_sqrt_le s
    (f := fun i => w i * a i) (g := fun i => w i * b i)
    (fun i => mul_nonneg (hw i) (ha i))
    (fun i => mul_nonneg (hw i) (hb i))
  have hterm (i : ι) (hi : i ∈ s) :
      Real.sqrt (w i * a i) * Real.sqrt (w i * b i) =
        w i * Real.sqrt (a i * b i) := by
    rw [Real.sqrt_mul (hw i) (a i), Real.sqrt_mul (hw i) (b i)]
    calc
      Real.sqrt (w i) * Real.sqrt (a i) *
          (Real.sqrt (w i) * Real.sqrt (b i)) =
          (Real.sqrt (w i) ^ 2) *
            (Real.sqrt (a i) * Real.sqrt (b i)) := by ring
      _ = w i * Real.sqrt (a i * b i) := by
        rw [Real.sq_sqrt (hw i), ← Real.sqrt_mul (ha i) (b i)]
  calc
    _ = ∑ i ∈ s, Real.sqrt (w i * a i) * Real.sqrt (w i * b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hterm i hi]
    _ ≤ _ := hcs

end
end ASDExplicitGamma.Inverse
