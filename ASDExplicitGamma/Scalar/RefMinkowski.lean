module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.MeasureTheory.Function.L2Space

/-! `L²`-Minkowski for nonnegative square-integrable functions, in integral form. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory

noncomputable section

theorem integral_sq_add_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X Y : Ω → ℝ) (hXm : AEStronglyMeasurable X μ)
    (hYm : AEStronglyMeasurable Y μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    Integrable (fun ω => (X ω + Y ω) ^ 2) μ ∧
      ∫ ω, (X ω + Y ω) ^ 2 ∂μ ≤
        (Real.sqrt (∫ ω, X ω ^ 2 ∂μ) + Real.sqrt (∫ ω, Y ω ^ 2 ∂μ)) ^ 2 := by
  have hXY : Integrable (fun ω => X ω * Y ω) μ := by
    refine Integrable.mono' ((hX2.add hY2).const_mul (1 / 2 : ℝ)) (hXm.mul hYm) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (X ω), sq_abs (Y ω), sq_nonneg (|X ω| - |Y ω|), abs_nonneg (X ω),
      abs_nonneg (Y ω)]
  have hint : Integrable (fun ω => (X ω + Y ω) ^ 2) μ := by
    have := (hX2.add (hXY.const_mul 2)).add hY2
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]; ring
  refine ⟨hint, ?_⟩
  set A := ∫ ω, X ω ^ 2 ∂μ with hA
  set B := ∫ ω, Y ω ^ 2 ∂μ with hB
  set Cc := ∫ ω, X ω * Y ω ∂μ with hC
  have hexp : ∫ ω, (X ω + Y ω) ^ 2 ∂μ = A + 2 * Cc + B := by
    have hf : (fun ω => (X ω + Y ω) ^ 2) = fun ω => (X ω ^ 2 + 2 * (X ω * Y ω)) + Y ω ^ 2 :=
      funext fun ω => by ring
    have h1 : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ := hX2.add (hXY.const_mul 2)
    rw [hf, integral_add h1 hY2, integral_add hX2 (hXY.const_mul 2), integral_const_mul]
  have hA0 : 0 ≤ A := integral_nonneg fun ω => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun ω => sq_nonneg _
  have hquad : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * Cc) * t + B := by
    intro t
    have hf : (fun ω => (t * X ω - Y ω) ^ 2) = fun ω =>
        (t ^ 2 * X ω ^ 2 + (-2 * t) * (X ω * Y ω)) + Y ω ^ 2 := funext fun ω => by ring
    have hnn : 0 ≤ ∫ ω, (t * X ω - Y ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hint2 : Integrable (fun ω => t ^ 2 * X ω ^ 2 + (-2 * t) * (X ω * Y ω)) μ :=
      (hX2.const_mul (t ^ 2)).add (hXY.const_mul (-2 * t))
    rw [hf, integral_add hint2 hY2, integral_add (hX2.const_mul (t ^ 2)) (hXY.const_mul (-2 * t)),
      integral_const_mul, integral_const_mul] at hnn
    nlinarith [hnn]
  have hdisc := discrim_le_zero hquad
  have hcs : Cc ≤ Real.sqrt A * Real.sqrt B := by
    unfold discrim at hdisc
    have h2 : Cc ^ 2 ≤ A * B := by nlinarith [hdisc]
    rw [← Real.sqrt_mul hA0]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h2)
  rw [hexp]
  have hsA := Real.sq_sqrt hA0
  have hsB := Real.sq_sqrt hB0
  nlinarith [hcs, hsA, hsB]

end

end ASDExplicitGamma.Scalar
