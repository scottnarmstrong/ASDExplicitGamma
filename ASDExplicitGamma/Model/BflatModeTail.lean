module

public import ASDExplicitGamma.Model.BflatActualBessel
public import ASDExplicitGamma.Model.BflatModeMasses
public import ASDExplicitGamma.Model.BflatModeSeries

/-! # Actual Gaussian B-flat tails and finite caps -/

@[expose] public section

open MeasureTheory Homogenization
open scoped BigOperators RealInnerProductSpace

namespace ASDExplicitGamma.Model

noncomputable def bflatQ3ModeScale (j : ℕ) : {l : ℝ // 0 < l} :=
  ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), bflatQ3ModeLength_pos j⟩

noncomputable def bflatQ3ProjectedSourceField {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (β : ℝ) (i : Fin 2) (j : ℕ) :
    (ℕ → ℝ) → HilbertVectorL2 bflatSquareObservationDomain :=
  (bflatProjectedSourceLinear i β (bflatQ3ModeScale j)) ∘
    Gaussian.q3H3Series (-1/2) (1/2) (-1/2) (1/2) β (bflatQ3ModeScale j) e

private theorem bflatQ3_modeWeight_nonneg (m n : ℕ) :
    0 ≤ ASDExplicitGamma.Numerics.Model.modeWeight m n := by
  unfold ASDExplicitGamma.Numerics.Model.modeWeight
  positivity

private theorem bflatQ3_modeWeight_le_one (m n : ℕ) :
    ASDExplicitGamma.Numerics.Model.modeWeight m n ≤ 1 := by
  have hden : 0 < ((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2 := by positivity
  have hnum : ((m+1:ℕ):ℝ)^2 ≤
      ((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2 := by nlinarith
  unfold ASDExplicitGamma.Numerics.Model.modeWeight
  exact (div_le_one hden).2 hnum

noncomputable def bflatQ3ModeProjectionTerm (j : ℕ) (p : ℕ × ℕ) : ℝ :=
  2 * ASDExplicitGamma.Numerics.Model.modeWeight p.1 p.2 *
    (ASDExplicitGamma.Numerics.Model.q3ModeCosine j p.1 *
      ASDExplicitGamma.Numerics.Model.q3ModeSine j p.2)

private theorem bflatQ3ModeProjectionTerm_nonneg (j : ℕ) (p : ℕ × ℕ) :
    0 ≤ bflatQ3ModeProjectionTerm j p := by
  unfold bflatQ3ModeProjectionTerm
  exact mul_nonneg (mul_nonneg (by norm_num) (bflatQ3_modeWeight_nonneg _ _))
    (mul_nonneg (bflatQ3ModeCosine_nonneg j p.1)
      (bflatQ3ModeSine_nonneg j p.2))

private theorem bflatQ3ModeProduct_summable (j : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      ASDExplicitGamma.Numerics.Model.q3ModeCosine j p.1 *
        ASDExplicitGamma.Numerics.Model.q3ModeSine j p.2) := by
  apply (summable_prod_of_nonneg
    (f := fun p : ℕ × ℕ =>
      ASDExplicitGamma.Numerics.Model.q3ModeCosine j p.1 *
        ASDExplicitGamma.Numerics.Model.q3ModeSine j p.2)
    (fun p => mul_nonneg (bflatQ3ModeCosine_nonneg j p.1)
      (bflatQ3ModeSine_nonneg j p.2))).2
  constructor
  · intro m
    exact (bflatQ3ModeSine_summable j).mul_left
      (ASDExplicitGamma.Numerics.Model.q3ModeCosine j m)
  · have hrow : (fun m : ℕ => ∑' n : ℕ,
        ASDExplicitGamma.Numerics.Model.q3ModeCosine j m *
          ASDExplicitGamma.Numerics.Model.q3ModeSine j n) =
      fun m => ASDExplicitGamma.Numerics.Model.q3ModeCosine j m *
        ∑' n : ℕ, ASDExplicitGamma.Numerics.Model.q3ModeSine j n := by
      funext m
      rw [tsum_mul_left]
    rw [hrow]
    exact (bflatQ3ModeCosine_summable j).mul_right _

theorem bflatQ3ModeProjectionTerm_summable (j : ℕ) :
    Summable (bflatQ3ModeProjectionTerm j) := by
  have hprod := bflatQ3ModeProduct_summable j
  apply Summable.of_nonneg_of_le (fun p => bflatQ3ModeProjectionTerm_nonneg j p)
    (fun p => ?_)
    (hprod.mul_left 2)
  have hweight := bflatQ3_modeWeight_le_one p.1 p.2
  have hprod0 := mul_nonneg (bflatQ3ModeCosine_nonneg j p.1)
    (bflatQ3ModeSine_nonneg j p.2)
  unfold bflatQ3ModeProjectionTerm
  nlinarith [mul_le_mul_of_nonneg_right hweight hprod0]

end ASDExplicitGamma.Model
