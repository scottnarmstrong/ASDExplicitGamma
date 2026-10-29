module

public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment

/-! # The ordinary annealed Frobenius triangle inequality -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
namespace ASDExplicitGamma.Cold

/-- The source matrix L2 Frobenius triangle inequality, with actual entry integrability. -/
theorem matrixFrobeniusL2_add_le {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A B : Ω → Matrix n n ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 ℙ) :
    matrixFrobeniusL2 ℙ (fun ω => A ω+B ω) ≤ matrixFrobeniusL2 ℙ A+matrixFrobeniusL2 ℙ B := by
  have hiA := integrable_matrixFrobeniusSq hA
  have hiB := integrable_matrixFrobeniusSq hB
  have hiAB : Integrable (fun ω => matrixFrobeniusInner (A ω) (B ω)) ℙ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hA i j).integrable_mul (hB i j)))
  have he : (matrixFrobeniusL2 ℙ (fun ω => A ω+B ω))^2 =
      (matrixFrobeniusL2 ℙ A)^2+(matrixFrobeniusL2 ℙ B)^2+
        2*(∫ ω, matrixFrobeniusInner (A ω) (B ω) ∂ℙ) := by
    rw [matrixFrobeniusL2_sq,matrixFrobeniusL2_sq,matrixFrobeniusL2_sq]
    simp_rw [matrixFrobeniusSq_add]
    rw [integral_add (f := fun ω => matrixFrobeniusSq (A ω)+matrixFrobeniusSq (B ω))
      (g := fun ω => 2*matrixFrobeniusInner (A ω) (B ω)) (hiA.add hiB) (hiAB.const_mul 2),
      integral_add hiA hiB,integral_const_mul]
  have hc := (le_abs_self _).trans (abs_integral_matrixFrobeniusInner_le hA hB)
  have hn : 0 ≤ matrixFrobeniusL2 ℙ A := Real.sqrt_nonneg _
  have hm : 0 ≤ matrixFrobeniusL2 ℙ B := Real.sqrt_nonneg _
  have hsum : 0 ≤ matrixFrobeniusL2 ℙ (fun ω => A ω+B ω) := Real.sqrt_nonneg _
  nlinarith only [he,hc,hn,hm,hsum]

/-- A proved squared-distance cap can be used directly without another triangle loss. -/
theorem matrixFrobeniusL2_le_sqrt {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A : Ω → Matrix n n ℝ} {C : ℝ}
    (h : (∫ ω, matrixFrobeniusSq (A ω) ∂ℙ) ≤ C) :
    matrixFrobeniusL2 ℙ A ≤ Real.sqrt C := Real.sqrt_le_sqrt h

end ASDExplicitGamma.Cold
