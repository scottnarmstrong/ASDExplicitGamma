module

public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment

/-! # Exact matrix means and bias decomposition in the cold graph argument -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Expectation commutes with an actual fixed-matrix Frobenius product. -/
theorem integral_matrixFrobeniusInner_const {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} (P : Matrix n n ℝ) (Z : Ω → Matrix n n ℝ)
    (hZ : ∀ i j, Integrable (fun ω => Z ω i j) ℙ) :
    (∫ ω, matrixFrobeniusInner P (Z ω) ∂ℙ) = matrixFrobeniusInner P (matrixMean ℙ Z) := by
  unfold matrixFrobeniusInner matrixMean
  rw [integral_finsetSum Finset.univ (f := fun i ω => ∑ j, P i j*Z ω i j)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => (hZ i j).const_mul (P i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (f := fun j ω => P i j*Z ω i j)
    (fun j _ => (hZ i j).const_mul (P i j))]
  simp only [integral_const_mul]

/-- Entrywise matrix means preserve actual finite second-moment differences. -/
theorem matrixMean_sub {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} (A B : Ω → Matrix n n ℝ)
    (hA : ∀ i j, Integrable (fun ω => A ω i j) ℙ)
    (hB : ∀ i j, Integrable (fun ω => B ω i j) ℙ) :
    matrixMean ℙ (fun ω => A ω-B ω) = matrixMean ℙ A-matrixMean ℙ B := by
  ext i j
  exact integral_sub (hA i j) (hB i j)

/-- The exact negative-bias identity used by the five-sixths graph candidate. -/
theorem integral_matrixFrobeniusSq_bias_gap {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {P Q : Matrix n n ℝ} {Z : Ω → Matrix n n ℝ}
    (hZ : ∀ i j, MemLp (fun ω => Z ω i j) 2 ℙ) (hmean : matrixMean ℙ Z = P-Q) :
    (∫ ω, matrixFrobeniusSq (P-Z ω) ∂ℙ) = -matrixFrobeniusSq P+
      2*matrixFrobeniusInner P Q+(∫ ω, matrixFrobeniusSq (Z ω) ∂ℙ) := by
  have hi := integrable_matrixFrobeniusSq hZ
  have hc : Integrable (fun ω => matrixFrobeniusInner P (Z ω)) ℙ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      ((hZ i j).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).const_mul _))
  simp_rw [matrixFrobeniusSq_sub]
  rw [integral_sub (f := fun ω => matrixFrobeniusSq P+matrixFrobeniusSq (Z ω))
    (g := fun ω => 2*matrixFrobeniusInner P (Z ω)) ((integrable_const _).add hi) (hc.const_mul 2),
    integral_add (integrable_const _) hi,integral_const,probReal_univ,one_smul,integral_const_mul,
    integral_matrixFrobeniusInner_const P Z (fun i j => (hZ i j).integrable (by norm_num)),hmean]
  have he : matrixFrobeniusInner P (P-Q) = matrixFrobeniusSq P-matrixFrobeniusInner P Q := by
    unfold matrixFrobeniusInner matrixFrobeniusSq
    simp only [Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib,pow_two]
  rw [he]
  ring

/-- The actual matrix trace commutes with expectation. -/
theorem integral_matrix_trace {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} (A : Ω → Matrix n n ℝ) (hA : ∀ i, Integrable (fun ω => A ω i i) ℙ) :
    (∫ ω, (A ω).trace ∂ℙ) = (matrixMean ℙ A).trace := by
  unfold Matrix.trace matrixMean
  exact integral_finsetSum Finset.univ (fun i _ => hA i)

/-- An ordinary constant matrix has its literal expectation in a probability space. -/
theorem matrixMean_const {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (P : Matrix n n ℝ) :
    matrixMean ℙ (fun _ : Ω => P) = P := by
  ext i j
  simp only [matrixMean,integral_const,probReal_univ,one_smul]

/-- Subtracting a deterministic matrix subtracts its literal mean. -/
theorem matrixMean_sub_const {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] (A : Ω → Matrix n n ℝ) (P : Matrix n n ℝ)
    (hA : ∀ i j, Integrable (fun ω => A ω i j) ℙ) :
    matrixMean ℙ (fun ω => A ω-P) = matrixMean ℙ A-P := by
  rw [matrixMean_sub A (fun _ : Ω => P) hA (fun i j => integrable_const (P i j)),matrixMean_const]

end ASDExplicitGamma.Cold
