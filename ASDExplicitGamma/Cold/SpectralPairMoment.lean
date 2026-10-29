module

public import ASDExplicitGamma.Cold.SpectralPair
public import Mathlib.Probability.Moments.Variance

/-! # The centered random-matrix spectral-pair estimate -/

@[expose] public section

namespace ASDExplicitGamma.Cold

open Matrix MeasureTheory ProbabilityTheory

/-- Entrywise expectation of a finite random matrix. -/
noncomputable def matrixMean {Ω n : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => ∫ omega, A omega i j ∂μ

/-- Finite sums in the squared Frobenius norm commute with expectation when
all matrix entries have finite second moments. -/
theorem integral_matrixFrobeniusSq {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] (μ : Measure Ω) (A : Ω → Matrix n n ℝ)
    (hA : ∀ i j, MemLp (fun omega => A omega i j) 2 μ) :
    (∫ omega, matrixFrobeniusSq (A omega) ∂μ) =
      ∑ i, ∑ j, ∫ omega, A omega i j ^ 2 ∂μ := by
  unfold matrixFrobeniusSq
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hA i j).integrable_sq))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum Finset.univ (fun j _ => (hA i j).integrable_sq)

/-- Centering minimizes the expected squared Frobenius distance from a
constant matrix. -/
theorem integral_matrixFrobeniusSq_center_le {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix n n ℝ)
    (B : Matrix n n ℝ) (hA : ∀ i j, MemLp (fun omega => A omega i j) 2 μ) :
    (∫ omega, matrixFrobeniusSq (A omega - matrixMean μ A) ∂μ) ≤
      ∫ omega, matrixFrobeniusSq (A omega - B) ∂μ := by
  have hC : ∀ i j, MemLp (fun omega => (A omega - matrixMean μ A) i j) 2 μ :=
    fun i j => (hA i j).sub (memLp_const _)
  have hB : ∀ i j, MemLp (fun omega => (A omega - B) i j) 2 μ :=
    fun i j => (hA i j).sub (memLp_const _)
  rw [integral_matrixFrobeniusSq μ _ hC, integral_matrixFrobeniusSq μ _ hB]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  change (∫ omega, (A omega i j - ∫ a, A a i j ∂μ) ^ 2 ∂μ) ≤
    ∫ omega, (A omega i j - B i j) ^ 2 ∂μ
  rw [← variance_eq_integral (hA i j).aemeasurable,
    ← variance_sub_const (hA i j).aestronglyMeasurable (B i j)]
  exact variance_le_expectation_sq (hB i j).aestronglyMeasurable

end ASDExplicitGamma.Cold
