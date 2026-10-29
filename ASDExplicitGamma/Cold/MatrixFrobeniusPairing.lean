module

public import ASDExplicitGamma.Cold.MatrixMeanAlgebra

/-! # Bilinearity of the actual annealed Frobenius pairing -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual annealed Frobenius pairing of two random matrices. -/
def matrixFrobeniusPairing {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) (A B : Ω → Matrix n n ℝ) : ℝ :=
  ∫ ω, matrixFrobeniusInner (A ω) (B ω) ∂ℙ

theorem integrable_matrixFrobeniusInner {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A B : Ω → Matrix n n ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 ℙ) :
    Integrable (fun ω => matrixFrobeniusInner (A ω) (B ω)) ℙ :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hA i j).integrable_mul (hB i j)))

theorem matrixFrobeniusInner_add_left {n : Type*} [Fintype n] (A B C : Matrix n n ℝ) :
    matrixFrobeniusInner (A+B) C = matrixFrobeniusInner A C+matrixFrobeniusInner B C := by
  simp only [matrixFrobeniusInner,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem matrixFrobeniusInner_sub_left {n : Type*} [Fintype n] (A B C : Matrix n n ℝ) :
    matrixFrobeniusInner (A-B) C = matrixFrobeniusInner A C-matrixFrobeniusInner B C := by
  simp only [matrixFrobeniusInner,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem matrixFrobeniusInner_comm {n : Type*} [Fintype n] (A B : Matrix n n ℝ) :
    matrixFrobeniusInner A B = matrixFrobeniusInner B A := by
  simp only [matrixFrobeniusInner,mul_comm]

theorem matrixFrobeniusPairing_add_left {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A B C : Ω → Matrix n n ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 ℙ)
    (hC : ∀ i j, MemLp (fun ω => C ω i j) 2 ℙ) :
    matrixFrobeniusPairing ℙ (fun ω => A ω+B ω) C =
      matrixFrobeniusPairing ℙ A C+matrixFrobeniusPairing ℙ B C := by
  unfold matrixFrobeniusPairing
  simp_rw [matrixFrobeniusInner_add_left]
  exact integral_add (integrable_matrixFrobeniusInner hA hC) (integrable_matrixFrobeniusInner hB hC)

theorem matrixFrobeniusPairing_comm {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) (A B : Ω → Matrix n n ℝ) :
    matrixFrobeniusPairing ℙ A B = matrixFrobeniusPairing ℙ B A := by
  unfold matrixFrobeniusPairing
  simp_rw [matrixFrobeniusInner_comm]

theorem matrixFrobeniusPairing_add_right {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A B C : Ω → Matrix n n ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 ℙ)
    (hC : ∀ i j, MemLp (fun ω => C ω i j) 2 ℙ) :
    matrixFrobeniusPairing ℙ A (fun ω => B ω+C ω) =
      matrixFrobeniusPairing ℙ A B+matrixFrobeniusPairing ℙ A C := by
  rw [matrixFrobeniusPairing_comm,matrixFrobeniusPairing_add_left hB hC hA]
  rw [matrixFrobeniusPairing_comm ℙ B A,matrixFrobeniusPairing_comm ℙ C A]

theorem matrixFrobeniusPairing_const_left {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} [IsFiniteMeasure ℙ] (P : Matrix n n ℝ) (B : Ω → Matrix n n ℝ)
    (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 ℙ) :
    matrixFrobeniusPairing ℙ (fun _ => P) B = matrixFrobeniusInner P (matrixMean ℙ B) :=
  integral_matrixFrobeniusInner_const P B (fun i j => (hB i j).integrable (by norm_num))

end ASDExplicitGamma.Cold
