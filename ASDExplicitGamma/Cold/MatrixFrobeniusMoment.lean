module

public import ASDExplicitGamma.Cold.MatrixFrobeniusAlgebra

/-! # Actual L2 Frobenius norms and their Cauchy--Schwarz bound -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The ordinary annealed L2 Frobenius norm used by every cold graph candidate. -/
def matrixFrobeniusL2 {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) (A : Ω → Matrix n n ℝ) : ℝ :=
  Real.sqrt (∫ ω, matrixFrobeniusSq (A ω) ∂ℙ)

/-- Finite entrywise second moments integrate the actual Frobenius square. -/
theorem integrable_matrixFrobeniusSq {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A : Ω → Matrix n n ℝ} (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) :
    Integrable (fun ω => matrixFrobeniusSq (A ω)) ℙ :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hA i j).integrable_sq))

/-- The literal pointwise Frobenius norm belongs to L2. -/
theorem memLp_sqrt_matrixFrobeniusSq {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A : Ω → Matrix n n ℝ} (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) :
    MemLp (fun ω => Real.sqrt (matrixFrobeniusSq (A ω))) 2 ℙ := by
  have hi := integrable_matrixFrobeniusSq hA
  have hm := Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [Real.sq_sqrt (matrixFrobeniusSq_nonneg _)] using hi

/-- Every actual Frobenius L2 square is exactly its moment integral. -/
theorem matrixFrobeniusL2_sq {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) (A : Ω → Matrix n n ℝ) :
    (matrixFrobeniusL2 ℙ A)^2 = ∫ ω, matrixFrobeniusSq (A ω) ∂ℙ :=
  Real.sq_sqrt (integral_nonneg (fun ω => matrixFrobeniusSq_nonneg (A ω)))

/-- Cauchy--Schwarz for the actual random matrix product, with its exact Frobenius norms. -/
theorem abs_integral_matrixFrobeniusInner_le {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} {A B : Ω → Matrix n n ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 ℙ) :
    |∫ ω, matrixFrobeniusInner (A ω) (B ω) ∂ℙ| ≤ matrixFrobeniusL2 ℙ A*matrixFrobeniusL2 ℙ B := by
  have ha := memLp_sqrt_matrixFrobeniusSq hA
  have hb := memLp_sqrt_matrixFrobeniusSq hB
  have hi : Integrable (fun ω => matrixFrobeniusInner (A ω) (B ω)) ℙ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hA i j).integrable_mul (hB i j)))
  have hmono := integral_mono_ae hi.norm (ha.integrable_mul hb)
    (Filter.Eventually.of_forall (fun ω => abs_matrixFrobeniusInner_le (A ω) (B ω)))
  simp only [Real.norm_eq_abs] at hmono
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (show (2:ℝ).HolderConjugate 2 by constructor <;> norm_num)
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (matrixFrobeniusSq (A ω))))
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (matrixFrobeniusSq (B ω)))) (by simpa only [ENNReal.ofReal_ofNat] using ha) (by simpa only [ENNReal.ofReal_ofNat] using hb)
  norm_num only [Real.rpow_ofNat] at hh
  simp_rw [Real.sq_sqrt (matrixFrobeniusSq_nonneg _)] at hh
  rw [← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hh
  exact abs_integral_le_integral_abs.trans (hmono.trans hh)

/-- Adding an actual deterministic matrix preserves entrywise L2 integrability. -/
theorem memLp_matrix_const_add {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} [IsFiniteMeasure ℙ] (P : Matrix n n ℝ) {E : Ω → Matrix n n ℝ}
    (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 ℙ) (i j : n) :
    MemLp (fun ω => (P+E ω) i j) 2 ℙ :=
  (memLp_const (μ := ℙ) (p := 2) (P i j)).add (hE i j)

end ASDExplicitGamma.Cold
