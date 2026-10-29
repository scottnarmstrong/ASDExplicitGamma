module

public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # Entrywise integrability from the sharp spectral trace estimate -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- One actual squared entry is bounded by the full Frobenius square. -/
theorem matrix_entry_sq_le_frobenius {n : Type*} [Fintype n] (A : Matrix n n ℝ) (i j : n) :
    (A i j)^2 ≤ matrixFrobeniusSq A := by
  classical
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (A k l))) (Finset.mem_univ i))

/-- The spectral trace estimate supplies a deterministic bound for every response entry. -/
theorem matrix_entry_abs_le_trace_add_two {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hA : matrixFrobeniusSq (A-1) ≤ 2*T+T^2) (i j : n) : |A i j| ≤ T+2 := by
  have hs := (matrix_entry_sq_le_frobenius (A-1) i j).trans hA
  have hd : |(A-1) i j| ≤ T+1 := by
    have hh := sq_abs ((A-1) i j)
    nlinarith only [hT,hs,hh,abs_nonneg ((A-1) i j)]
  have hi : |(1 : Matrix n n ℝ) i j| ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have he : A i j = (A-1) i j+(1 : Matrix n n ℝ) i j := by simp
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [hd,hi])

/-- Genuine measurable matrix entries inherit L2 membership from a spectral trace bound. -/
theorem memLp_matrix_entry_of_spectral {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] {μprob : Measure Ω} [IsFiniteMeasure μprob]
    (A : Ω → Matrix n n ℝ) (T : Ω → ℝ) (hT : MemLp T 2 μprob)
    (hAm : Measurable A) (hTn : ∀ ω, 0 ≤ T ω)
    (hs : ∀ ω, matrixFrobeniusSq (A ω-1) ≤ 2*T ω+(T ω)^2) (i j : n) :
    MemLp (fun ω => A ω i j) 2 μprob := by
  apply (hT.add (memLp_const 2)).of_le
    ((measurable_pi_iff.mp (measurable_pi_iff.mp hAm i)) j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change |A ω i j| ≤ |T ω+2|
  rw [abs_of_nonneg (by linarith only [hTn ω] : 0 ≤ T ω+2)]
  exact matrix_entry_abs_le_trace_add_two (A ω) (hTn ω) (hs ω) i j

end ASDExplicitGamma.Cold
