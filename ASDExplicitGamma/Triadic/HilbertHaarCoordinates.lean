module

public import ASDExplicitGamma.Triadic.HilbertHaarProjection
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Exact normalized L2 Parseval for countable Hilbert coordinates. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- Finite Hilbert coordinates satisfy the normalized integrated Bessel inequality. -/
theorem hilbertEnergy_coordinates_finset_le {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (b : ι → E)
    (hb : Orthonormal ℝ b) {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) (s : Finset ι) :
    (∑ i ∈ s, energy Q (fun x => inner ℝ (b i) (F x))) ≤ hilbertEnergy Q F := by
  have hi (i : ι) : Integrable (fun x => (inner ℝ (b i) (F x))^2) (normalizedCubeMeasure Q) := by
    have h := ((innerSL ℝ (b i)).comp_memLp' hF).integrable_norm_pow (by norm_num : 2 ≠ 0)
    simpa only [Real.norm_eq_abs, sq_abs, Function.comp_apply, innerSL_apply_apply] using h
  simp only [energy_eq_integral_sq]
  rw [← integral_finsetSum s (fun i _ => hi i)]
  apply integral_mono_ae (integrable_finsetSum s (fun i _ => hi i)) (hF.integrable_norm_pow (by norm_num))
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs, sq_abs, Function.comp_apply, innerSL_apply_apply] using hb.sum_inner_products_le (s := s) (F x)

/-- The actual coordinate L2 energies form a summable series. -/
theorem hilbertEnergy_coordinates_summable {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (b : ι → E)
    (hb : Orthonormal ℝ b) {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    Summable (fun i => energy Q (fun x => inner ℝ (b i) (F x))) :=
  summable_of_sum_le (fun i => energy_nonneg Q (fun x => inner ℝ (b i) (F x))) (hilbertEnergy_coordinates_finset_le Q b hb hF)

/-- Parseval commutes with normalized cell integration for a countable Hilbert basis. -/
theorem hilbertEnergy_eq_tsum_coordinates {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Countable ι] (Q : TriadicCube d)
    (b : HilbertBasis ι ℝ E) {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q F = ∑' i, energy Q (fun x => inner ℝ (b i) (F x)) := by
  have hpoint (x : Vec d) : ‖F x‖^2 = ∑' i, (inner ℝ (b i) (F x))^2 := by
    simpa only [real_inner_self_eq_norm_sq, real_inner_comm (F x), ← pow_two] using
      (b.tsum_inner_mul_inner (F x) (F x)).symm
  have hi (i : ι) : Integrable (fun x => (inner ℝ (b i) (F x))^2) (normalizedCubeMeasure Q) := by
    have h := ((innerSL ℝ (b i)).comp_memLp' hF).integrable_norm_pow (by norm_num : 2 ≠ 0)
    simpa only [Real.norm_eq_abs, sq_abs, Function.comp_apply, innerSL_apply_apply] using h
  have hs := hilbertEnergy_coordinates_summable Q b b.orthonormal hF
  have hnorm : Summable (fun i => ∫ x, ‖(inner ℝ (b i) (F x))^2‖ ∂normalizedCubeMeasure Q) := by
    simpa only [Real.norm_of_nonneg (sq_nonneg _), energy_eq_integral_sq] using hs
  unfold hilbertEnergy
  simp_rw [hpoint]
  rw [← integral_tsum_of_summable_integral_norm hi hnorm]
  simp only [energy_eq_integral_sq]

end

end ASDExplicitGamma.Triadic
