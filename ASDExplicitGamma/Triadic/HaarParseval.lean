module

public import ASDExplicitGamma.Triadic.TriadicDualNorms
public import Homogenization.Besov.Duality.ProjectionLimit

/-! Complete scalar Haar Parseval and exact L2 residual tails. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- Actual triadic projections recover the full normalized L2 energy. -/
theorem energy_cubeProjection_tendsto {d : ℕ} (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Tendsto (fun n => energy Q (cubeProjection Q n f)) atTop (nhds (energy Q f)) := by
  have hc : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    exact NNReal.HolderConjugate.two_two.coe_ennreal.conjExponent_eq
  have h := tendsto_cubeBesovPairing_projection_left_of_memLp Q 2 f f hf
    (by simpa only [hc] using hf) (by norm_num) (by norm_num) (by rw [hc]; norm_num)
  have hp (n : ℕ) : cubeBesovPairing Q (cubeProjection Q n f) f = energy Q (cubeProjection Q n f) := by
    change pairing Q (cubeProjection Q n f) f = _
    rw [pairing_comm, pairing_projection_energy Q n hf]
  simp_rw [hp] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- The complete sequence of actual Haar increment energies is summable. -/
theorem summable_cubeIncrement_energy {d : ℕ} (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) : Summable (fun n => energy Q (cubeIncrement Q n f)) := by
  apply summable_of_sum_range_le (fun n => energy_nonneg Q (cubeIncrement Q n f))
  intro n
  cases n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using energy_nonneg Q f
  | succ n => rw [← energy_projection_sum Q n hf]; exact energy_projection_le Q n hf

/-- Complete Parseval for the exact source scalar Haar increments. -/
theorem tsum_cubeIncrement_energy {d : ℕ} (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (∑' n, energy Q (cubeIncrement Q n f)) = energy Q f := by
  have hsum := (summable_cubeIncrement_energy Q hf).hasSum.tendsto_sum_nat
  have hlim := energy_cubeProjection_tendsto Q hf
  have hshift := hsum.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, ← energy_projection_sum Q _ hf] at hshift
  exact tendsto_nhds_unique hshift hlim

/-- Every residual energy is exactly its infinite orthogonal Haar tail. -/
theorem energy_residual_eq_tsum_increments {d : ℕ} (Q : TriadicCube d) (j : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x-cubeProjection Q j f x) =
      ∑' n, energy Q (cubeIncrement Q (n+j+1) f) := by
  have ht := (summable_cubeIncrement_energy Q hf).sum_add_tsum_nat_add (j+1)
  rw [tsum_cubeIncrement_energy Q hf, ← energy_projection_sum Q j hf] at ht
  rw [energy_residual Q j hf]
  simp only [← add_assoc] at ht
  linarith only [ht]

end

end ASDExplicitGamma.Triadic
