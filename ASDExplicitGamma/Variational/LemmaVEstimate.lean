module

public import ASDExplicitGamma.Variational.LemmaVH1
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Cauchy–Schwarz and finite-direction duality for Lemma V. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open scoped BigOperators

/-- Cauchy–Schwarz for normalized finite averages of square roots. -/
theorem lemmaV_average_sqrt_products_le {ι : Type*} (s : Finset ι) (W E : ι → ℝ)
    (hW : ∀ i ∈ s, 0 ≤ W i) (hE : ∀ i ∈ s, 0 ≤ E i) :
    (s.card : ℝ)⁻¹ * (∑ i ∈ s, Real.sqrt (W i) * Real.sqrt (E i)) ≤
      Real.sqrt ((s.card : ℝ)⁻¹ * ∑ i ∈ s, W i) *
        Real.sqrt ((s.card : ℝ)⁻¹ * ∑ i ∈ s, E i) := by
  have hc : 0 ≤ (s.card : ℝ)⁻¹ := by positivity
  have hWs : 0 ≤ ∑ i ∈ s, W i := Finset.sum_nonneg hW
  have hEs : 0 ≤ ∑ i ∈ s, E i := Finset.sum_nonneg hE
  have hsum : 0 ≤ ∑ i ∈ s, Real.sqrt (W i) * Real.sqrt (E i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (W i))
    (fun i => Real.sqrt (E i))
  have hwEq : (∑ i ∈ s, Real.sqrt (W i) ^ 2) = ∑ i ∈ s, W i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hW i hi)
  have heEq : (∑ i ∈ s, Real.sqrt (E i) ^ 2) = ∑ i ∈ s, E i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hE i hi)
  rw [hwEq, heEq] at hcs
  apply (sq_le_sq₀ (mul_nonneg hc hsum)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg hc hWs), Real.sq_sqrt (mul_nonneg hc hEs)]
  have h := mul_le_mul_of_nonneg_left hcs (sq_nonneg (s.card : ℝ)⁻¹)
  nlinarith only [h]

/-- The load Cauchy–Schwarz step with the two H1 estimates. -/
theorem lemmaV_load_norm_product_sum_le {ι : Type*} (s : Finset ι)
    (W V T E : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hW : ∀ i ∈ s, 0 ≤ W i) (hV : ∀ i ∈ s, 0 ≤ V i)
    (hT : ∀ i ∈ s, 0 ≤ T i) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hWT : ∀ i ∈ s, W i ^ 2 ≤ B * T i)
    (hVE : ∀ i ∈ s, V i ^ 2 ≤ B * E i) :
    (∑ i ∈ s, W i * V i) ≤ B * Real.sqrt ((∑ i ∈ s, T i) * (∑ i ∈ s, E i)) := by
  have hWsum : (∑ i ∈ s, W i ^ 2) ≤ B * ∑ i ∈ s, T i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hWT
  have hVsum : (∑ i ∈ s, V i ^ 2) ≤ B * ∑ i ∈ s, E i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hVE
  have hprod := mul_le_mul hWsum hVsum (Finset.sum_nonneg fun i _ => sq_nonneg (V i))
    (mul_nonneg hB (Finset.sum_nonneg hT))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s W V
  have hnon : 0 ≤ (∑ i ∈ s, T i) * (∑ i ∈ s, E i) :=
    mul_nonneg (Finset.sum_nonneg hT) (Finset.sum_nonneg hE)
  apply (sq_le_sq₀ (Finset.sum_nonneg fun i hi => mul_nonneg (hW i hi) (hV i hi))
    (mul_nonneg hB (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hnon]
  nlinarith only [hcs, hprod]

/-- Unit-ball finite direction duality is sufficient for the full bracket. -/
theorem lemmaV_bracket_summable_and_le_of_unit_dual_bound {ι : Type*} (D : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hdual : ∀ (s : Finset ι) (c : ι → ℝ), (∑ i ∈ s, c i ^ 2) ≤ 1 →
      |∑ i ∈ s, c i * D i| ≤ C * Real.sqrt (∑ i ∈ s, c i ^ 2)) :
    Summable (fun i => D i ^ 2) ∧ (∑' i, D i ^ 2) ≤ C ^ 2 := by
  have hbound (s : Finset ι) : (∑ i ∈ s, D i ^ 2) ≤ C ^ 2 := by
    let L : ℝ := ∑ i ∈ s, D i ^ 2
    have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => sq_nonneg _
    by_cases hz : L = 0
    · change L ≤ C ^ 2
      rw [hz]
      exact sq_nonneg C
    have hp : 0 < L := lt_of_le_of_ne hL (Ne.symm hz)
    have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hp
    let c : ι → ℝ := fun i => D i / Real.sqrt L
    have hc : (∑ i ∈ s, c i ^ 2) = 1 := by
      simp only [c, div_pow, Real.sq_sqrt hL, ← Finset.sum_div]
      exact div_self hz
    have hpair : (∑ i ∈ s, c i * D i) = Real.sqrt L := by
      calc
        _ = L / Real.sqrt L := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [c]
          ring
        _ = Real.sqrt L := by
          apply (div_eq_iff hr.ne').mpr
          nlinarith only [Real.sq_sqrt hL]
    have h := hdual s c hc.le
    rw [hc, Real.sqrt_one, mul_one, hpair, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    calc
      L = Real.sqrt L ^ 2 := (Real.sq_sqrt hL).symm
      _ ≤ C ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr h
  exact ⟨summable_of_sum_le (fun i => sq_nonneg _) hbound,
    Real.tsum_le_of_sum_le (fun i => sq_nonneg _) hbound⟩

end ASDExplicitGamma.Variational
