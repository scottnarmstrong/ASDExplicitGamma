module

public import ASDExplicitGamma.Triadic.DiagCertificates
public import ASDExplicitGamma.Triadic.TriadicDualNorms
public import ASDExplicitGamma.Triadic.VectorHaar

/-! Joint mean/centered-face Bessel inequality in the complete weak Haar norm. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

theorem diagProjection_sub_const (Q : TriadicCube 2) (j : ℕ)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    cubeProjection Q j (fun x => f x - c) =
      fun x => cubeProjection Q j f x - cubeProjection Q j (fun _ => c) x := by
  classical
  funext x
  unfold cubeProjection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  split_ifs
  · rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      integral_sub ((memLp_on_descendant_of_memLp hR hf).integrable one_le_two) (integrable_const c)]
  · ring

theorem diagIncrement_succ_sub_const (Q : TriadicCube 2) (j : ℕ)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    cubeIncrement Q (j + 1) (fun x => f x - c) = cubeIncrement Q (j + 1) f := by
  funext x
  simp only [cubeIncrement, diagProjection_sub_const Q _ hf]
  have hc := cubeIncrement_succ_const Q j c x
  change cubeProjection Q (j + 1) (fun _ => c) x - cubeProjection Q j (fun _ => c) x = 0 at hc
  linarith only [hc]

/-- Removing the mean subtracts exactly its square from the complete weak
energy, and leaves every positive-depth martingale increment unchanged. -/
theorem diagDualEnergy_sub_mean (Q : TriadicCube 2) (q : ℝ)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q q (fun x => f x - cubeAverage Q f) =
      dualEnergy Q q f - (cubeAverage Q f) ^ 2 := by
  have hmean : cubeAverage Q (fun x => f x - cubeAverage Q f) = 0 := by
    rw [cubeAverage_sub_const_of_memLp_two Q hf]
    ring
  unfold dualEnergy primalEnergy
  simp only [cubeIncrement_zero, energy_projection_zero, hmean, zero_pow (by norm_num : 2 ≠ 0),
    diagIncrement_succ_sub_const Q _ hf, zero_add]
  ring

/-- Joint Bessel for the mean and any centered positive-dual test. Applied
to the centered unit-cell coordinate this gives the exact weak-face disk. -/
theorem diagJointBessel (Q : TriadicCube 2)
    {f t : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (ht : MemLp t 2 (normalizedCubeMeasure Q)) (htmean : cubeAverage Q t = 0)
    (htsum : Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) t))) :
    (pairing Q f t) ^ 2 ≤ primalEnergy Q (Real.sqrt 3) t *
      (dualEnergy Q (Real.sqrt 3) f - (cubeAverage Q f) ^ 2) := by
  let g : Vec 2 → ℝ := fun x => f x - cubeAverage Q f
  have hg : MemLp g 2 (normalizedCubeMeasure Q) := hf.sub (memLp_const _)
  have hpair : pairing Q t g = pairing Q f t := by
    rw [pairing_comm, pairing_sub_left Q hf (memLp_const _) ht,
      pairing_comm Q (fun _ => cubeAverage Q f) t, pairing_const_right, htmean, zero_mul, sub_zero]
  have h := weak_positive_pairing_le Q ht hg htsum
  rw [hpair] at h
  have hnonneg : 0 ≤ positiveHaarNorm Q t * weakHaarNorm Q g :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := mul_self_le_mul_self (abs_nonneg (pairing Q f t)) h
  rw [← pow_two, ← pow_two, sq_abs, mul_pow, positiveHaarNorm, weakHaarNorm,
    Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) t),
    Real.sq_sqrt (dualEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) g),
    diagDualEnergy_sub_mean Q (Real.sqrt 3) hf] at hsq
  exact hsq

end

end ASDExplicitGamma.Triadic
