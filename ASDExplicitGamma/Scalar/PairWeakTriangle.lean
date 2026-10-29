module

public import ASDExplicitGamma.Native.OldSignedFlatBounds
public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Public copy of the constant-one triangle inequality for the weak Haar norm. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators RealInnerProductSpace

noncomputable section

theorem weakHaarNorm_add_le (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    weakHaarNorm Q (fun x => f x + g x) ≤ weakHaarNorm Q f + weakHaarNorm Q g := by
  let w := (Real.sqrt 3)⁻¹
  let c₀ := 1 - w
  let weight (n : ℕ) := c₀ * w ^ n
  let a (n : ℕ) := Real.sqrt (weight n * energy Q (cubeProjection Q n f))
  let b (n : ℕ) := Real.sqrt (weight n * energy Q (cubeProjection Q n g))
  let c (n : ℕ) := Real.sqrt (weight n *
    energy Q (cubeProjection Q n (fun x => f x + g x)))
  have hroot : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hw : 0 ≤ w := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀, w]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hroot.le)
  have hweight (n : ℕ) : 0 ≤ weight n :=
    mul_nonneg hc₀ (pow_nonneg hw n)
  have hsf' : Summable (fun n : ℕ => w ^ n * energy Q (cubeProjection Q n f)) := by
    simpa only [w] using summable_weighted_projections Q hroot hf
  have hsg' : Summable (fun n : ℕ => w ^ n * energy Q (cubeProjection Q n g)) := by
    simpa only [w] using summable_weighted_projections Q hroot hg
  have hsf : Summable (fun n : ℕ => weight n * energy Q (cubeProjection Q n f)) := by
    convert hsf'.mul_left c₀ using 1
    ext n
    simp [weight, mul_assoc]
  have hsg : Summable (fun n : ℕ => weight n * energy Q (cubeProjection Q n g)) := by
    convert hsg'.mul_left c₀ using 1
    ext n
    simp [weight, mul_assoc]
  have hsq (u : Vec 2 → ℝ) (n : ℕ) :
      (Real.sqrt (weight n * energy Q (cubeProjection Q n u))) ^ 2 =
        weight n * energy Q (cubeProjection Q n u) :=
    Real.sq_sqrt (mul_nonneg (hweight n) (energy_nonneg Q _))
  have has : Summable (fun n : ℕ => (a n) ^ 2) := by
    simpa only [a, hsq] using hsf
  have hbs : Summable (fun n : ℕ => (b n) ^ 2) := by
    simpa only [b, hsq] using hsg
  have hpoint (n : ℕ) : c n ≤ a n + b n := by
    have h := hilbertL2Norm_add_le Q (projection_memLp Q n f 2)
      (projection_memLp Q n g 2)
    simp only [hilbertL2Norm, hilbertEnergy_real] at h
    dsimp [a, b, c]
    rw [projection_add Q n hf hg]
    rw [Real.sqrt_mul (hweight n), Real.sqrt_mul (hweight n), Real.sqrt_mul (hweight n)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (weight n))
  have hseries := sqrt_tsum_sq_le_of_pointwise has hbs
    (fun n => Real.sqrt_nonneg _) hpoint
  have hsc : Summable (fun n : ℕ => weight n *
      energy Q (cubeProjection Q n (fun x => f x + g x))) := by
    simpa only [c, hsq] using hseries.1
  have hsf'' : Summable (fun n : ℕ => w ^ n * energy Q (cubeProjection Q n
      (fun x => f x + g x))) := by
    have hwlt : w < 1 := (inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))).2 hroot
    have hc₀pos : 0 < c₀ := sub_pos.mpr hwlt
    have htmp := hsc.mul_left c₀⁻¹
    convert htmp using 1
    ext n
    dsimp [weight]
    field_simp [ne_of_gt hc₀pos]
  have hdualF := dualEnergy_eq_weighted_projections Q hroot hf
    (by simpa only [w] using hsf')
  have hdualG := dualEnergy_eq_weighted_projections Q hroot hg
    (by simpa only [w] using hsg')
  have hdualFG : dualEnergy Q (Real.sqrt 3) (fun x => f x + g x) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q
        (cubeProjection Q n (fun x => f x + g x)) := by
    exact dualEnergy_eq_weighted_projections Q hroot
      (show MemLp (fun x => f x + g x) 2 (normalizedCubeMeasure Q) from hf.add hg)
      hsf''
  have hsumA : (∑' n : ℕ, (a n) ^ 2) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n f) := by
    calc
      _ = ∑' n : ℕ, c₀ *
          (w ^ n * energy Q (cubeProjection Q n f)) := by
        apply tsum_congr
        intro n
        calc
          (a n) ^ 2 = weight n * energy Q (cubeProjection Q n f) := hsq f n
          _ = c₀ * (w ^ n * energy Q (cubeProjection Q n f)) := by ring
      _ = c₀ * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n f) := tsum_mul_left
      _ = _ := by rfl
  have hsumB : (∑' n : ℕ, (b n) ^ 2) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n g) := by
    calc
      _ = ∑' n : ℕ, c₀ *
          (w ^ n * energy Q (cubeProjection Q n g)) := by
        apply tsum_congr
        intro n
        calc
          (b n) ^ 2 = weight n * energy Q (cubeProjection Q n g) := hsq g n
          _ = c₀ * (w ^ n * energy Q (cubeProjection Q n g)) := by ring
      _ = c₀ * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n g) := tsum_mul_left
      _ = _ := by rfl
  have hsumC : (∑' n : ℕ, (c n) ^ 2) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q
        (cubeProjection Q n (fun x => f x + g x)) := by
    calc
      _ = ∑' n : ℕ, c₀ *
          (w ^ n * energy Q (cubeProjection Q n (fun x => f x + g x))) := by
        apply tsum_congr
        intro n
        calc
          (c n) ^ 2 = weight n *
              energy Q (cubeProjection Q n (fun x => f x + g x)) := hsq (fun x => f x + g x) n
          _ = c₀ * (w ^ n *
              energy Q (cubeProjection Q n (fun x => f x + g x))) := by ring
      _ = c₀ * ∑' n : ℕ, w ^ n * energy Q
          (cubeProjection Q n (fun x => f x + g x)) := tsum_mul_left
      _ = _ := by rfl
  have hrootBound : Real.sqrt (∑' n : ℕ, (c n) ^ 2) ≤
      Real.sqrt (∑' n : ℕ, (a n) ^ 2) + Real.sqrt (∑' n : ℕ, (b n) ^ 2) :=
    hseries.2
  have hnormF : weakHaarNorm Q f = Real.sqrt (∑' n : ℕ, (a n) ^ 2) := by
    unfold weakHaarNorm
    rw [hdualF, ← hsumA]
  have hnormG : weakHaarNorm Q g = Real.sqrt (∑' n : ℕ, (b n) ^ 2) := by
    unfold weakHaarNorm
    rw [hdualG, ← hsumB]
  have hnormFG : weakHaarNorm Q (fun x => f x + g x) =
      Real.sqrt (∑' n : ℕ, (c n) ^ 2) := by
    unfold weakHaarNorm
    rw [hdualFG, ← hsumC]
  rw [hnormFG, hnormF, hnormG]
  exact hrootBound

theorem vectorWeakHaarNorm_add_le (Q : TriadicCube 2)
    {f g : Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hg : ∀ i : Fin 2, MemLp (fun x => g x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarNorm Q (fun x i => f x i + g x i) ≤
      vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q g := by
  let a (i : Fin 2) := weakHaarNorm Q (fun x => f x i)
  let b (i : Fin 2) := weakHaarNorm Q (fun x => g x i)
  let c (i : Fin 2) := weakHaarNorm Q (fun x => f x i + g x i)
  have hpoint (i : Fin 2) : c i ≤ a i + b i :=
    weakHaarNorm_add_le Q (hf i) (hg i)
  have hsum : (∑ i : Fin 2, c i ^ 2) ≤ ∑ i : Fin 2, (a i + b i) ^ 2 :=
    Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpoint i) 2
  have h1 := Real.sqrt_le_sqrt hsum
  have h2 := sqrt_finset_sq_add_le Finset.univ a b
  have hfid (u : Vec 2 → Vec 2) :
      vectorWeakHaarNorm Q u =
        Real.sqrt (∑ i : Fin 2, weakHaarNorm Q (fun x => u x i) ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    change (vectorWeakHaarNorm Q u) ^ 2 = _
    rw [vectorWeakHaarNorm_sq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg
      (weakHaarNorm Q (fun x => u x i)))]
  calc
    vectorWeakHaarNorm Q (fun x i => f x i + g x i) = Real.sqrt (∑ i : Fin 2, c i ^ 2) := by
      simpa only [c] using hfid (fun x i => f x i + g x i)
    _ ≤ Real.sqrt (∑ i : Fin 2, (a i + b i) ^ 2) := h1
    _ ≤ Real.sqrt (∑ i : Fin 2, a i ^ 2) + Real.sqrt (∑ i : Fin 2, b i ^ 2) := h2
    _ = vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q g := by rw [← hfid, ← hfid]


end

end ASDExplicitGamma.Scalar
