/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import ASDExplicitGamma.Gaussian.TwoParameter
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Regularized real powers in the all-order heat inequality -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

private lemma p12_shifted_rpow_value_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Φ : E → ℝ} {C ε q : ℝ} {d N : ℕ}
    (hC : 0 ≤ C) (hval : ∀ x, |Φ x| ≤ C * (1 + ‖x‖) ^ d)
    (hΦ0 : ∀ x, 0 ≤ Φ x) (hε : 0 < ε) (hq0 : 0 ≤ q)
    (hqN : q ≤ (N : ℝ)) (x : E) :
    (Φ x + ε) ^ q ≤ (1 + C + ε) ^ N * (1 + ‖x‖) ^ (d * N) := by
  let A : ℝ := 1 + ‖x‖
  let B : ℝ := Φ x + ε
  have hA : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg x]
  have hB0 : 0 ≤ B := by dsimp [B]; nlinarith [hΦ0 x, hε]
  have hB : B ≤ (C + ε) * A ^ d := by
    have hΦbound : Φ x ≤ C * A ^ d := by
      dsimp [A]
      exact (le_abs_self _).trans (hval x)
    have hAd : 1 ≤ A ^ d := one_le_pow₀ hA
    dsimp [B]
    nlinarith [mul_nonneg (show 0 ≤ ε by linarith) (sub_nonneg.mpr hAd)]
  have hQ : 1 ≤ (1 + (C + ε) * A ^ d) := by
    have hcoef : 0 ≤ C + ε := by linarith
    have hpower : 0 ≤ A ^ d := pow_nonneg (by linarith [hA]) _
    nlinarith [mul_nonneg hcoef hpower]
  have hQ' : (1 + (C + ε) * A ^ d) ≤ (1 + C + ε) * A ^ d := by
    have hAd : 1 ≤ A ^ d := one_le_pow₀ hA
    nlinarith [mul_nonneg (show 0 ≤ C + ε by linarith) (sub_nonneg.mpr hAd)]
  calc
    B ^ q ≤ (1 + (C + ε) * A ^ d) ^ q :=
      Real.rpow_le_rpow hB0 (by linarith [hB]) hq0
    _ ≤ (1 + (C + ε) * A ^ d) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ hqN
    _ ≤ ((1 + C + ε) * A ^ d) ^ (N : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hQ' (Nat.cast_nonneg _)
    _ = (1 + C + ε) ^ N * A ^ (d * N) := by
      simp only [Real.rpow_natCast, mul_pow, pow_mul]

private lemma p12_shifted_rpow_negative_bound {ε x r : ℝ}
    (hε : 0 < ε) (hx : ε ≤ x) (hr : r ≤ 0) : x ^ r ≤ ε ^ r :=
  Real.rpow_le_rpow_of_nonpos hε hx hr

private lemma p12_fderiv_shifted_rpow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Φ : E → ℝ} (hΦ : ContDiff ℝ 2 Φ) {ε q : ℝ}
    (hε : 0 < ε) (hΦ0 : ∀ x, 0 ≤ Φ x) (x : E) :
    fderiv ℝ (fun y => (Φ y + ε) ^ q) x =
      (q * (Φ x + ε) ^ (q - 1)) • fderiv ℝ Φ x := by
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hΦder : HasFDerivAt (fun y => Φ y + ε) (fderiv ℝ Φ x) x :=
    (hΦ1.differentiable_one x).hasFDerivAt.add_const ε
  have hbase : Φ x + ε ≠ 0 := ne_of_gt (by linarith [hΦ0 x])
  have hp := hΦder.rpow_const (p := q) (Or.inl hbase)
  simpa only [Function.comp_def, hbase, smul_eq_mul, add_comm] using hp.fderiv

private lemma p12_fderiv_fderiv_shifted_rpow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) {ε q : ℝ} (hε : 0 < ε)
    (hΦ0 : ∀ x, 0 ≤ Φ x) (x u w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (Φ z + ε) ^ q) y w) x u =
      q * (Φ x + ε) ^ (q - 1) * fderiv ℝ (fun y => fderiv ℝ Φ y w) x u +
        q * (q - 1) * (Φ x + ε) ^ (q - 2) *
          fderiv ℝ Φ x u * fderiv ℝ Φ x w := by
  let A : E → ℝ := fun y => q * (Φ y + ε) ^ (q - 1)
  let B : E → ℝ := fun y => fderiv ℝ Φ y w
  have hinner (y : E) : fderiv ℝ (fun z => (Φ z + ε) ^ q) y w = A y * B y := by
    rw [p12_fderiv_shifted_rpow hΦ hε hΦ0 y]
    simp [A, B, smul_apply, smul_eq_mul, mul_assoc]
  have hAB : (fun y => fderiv ℝ (fun z => (Φ z + ε) ^ q) y w) = fun y => A y * B y :=
    funext hinner
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hΦder : HasFDerivAt (fun y => Φ y + ε) (fderiv ℝ Φ x) x :=
    (hΦ1.differentiable_one x).hasFDerivAt.add_const ε
  have hbase : Φ x + ε ≠ 0 := ne_of_gt (by linarith [hΦ0 x])
  have hAder : HasFDerivAt A
      ((q * (q - 1) * (Φ x + ε) ^ (q - 2)) • fderiv ℝ Φ x) x := by
    have hcoef : HasFDerivAt (fun y => q * (Φ y + ε) ^ (q - 1))
        ((q * (q - 1) * (Φ x + ε) ^ (q - 2)) • fderiv ℝ Φ x) x := by
      have hexp : q - 1 - 1 = q - 2 := by ring
      simpa [Function.comp_def, A, hexp, smul_smul, smul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (hΦder.rpow_const (p := q - 1) (Or.inl hbase)).const_mul q
    exact hcoef
  have hBcont : ContDiff ℝ 1 B := by
    have h := hΦ.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hp : ContDiff ℝ 1 (fun y : E => (y, w)) := contDiff_id.prodMk contDiff_const
    simpa [B, Function.comp_def] using h.comp hp
  have hBder : HasFDerivAt B (fderiv ℝ B x) x := (hBcont.differentiable_one x).hasFDerivAt
  have hprod := (hAder.mul hBder).fderiv
  rw [hAB]
  have hEval := congrArg (fun L : E →L[ℝ] ℝ => L u) hprod
  have hEval' : (fderiv ℝ (fun y => A y * B y) x) u =
      A x * fderiv ℝ B x u +
        (q * (q - 1) * (Φ x + ε) ^ (q - 2) * fderiv ℝ Φ x u) * B x := by
    calc
      _ = (fderiv ℝ (A * B) x) u := rfl
      _ = (A x • fderiv ℝ B x +
          B x • (q * (q - 1) * (Φ x + ε) ^ (q - 2)) • fderiv ℝ Φ x) u := hEval
      _ = _ := by simp [smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  calc
    _ = A x * fderiv ℝ B x u +
        (q * (q - 1) * (Φ x + ε) ^ (q - 2) * fderiv ℝ Φ x u) * B x := hEval'
    _ = _ := by simp only [A, B]

/-! The positive shift keeps every fractional derivative coefficient away
from its singular point.  The resulting test remains in the Gaussian heat
class with polynomially bounded derivatives. -/

theorem hasPolynomiallyBoundedC2Derivatives_positiveShift_rpow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (hΦ0 : ∀ x, 0 ≤ Φ x)
    {ε q : ℝ} (hε : 0 < ε) (hq : 0 < q) :
    HasPolynomiallyBoundedC2Derivatives (fun x => (Φ x + ε) ^ q) := by
  rcases hΦ with ⟨hΦC2, C, hC, d, hvalue, hfirst, hsecond⟩
  let N : ℕ := Nat.ceil q
  let D : ℕ := d * N + 2 * d
  let Q : ℝ := (1 + C + ε) ^ N
  let R₁ : ℝ := max Q (ε ^ (q - 1))
  let R₂ : ℝ := max Q (ε ^ (q - 2))
  let K : ℝ := Q + |q| * C * R₁ + |q * (q - 1)| * C ^ 2 * R₂
  have hN : q ≤ (N : ℝ) := by dsimp [N]; exact Nat.le_ceil q
  have hD0 : d * N ≤ D := by dsimp [D]; omega
  have hD1 : d * N + d ≤ D := by dsimp [D]; omega
  have hD2 : d * N + 2 * d = D := by rfl
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hR₂ : 0 ≤ R₂ := by dsimp [R₂]; positivity
  have hgrowth (x : E) (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ (N : ℝ)) :
      (Φ x + ε) ^ r ≤ Q * (1 + ‖x‖) ^ (d * N) := by
    have hh := p12_shifted_rpow_value_bound hC hvalue hΦ0 hε hr0 hrN x
    simpa only [Q, N] using hh
  have hpow₁ (x : E) : (Φ x + ε) ^ (q - 1) ≤ R₁ * (1 + ‖x‖) ^ (d * N) := by
    let B : ℝ := Φ x + ε
    let A : ℝ := 1 + ‖x‖
    have hB : ε ≤ B := by dsimp [B]; linarith [hΦ0 x]
    have hA : 1 ≤ A ^ (d * N) := by dsimp [A]; exact one_le_pow₀ (by linarith [norm_nonneg x])
    by_cases hr : 0 ≤ q - 1
    · have hh := hgrowth x (q - 1) hr (by linarith)
      dsimp [R₁, Q, A]
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hh := p12_shifted_rpow_negative_bound hε hB (le_of_not_ge hr)
      dsimp [R₁, A]
      calc
        _ ≤ ε ^ (q - 1) := hh
        _ ≤ max Q (ε ^ (q - 1)) := le_max_right _ _
        _ = (max Q (ε ^ (q - 1))) * 1 := by ring
        _ ≤ (max Q (ε ^ (q - 1))) * (1 + ‖x‖) ^ (d * N) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
  have hpow₂ (x : E) : (Φ x + ε) ^ (q - 2) ≤ R₂ * (1 + ‖x‖) ^ (d * N) := by
    let B : ℝ := Φ x + ε
    let A : ℝ := 1 + ‖x‖
    have hB : ε ≤ B := by dsimp [B]; linarith [hΦ0 x]
    have hA : 1 ≤ A ^ (d * N) := by dsimp [A]; exact one_le_pow₀ (by linarith [norm_nonneg x])
    by_cases hr : 0 ≤ q - 2
    · have hh := hgrowth x (q - 2) hr (by linarith)
      dsimp [R₂, Q, A]
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hh := p12_shifted_rpow_negative_bound hε hB (le_of_not_ge hr)
      dsimp [R₂, A]
      calc
        _ ≤ ε ^ (q - 2) := hh
        _ ≤ max Q (ε ^ (q - 2)) := le_max_right _ _
        _ = (max Q (ε ^ (q - 2))) * 1 := by ring
        _ ≤ (max Q (ε ^ (q - 2))) * (1 + ‖x‖) ^ (d * N) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
  have hC2 : ContDiff ℝ 2 (fun x => (Φ x + ε) ^ q) := by
    apply (hΦC2.add contDiff_const).rpow_const_of_ne
    intro x
    exact ne_of_gt (by linarith [hΦ0 x])
  refine ⟨hC2, K, hK, D, ?_, ?_, ?_⟩
  · intro x
    have hq0 : 0 ≤ q := le_of_lt hq
    have hh := hgrowth x q hq0 hN
    have hnon : 0 ≤ (Φ x + ε) ^ q := Real.rpow_nonneg (by linarith [hΦ0 x]) q
    rw [abs_of_nonneg hnon]
    dsimp [K, Q]
    have hpow : (1 + ‖x‖) ^ (d * N) ≤ (1 + ‖x‖) ^ D :=
      pow_le_pow_right₀ (by linarith [norm_nonneg x]) hD0
    calc
      _ ≤ Q * (1 + ‖x‖) ^ D := by
        exact hh.trans (mul_le_mul_of_nonneg_left hpow hQ)
      _ ≤ K * (1 + ‖x‖) ^ D := by
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [mul_nonneg (abs_nonneg q) (mul_nonneg hC hR₁), mul_nonneg (abs_nonneg (q*(q-1))) (mul_nonneg (sq_nonneg C) hR₂)]) (by positivity)
  · intro x
    rw [p12_fderiv_shifted_rpow hΦC2 hε hΦ0 x]
    have hpow := hpow₁ x
    have hbase0 : 0 ≤ Φ x + ε := by linarith [hΦ0 x, hε]
    have hcoeff : |q * (Φ x + ε) ^ (q - 1)| ≤ |q| * R₁ * (1 + ‖x‖) ^ (d * N) := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase0 _)]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hpow (abs_nonneg q)
    have hD : ‖fderiv ℝ Φ x‖ ≤ C * (1 + ‖x‖) ^ d := hfirst x
    have hpowD : (1 + ‖x‖) ^ (d * N) * (1 + ‖x‖) ^ d ≤ (1 + ‖x‖) ^ D := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
    calc
      ‖(q * (Φ x + ε) ^ (q - 1)) • fderiv ℝ Φ x‖ =
          |q * (Φ x + ε) ^ (q - 1)| * ‖fderiv ℝ Φ x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (|q| * R₁ * (1 + ‖x‖) ^ (d * N)) *
          (C * (1 + ‖x‖) ^ d) := by
        exact mul_le_mul hcoeff hD (norm_nonneg _) (by positivity)
      _ ≤ K * (1 + ‖x‖) ^ D := by
        have hcoeff' : |q| * R₁ * C ≤ K := by
          dsimp [K]
          have hsecondNonneg : 0 ≤ |q * (q - 1)| * C ^ 2 * R₂ :=
            mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) hR₂
          nlinarith [hQ, mul_nonneg (abs_nonneg q) (mul_nonneg hR₁ hC), hsecondNonneg]
        calc
          _ = (|q| * R₁ * C) *
              ((1 + ‖x‖) ^ (d * N) * (1 + ‖x‖) ^ d) := by ring
          _ ≤ (|q| * R₁ * C) * (1 + ‖x‖) ^ D :=
            mul_le_mul_of_nonneg_left hpowD (by positivity)
          _ ≤ K * (1 + ‖x‖) ^ D :=
            mul_le_mul_of_nonneg_right hcoeff' (by positivity)
  · intro x u w
    rw [p12_fderiv_fderiv_shifted_rpow hΦC2 hε hΦ0 x u w]
    let A : ℝ := 1 + ‖x‖
    have hbase0 : 0 ≤ Φ x + ε := by linarith [hΦ0 x, hε]
    have hDu : |fderiv ℝ Φ x u| ≤ C * A ^ d * ‖u‖ := by
      calc
        |fderiv ℝ Φ x u| = ‖fderiv ℝ Φ x u‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ Φ x‖ * ‖u‖ := (fderiv ℝ Φ x).le_opNorm _
        _ ≤ C * A ^ d * ‖u‖ := by
          exact mul_le_mul_of_nonneg_right (by simpa [A] using hfirst x) (norm_nonneg _)
    have hDw : |fderiv ℝ Φ x w| ≤ C * A ^ d * ‖w‖ := by
      calc
        |fderiv ℝ Φ x w| = ‖fderiv ℝ Φ x w‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ Φ x‖ * ‖w‖ := (fderiv ℝ Φ x).le_opNorm _
        _ ≤ C * A ^ d * ‖w‖ := by
          exact mul_le_mul_of_nonneg_right (by simpa [A] using hfirst x) (norm_nonneg _)
    have hSecond : |fderiv ℝ (fun y => fderiv ℝ Φ y w) x u| ≤
        C * A ^ d * ‖u‖ * ‖w‖ := by simpa [A] using hsecond x u w
    have hterm₁ : |q * (Φ x + ε) ^ (q - 1) *
        fderiv ℝ (fun y => fderiv ℝ Φ y w) x u| ≤
        (|q| * C * R₁) * A ^ (d * N + d) * ‖u‖ * ‖w‖ := by
      have hproduct : (Φ x + ε) ^ (q - 1) *
          |fderiv ℝ (fun y => fderiv ℝ Φ y w) x u| ≤
          (R₁ * A ^ (d * N)) * (C * A ^ d * ‖u‖ * ‖w‖) := by
        exact mul_le_mul (hpow₁ x) hSecond (abs_nonneg _) (by positivity)
      calc
        _ = |q| * ((Φ x + ε) ^ (q - 1) *
            |fderiv ℝ (fun y => fderiv ℝ Φ y w) x u|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase0 _)]
          ring
        _ ≤ |q| * ((R₁ * A ^ (d * N)) *
            (C * A ^ d * ‖u‖ * ‖w‖)) :=
          mul_le_mul_of_nonneg_left hproduct (abs_nonneg q)
        _ = _ := by rw [pow_add]; ring
    have hterm₂ : |q * (q - 1) * (Φ x + ε) ^ (q - 2) *
        fderiv ℝ Φ x u * fderiv ℝ Φ x w| ≤
        (|q * (q - 1)| * C ^ 2 * R₂) * A ^ (d * N + 2 * d) * ‖u‖ * ‖w‖ := by
      calc
        _ = |q * (q - 1)| *
            ((Φ x + ε) ^ (q - 2) * |fderiv ℝ Φ x u| *
              |fderiv ℝ Φ x w|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase0 _)]
          ring
        _ ≤ |q * (q - 1)| *
            ((R₂ * A ^ (d * N)) * (C * A ^ d * ‖u‖) *
              (C * A ^ d * ‖w‖)) := by
          apply mul_le_mul_of_nonneg_left
          · have hfirst := mul_le_mul (hpow₂ x) hDu (abs_nonneg _) (by positivity)
            have hsecond := mul_le_mul_of_nonneg_right hfirst (abs_nonneg (fderiv ℝ Φ x w))
            calc
              _ ≤ (R₂ * A ^ (d * N)) * (C * A ^ d * ‖u‖) *
                  |fderiv ℝ Φ x w| := by
                    exact hsecond
              _ ≤ (R₂ * A ^ (d * N)) * (C * A ^ d * ‖u‖) *
                  (C * A ^ d * ‖w‖) := by
                    exact mul_le_mul_of_nonneg_left hDw (by positivity)
          · exact abs_nonneg (q * (q - 1))
        _ = _ := by rw [pow_add]; ring
    have hcoefsum : |q| * C * R₁ + |q * (q - 1)| * C ^ 2 * R₂ ≤ K := by
      dsimp [K]
      have hfirstNonneg : 0 ≤ |q| * C * R₁ :=
        mul_nonneg (mul_nonneg (abs_nonneg q) hC) hR₁
      have hsecondNonneg : 0 ≤ |q * (q - 1)| * C ^ 2 * R₂ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) hR₂
      linarith [hQ, hfirstNonneg, hsecondNonneg]
    have hpowD1 : A ^ (d * N + d) ≤ A ^ D := by
      exact pow_le_pow_right₀ (by dsimp [A]; linarith [norm_nonneg x]) (by omega)
    have hpowD2 : A ^ (d * N + 2 * d) ≤ A ^ D := by rw [hD2]
    calc
      |q * (Φ x + ε) ^ (q - 1) *
          fderiv ℝ (fun y => fderiv ℝ Φ y w) x u +
        q * (q - 1) * (Φ x + ε) ^ (q - 2) *
          fderiv ℝ Φ x u * fderiv ℝ Φ x w| ≤
          |q * (Φ x + ε) ^ (q - 1) *
            fderiv ℝ (fun y => fderiv ℝ Φ y w) x u| +
          |q * (q - 1) * (Φ x + ε) ^ (q - 2) *
            fderiv ℝ Φ x u * fderiv ℝ Φ x w| := abs_add_le _ _
      _ ≤ (|q| * C * R₁) * A ^ (d * N + d) * ‖u‖ * ‖w‖ +
          (|q * (q - 1)| * C ^ 2 * R₂) * A ^ (d * N + 2 * d) * ‖u‖ * ‖w‖ :=
        add_le_add hterm₁ hterm₂
      _ ≤ K * A ^ D * ‖u‖ * ‖w‖ := by
        have hnorm : 0 ≤ ‖u‖ * ‖w‖ := by positivity
        calc
          _ = ((|q| * C * R₁) * A ^ (d * N + d) +
              (|q * (q - 1)| * C ^ 2 * R₂) * A ^ (d * N + 2 * d)) *
                (‖u‖ * ‖w‖) := by ring
          _ ≤ ((|q| * C * R₁) * A ^ D +
              (|q * (q - 1)| * C ^ 2 * R₂) * A ^ D) * (‖u‖ * ‖w‖) := by
                exact mul_le_mul_of_nonneg_right
                  (add_le_add
                    (mul_le_mul_of_nonneg_left hpowD1 (by positivity))
                    (mul_le_mul_of_nonneg_left hpowD2 (by positivity))) hnorm
          _ = (|q| * C * R₁ + |q * (q - 1)| * C ^ 2 * R₂) * A ^ D *
              (‖u‖ * ‖w‖) := by
            ring
          _ ≤ K * A ^ D * (‖u‖ * ‖w‖) := by
            apply mul_le_mul_of_nonneg_right _ hnorm
            exact mul_le_mul_of_nonneg_right hcoefsum (by positivity)
          _ = K * A ^ D * ‖u‖ * ‖w‖ := by ring

/-- The infinite Hessian trace obeys the ordinary second-order chain rule for a
strictly positive shifted power.  The two resulting series are separately
summable, so this identity retains the full gradient-square bracket term. -/
theorem modelCovarianceTrace_positiveShift_rpow
    {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦ0 : ∀ y, 0 ≤ Φ y) {ε q : ℝ} (hε : 0 < ε) (x : E) :
    modelCovarianceTrace (fun y => (Φ y + ε) ^ q) (fun j => T (v j)) x =
      q * (Φ x + ε) ^ (q - 1) *
          modelCovarianceTrace Φ (fun j => T (v j)) x +
        q * (q - 1) * (Φ x + ε) ^ (q - 2) *
          modelGradientSquareTrace Φ (fun j => T (v j)) x := by
  have hΦSecond := hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives hΦ
  have hsumΦ := summable_gaussianSeriesHeatTrace hA T Φ hΦSecond x 0 (fun _ => 0)
  have hsumΦ' : Summable (fun j => secondDirectionalDerivative Φ x (T (v j))) := by
    simpa [gaussianSeriesHeatArgument] using hsumΦ
  have hsumGrad := summable_gaussianSeriesPowerGradientSquareTerms hA T hΦ x
  have hsum1 : Summable (fun j => q * (Φ x + ε) ^ (q - 1) *
      secondDirectionalDerivative Φ x (T (v j))) :=
    hsumΦ'.mul_left (q * (Φ x + ε) ^ (q - 1))
  have hsum2 : Summable (fun j => q * (q - 1) * (Φ x + ε) ^ (q - 2) *
      (fderiv ℝ Φ x (T (v j))) ^ 2) :=
    hsumGrad.mul_left (q * (q - 1) * (Φ x + ε) ^ (q - 2))
  have hpoint (j : ℕ) :
      secondDirectionalDerivative (fun y => (Φ y + ε) ^ q) x (T (v j)) =
        q * (Φ x + ε) ^ (q - 1) * secondDirectionalDerivative Φ x (T (v j)) +
          q * (q - 1) * (Φ x + ε) ^ (q - 2) *
            (fderiv ℝ Φ x (T (v j))) ^ 2 := by
    simpa [secondDirectionalDerivative, pow_two, mul_assoc] using
      p12_fderiv_fderiv_shifted_rpow hΦ.1 hε hΦ0 x (T (v j)) (T (v j))
  change (∑' j, secondDirectionalDerivative (fun y => (Φ y + ε) ^ q) x (T (v j))) = _
  calc
    _ = ∑' j, (q * (Φ x + ε) ^ (q - 1) *
        secondDirectionalDerivative Φ x (T (v j)) +
        q * (q - 1) * (Φ x + ε) ^ (q - 2) *
          (fderiv ℝ Φ x (T (v j))) ^ 2) := by
      apply tsum_congr
      exact hpoint
    _ = (∑' j, q * (Φ x + ε) ^ (q - 1) *
        secondDirectionalDerivative Φ x (T (v j))) +
        ∑' j, q * (q - 1) * (Φ x + ε) ^ (q - 2) *
          (fderiv ℝ Φ x (T (v j))) ^ 2 := Summable.tsum_add hsum1 hsum2
    _ = _ := by
      simp only [modelCovarianceTrace, modelGradientSquareTrace, tsum_mul_left]

/-- The pointwise heat generator after applying a strictly positive shifted
real power. -/
noncomputable def modelPositiveShiftPowerHeatGenerator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → ℝ) (H : ℕ → E) (p ε : ℝ) (x : E) : ℝ :=
  p * (Φ x + ε) ^ (p - 1) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ H x) +
    (p * (p - 1) / 2) * (Φ x + ε) ^ (p - 2) * modelGradientSquareTrace Φ H x

/-- The observable, first generator and carré-du-champ along the actual
partially inserted cutoff-model path. -/
noncomputable def p12ModelObservablePath (K : Set (Vec 2)) [CompactSpace K] (m : ℤ)
    (Φ : C(K, ℝ) → ℝ) : ℝ → Cutoff.CutoffSample 2 → ℝ :=
  fun t ω => Φ (modelInsertedScalar K m t ω)

noncomputable def p12ModelGeneratorPath (K : Set (Vec 2)) [CompactSpace K] (m : ℤ)
    (Φ : C(K, ℝ) → ℝ) (H : ℕ → C(K, ℝ)) :
    ℝ → Cutoff.CutoffSample 2 → ℝ :=
  fun t ω => (1 / 2 : ℝ) * modelCovarianceTrace Φ H (modelInsertedScalar K m t ω)

noncomputable def p12ModelBracketPath (K : Set (Vec 2)) [CompactSpace K] (m : ℤ)
    (Φ : C(K, ℝ) → ℝ) (H : ℕ → C(K, ℝ)) :
    ℝ → Cutoff.CutoffSample 2 → ℝ :=
  fun t ω => modelGradientSquareTrace Φ H (modelInsertedScalar K m t ω)

/-- The heat-regularity package for one positive-shift power test.  These are
the exact differentiation and integrability outputs of GA-C2-TEST, separated
from the generator/bracket estimates. -/
structure P12RegularizedHeatData {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y G Γ : ℝ → Ω → ℝ) (p ε : ℝ) : Prop where
  moment_continuous :
    ContinuousOn (fun t => ∫ ω, (Y t ω + ε) ^ p ∂μ) (Icc 0 1)
  moment_positive :
    ∀ t ∈ Icc (0 : ℝ) 1, 0 < ∫ ω, (Y t ω + ε) ^ p ∂μ
  heat_derivative :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, (Y r ω + ε) ^ p ∂μ)
        (∫ ω, p * (Y t ω + ε) ^ (p - 1) * G t ω +
          (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ∂μ) t
  heat_integrable :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      Integrable (fun ω => p * (Y t ω + ε) ^ (p - 1) * G t ω +
        (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω) μ

/-- Polynomial-growth observables remain integrable along the actual partially
inserted cutoff-model path.  This is the pointwise integrability input used by
the regularized P12 heat data; it follows from the older-field moments, the
fresh-shell Gaussian realization, and their independence. -/
theorem p12_integrable_modelInserted_polynomial
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Ψ : C(K, ℝ) → ℝ) (hΨ : Measurable Ψ) (hgrowth : HasPolynomialGrowth Ψ)
    (t : ℝ) :
    Integrable (fun ω => Ψ (modelInsertedScalar K m t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := olderField K m
  let Y := fun ω : Cutoff.CutoffSample 2 =>
    shellFieldScalarRestriction K (ω.1 (m + 1))
  let Z := gaussianSeriesLimitE hA T
  let ν := μ.map X
  have hX : Measurable X := measurable_olderField K ell m hK
  have hY : Measurable Y := (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hZ : Measurable Z := (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hjoint : μ.map (fun ω => (X ω, Y ω)) =
      ν.prod (standardGaussianInfinitePi.map Z) := by
    rw [← hlaw]
    exact (indepFun_olderField_freshShell K M ell m hK).map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable
  have hprod : ν.prod (standardGaussianInfinitePi.map Z) =
      (ν.prod standardGaussianInfinitePi).map (Prod.map id Z) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map ν standardGaussianInfinitePi measurable_id hZ
  let f : C(K, ℝ) × C(K, ℝ) → ℝ := fun z => Ψ (z.1 + Real.sqrt t • z.2)
  have hf : Measurable f := hΨ.comp
    (measurable_fst.add (measurable_snd.const_smul (Real.sqrt t)))
  have hbase : Integrable (fun z : C(K, ℝ) × (ℕ → ℝ) =>
      Ψ (z.1 + Real.sqrt t • Z z.2)) (ν.prod standardGaussianInfinitePi) :=
    integrable_randomBaseHeatIntegrand hA T ν
      (integrable_polynomial_olderFieldLaw K M ell m hK) Ψ hΨ hgrowth t
  have hbase' : Integrable (f ∘ Prod.map id Z) (ν.prod standardGaussianInfinitePi) := by
    convert hbase using 1
    funext z
    simp [f, Z]
  have hmap : Integrable f ((ν.prod standardGaussianInfinitePi).map (Prod.map id Z)) := by
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_id.prodMap hZ).aemeasurable).mpr hbase'
  have hjointInt : Integrable f (μ.map (fun ω => (X ω, Y ω))) := by
    rw [hjoint, hprod]
    exact hmap
  have hpath :=
    (integrable_map_measure hf.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).mp hjointInt
  change Integrable (fun ω => Ψ (olderField K m ω + Real.sqrt t •
    shellFieldScalarRestriction K (ω.1 (m + 1)))) μ
  exact hpath

/-- A strictly positive regularized moment converts its one-sided differential
bound directly into the corresponding bound for the positive real root. -/
theorem p12_rpow_deriv_upper {F DF U : ℝ → ℝ} {p t : ℝ}
    (hp : 1 < p) (hFpos : 0 < F t) (hFder : HasDerivAt F (DF t) t)
    (hbound : DF t ≤ p * F t ^ (1 - p⁻¹) * U t) :
    deriv (fun s => F s ^ p⁻¹) t ≤ U t := by
  have hp0 : 0 < p := by linarith
  have hpow := hFder.rpow_const (p := p⁻¹) (Or.inl hFpos.ne')
  have hprod : F t ^ (p⁻¹ - 1) * F t ^ (1 - p⁻¹) = 1 := by
    rw [← Real.rpow_add hFpos]
    simp
  have hmul : p⁻¹ * F t ^ (p⁻¹ - 1) * (p * F t ^ (1 - p⁻¹)) = 1 := by
    calc
      _ = (p⁻¹ * p) *
          (F t ^ (p⁻¹ - 1) * F t ^ (1 - p⁻¹)) := by ring
      _ = 1 := by
        rw [inv_mul_cancel₀ hp0.ne', hprod]
        ring
  have hcoef : 0 ≤ p⁻¹ * F t ^ (p⁻¹ - 1) := by positivity
  have hh := mul_le_mul_of_nonneg_left hbound hcoef
  rw [← mul_assoc, hmul, one_mul] at hh
  rw [hpow.deriv]
  calc
    _ = p⁻¹ * F t ^ (p⁻¹ - 1) * DF t := by ring
    _ ≤ U t := hh

/-- The upper-derivative form of the fundamental theorem of calculus on a
closed subinterval. Strict positivity avoids any assertion at a zero moment. -/
theorem p12_integrated_rpow_upper {F DF U : ℝ → ℝ} {p s t : ℝ}
    (hp : 1 < p) (hFcont : ContinuousOn F (Icc 0 1))
    (hFpos : ∀ r ∈ Icc (0 : ℝ) 1, 0 < F r)
    (hFder : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (DF r) r)
    (hU : IntegrableOn U (Icc 0 1))
    (hbound : ∀ r ∈ Ioo (0 : ℝ) 1,
      DF r ≤ p * F r ^ (1 - p⁻¹) * U r)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    F t ^ p⁻¹ - F s ^ p⁻¹ ≤ ∫ r in s..t, U r := by
  let G : ℝ → ℝ := fun r => F r ^ p⁻¹
  let dG : ℝ → ℝ := fun r => DF r * p⁻¹ * F r ^ (p⁻¹ - 1)
  have hGcont : ContinuousOn G (Icc 0 1) := by
    exact hFcont.rpow_const fun r hr => Or.inr (by positivity : 0 ≤ p⁻¹)
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs ht
  have hUsub : IntegrableOn U (Icc s t) := hU.mono_set (Icc_subset_Icc hs ht)
  have hGcont' : ContinuousOn G (Icc s t) := hGcont.mono hsub
  apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst
    (g := G) (g' := dG) hGcont' ?_ hUsub ?_
  · intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt hs hr.1, lt_of_lt_of_le hr.2 ht⟩
    have hder := (hFder r hr').rpow_const (p := p⁻¹)
      (Or.inl (hFpos r (hsub ⟨hr.1.le, hr.2.le⟩)).ne')
    convert hder.hasDerivWithinAt (s := Ioi r) using 1
  · intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt hs hr.1, lt_of_lt_of_le hr.2 ht⟩
    have hroot := p12_rpow_deriv_upper hp (hFpos r (hsub ⟨hr.1.le, hr.2.le⟩))
      (hFder r hr') (hbound r hr')
    have hpow := (hFder r hr').rpow_const (p := p⁻¹)
      (Or.inl (hFpos r (hsub ⟨hr.1.le, hr.2.le⟩)).ne')
    have hdG : dG r = deriv (fun z => F z ^ p⁻¹) r := by
      rw [hpow.deriv]
    rw [hdG]
    exact hroot

/-! The Lp approximation and differential transport are separated from the
model-specific inputs.  The latter are exactly the heat identity and the
pathwise generator/carré-du-champ estimates. -/

/-- Adding a nonnegative constant changes a nonnegative finite Lp norm by at
most that constant, on a probability space. -/
theorem positiveLpNorm_add_const_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p ε : ℝ}
    (hp : 1 ≤ p) (hε : 0 ≤ ε) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hf : MemLp f (ENNReal.ofReal p) μ) :
    positiveLpNorm μ p (fun ω => f ω + ε) ≤
      positiveLpNorm μ p f + ε := by
  have hp0 : 0 < p := by linarith
  have hconst : MemLp (fun _ : Ω => ε) (ENNReal.ofReal p) μ := memLp_const ε
  have hsum : MemLp (fun ω => f ω + ε) (ENNReal.ofReal p) μ := hf.add hconst
  have hpow (g : Ω → ℝ) (hg0 : ∀ ω, 0 ≤ g ω) (hg : MemLp g (ENNReal.ofReal p) μ) :
      positiveLpNorm μ p g = (eLpNorm g (ENNReal.ofReal p) μ).toReal :=
    positiveLpNorm_eq_eLpNorm_toReal μ hp0 g hg0 hg
  have htriangle : eLpNorm (fun ω => f ω + ε) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ + eLpNorm (fun _ : Ω => ε) (ENNReal.ofReal p) μ :=
    eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)
  have hconstNorm : eLpNorm (fun _ : Ω => ε) (ENNReal.ofReal p) μ = ENNReal.ofReal ε := by
    rw [eLpNorm_const' ε (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
    rw [Real.enorm_of_nonneg hε]
    simp [measure_univ]
  have hleft := hpow (fun ω => f ω + ε) (fun ω => add_nonneg (hf0 ω) hε) hsum
  have hright := hpow f hf0 hf
  have hfinite1 := hsum.eLpNorm_ne_top
  have hfinite2 := hf.eLpNorm_ne_top
  have hsumFinite : eLpNorm f (ENNReal.ofReal p) μ + ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hfinite2, ENNReal.ofReal_ne_top⟩
  rw [hconstNorm] at htriangle
  have htoReal := ENNReal.toReal_mono hsumFinite htriangle
  calc
    positiveLpNorm μ p (fun ω => f ω + ε) =
        (eLpNorm (fun ω => f ω + ε) (ENNReal.ofReal p) μ).toReal := hleft
    _ ≤ (eLpNorm f (ENNReal.ofReal p) μ + ENNReal.ofReal ε).toReal := htoReal
    _ = positiveLpNorm μ p f + ε := by
      rw [ENNReal.toReal_add hfinite2 ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε]
      exact congrArg (fun x => x + ε) hright.symm

/-- The positive shift also dominates the original nonnegative Lp norm. -/
theorem positiveLpNorm_le_add_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p ε : ℝ} (hp : 0 < p)
    (hε : 0 ≤ ε) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hf : MemLp f (ENNReal.ofReal p) μ) :
    positiveLpNorm μ p f ≤ positiveLpNorm μ p (fun ω => f ω + ε) := by
  have hsum : MemLp (fun ω => f ω + ε) (ENNReal.ofReal p) μ :=
    hf.add (memLp_const ε)
  have hfNorm := positiveLpNorm_eq_eLpNorm_toReal μ hp f hf0 hf
  have hsumNorm := positiveLpNorm_eq_eLpNorm_toReal μ hp
    (fun ω => f ω + ε) (fun ω => add_nonneg (hf0 ω) hε) hsum
  have hmono : eLpNorm f (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => f ω + ε) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_ae_real hf.aestronglyMeasurable
    filter_upwards [] with ω
    calc
      ‖f ω‖ = f ω := Real.norm_of_nonneg (hf0 ω)
      _ ≤ f ω + ε := le_add_of_nonneg_right hε
  rw [hfNorm, hsumNorm]
  exact ENNReal.toReal_mono hsum.eLpNorm_ne_top hmono

/-- A heat derivative with generator bound 19 and bracket bound 16 yields
the regularized Lp differential estimate.  `hheat` is the differentiated
Gaussian heat identity supplied by GA-C2-TEST; `hgen` and `hbracket` are the
two pathwise outputs of the generator and bracket bounds. -/
theorem p12_regularized_heat_transport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y G Γ L : ℝ → Ω → ℝ) {p ε vbar : ℝ}
    (hp : 1 < p) (hε : 0 < ε) (hvbar : 0 ≤ vbar)
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (hL0 : ∀ t ω, 0 ≤ L t ω)
    (hYmem : ∀ t, MemLp (Y t) (ENNReal.ofReal p) μ)
    (hLmem : ∀ t, MemLp (L t) (ENNReal.ofReal p) μ)
    (hFcont : ContinuousOn (fun t => ∫ ω, (Y t ω + ε) ^ p ∂μ) (Icc 0 1))
    (hFpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ∫ ω, (Y t ω + ε) ^ p ∂μ)
    (hheat : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, (Y r ω + ε) ^ p ∂μ)
        (∫ ω, p * (Y t ω + ε) ^ (p - 1) * G t ω +
          (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ∂μ) t)
    (hheatInt : ∀ t ∈ Ioo (0 : ℝ) 1,
      Integrable (fun ω => p * (Y t ω + ε) ^ (p - 1) * G t ω +
        (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω) μ)
    (hgen : ∀ t ω, G t ω ≤ 19 * vbar * L t ω)
    (hbracket : ∀ t ω, Γ t ω ≤ 16 * vbar * Y t ω * L t ω)
    (hU : IntegrableOn (fun t => (19 + 8 * (p - 1)) * vbar *
      positiveLpNorm μ p (L t)) (Icc 0 1)) :
    (∀ t ∈ Ioo (0 : ℝ) 1,
      deriv (fun r => (∫ ω, (Y r ω + ε) ^ p ∂μ) ^ p⁻¹) t ≤
        (19 + 8 * (p - 1)) * vbar * positiveLpNorm μ p (L t)) ∧
    ((s t : ℝ) → 0 ≤ s → s ≤ t → t ≤ 1 →
      (∫ ω, (Y t ω + ε) ^ p ∂μ) ^ p⁻¹ -
        (∫ ω, (Y s ω + ε) ^ p ∂μ) ^ p⁻¹ ≤
          ∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
            positiveLpNorm μ p (L r)) := by
  have hp0 : 0 < p := by linarith
  have hcoef0 : 0 ≤ (19 + 8 * (p - 1)) * vbar := by positivity
  let F : ℝ → ℝ := fun t => ∫ ω, (Y t ω + ε) ^ p ∂μ
  let DF : ℝ → ℝ := fun t => ∫ ω,
    p * (Y t ω + ε) ^ (p - 1) * G t ω +
      (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ∂μ
  let U : ℝ → ℝ := fun t => (19 + 8 * (p - 1)) * vbar *
    positiveLpNorm μ p (L t)
  have hshiftMem (t : ℝ) : MemLp (fun ω => Y t ω + ε) (ENNReal.ofReal p) μ :=
    (hYmem t).add (memLp_const ε)
  have hmomentBound (t : ℝ) (ω : Ω) :
      p * (Y t ω + ε) ^ (p - 1) * G t ω +
        (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ≤
      p * (19 + 8 * (p - 1)) * vbar *
        ((Y t ω + ε) ^ (p - 1) * L t ω) := by
    have hbase : 0 < Y t ω + ε := by linarith [hY0 t ω]
    have hbase0 : 0 ≤ Y t ω + ε := hbase.le
    have hfirstCoeff : 0 ≤ p * (Y t ω + ε) ^ (p - 1) := by positivity
    have hfirst := mul_le_mul_of_nonneg_left (hgen t ω) hfirstCoeff
    have hsecondCoeff : 0 ≤ (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) := by
      positivity
    have hsecond := mul_le_mul_of_nonneg_left (hbracket t ω) hsecondCoeff
    have hYshift : Y t ω ≤ Y t ω + ε := by linarith
    have hpowmul : (Y t ω + ε) ^ (p - 2) * Y t ω ≤
        (Y t ω + ε) ^ (p - 1) := by
      have hone : Y t ω + ε = (Y t ω + ε) ^ (1 : ℝ) :=
        (Real.rpow_one (Y t ω + ε)).symm
      have hpow : (Y t ω + ε) ^ (p - 2) * (Y t ω + ε) =
          (Y t ω + ε) ^ (p - 1) := by
        calc
          _ = (Y t ω + ε) ^ (p - 2) * (Y t ω + ε) ^ (1 : ℝ) :=
            congrArg (fun z => (Y t ω + ε) ^ (p - 2) * z) hone
          _ = (Y t ω + ε) ^ ((p - 2) + 1) := (Real.rpow_add hbase _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ ≤ (Y t ω + ε) ^ (p - 2) * (Y t ω + ε) :=
          mul_le_mul_of_nonneg_left hYshift (Real.rpow_nonneg hbase0 _)
        _ = _ := hpow
    have hsecond' : (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) *
        (16 * vbar * Y t ω * L t ω) ≤
        (8 * p * (p - 1) * vbar) * ((Y t ω + ε) ^ (p - 1) * L t ω) := by
      rw [show (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) *
          (16 * vbar * Y t ω * L t ω) =
          (8 * p * (p - 1) * vbar) *
            ((Y t ω + ε) ^ (p - 2) * Y t ω * L t ω) by ring]
      have hinner : (Y t ω + ε) ^ (p - 2) * Y t ω * L t ω ≤
          (Y t ω + ε) ^ (p - 1) * L t ω :=
        mul_le_mul_of_nonneg_right hpowmul (hL0 t ω)
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    have hfirst' : p * (Y t ω + ε) ^ (p - 1) * G t ω ≤
        p * 19 * vbar * ((Y t ω + ε) ^ (p - 1) * L t ω) := by
      calc
        _ ≤ p * (Y t ω + ε) ^ (p - 1) * (19 * vbar * L t ω) := hfirst
        _ = _ := by ring
    have hsecond'' : (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ≤
        (8 * p * (p - 1) * vbar) * ((Y t ω + ε) ^ (p - 1) * L t ω) :=
      hsecond.trans hsecond'
    calc
      _ ≤ p * 19 * vbar * ((Y t ω + ε) ^ (p - 1) * L t ω) +
          (8 * p * (p - 1) * vbar) * ((Y t ω + ε) ^ (p - 1) * L t ω) :=
        add_le_add hfirst' hsecond''
      _ = _ := by ring
  have hDerivativeBound : ∀ t ∈ Ioo (0 : ℝ) 1,
      DF t ≤ p * F t ^ (1 - p⁻¹) * U t := by
    intro t ht
    have hshift0 (ω : Ω) : 0 ≤ Y t ω + ε := by linarith [hY0 t ω]
    have hprodInt := integrable_power_mul hp hshift0 (hshiftMem t) (hLmem t)
    have hpoint := hmomentBound t
    have hintle : DF t ≤ p * (19 + 8 * (p - 1)) * vbar *
        (∫ ω, (Y t ω + ε) ^ (p - 1) * L t ω ∂μ) := by
      change (∫ ω, p * (Y t ω + ε) ^ (p - 1) * G t ω +
          (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ∂μ) ≤ _
      calc
        _ ≤ ∫ ω, p * (19 + 8 * (p - 1)) * vbar *
            ((Y t ω + ε) ^ (p - 1) * L t ω) ∂μ := by
          apply integral_mono (hheatInt t ht) (hprodInt.const_mul _)
          intro ω
          exact hpoint ω
        _ = _ := by rw [integral_const_mul]
    have hholder := integral_power_mul_le μ hp hshift0
      (hL0 t) (hshiftMem t) (hLmem t)
    have hmul := mul_le_mul_of_nonneg_left hholder
      (by positivity : 0 ≤ p * (19 + 8 * (p - 1)) * vbar)
    have hF : F t = ∫ ω, (Y t ω + ε) ^ p ∂μ := rfl
    have hD' : p * F t ^ (1 - p⁻¹) * U t =
        p * (19 + 8 * (p - 1)) * vbar *
          ((∫ ω, (Y t ω + ε) ^ p ∂μ) ^ (1 - p⁻¹) *
            positiveLpNorm μ p (L t)) := by
      simp [F, U]
      ring
    change (∫ ω, p * (Y t ω + ε) ^ (p - 1) * G t ω +
        (p * (p - 1) / 2) * (Y t ω + ε) ^ (p - 2) * Γ t ω ∂μ) ≤ _ at hintle
    calc
      DF t ≤ p * (19 + 8 * (p - 1)) * vbar *
          (∫ ω, (Y t ω + ε) ^ (p - 1) * L t ω ∂μ) := hintle
      _ ≤ p * (19 + 8 * (p - 1)) * vbar *
          ((∫ ω, (Y t ω + ε) ^ p ∂μ) ^ (1 - p⁻¹) *
            positiveLpNorm μ p (L t)) := hmul
      _ = p * F t ^ (1 - p⁻¹) * U t := hD'.symm
  have hFcont' : ContinuousOn F (Icc (0 : ℝ) 1) := by simpa [F] using hFcont
  have hFpos' : ∀ r ∈ Icc (0 : ℝ) 1, 0 < F r := by simpa [F] using hFpos
  have hFder' : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (DF r) r := by
    intro r hr
    simpa [F, DF] using hheat r hr
  have hU' : IntegrableOn U (Icc (0 : ℝ) 1) := by simpa [U] using hU
  constructor
  · intro t ht
    exact p12_rpow_deriv_upper hp (hFpos' t ⟨le_of_lt ht.1, ht.2.le⟩)
      (hFder' t ht) (hDerivativeBound t ht)
  · intro s t hs hst ht
    exact p12_integrated_rpow_upper hp hFcont' hFpos' hFder' hU'
      hDerivativeBound hs hst ht

/-- Uniformly shifting a nonnegative Lp observable by `ε` changes its norm by
at most `ε`. This is the exact limit passage used after the regularized heat
estimate. -/
theorem p12_pass_to_zero_shift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p)
    {f g : Ω → ℝ} {R : ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ)
    (hshift : ∀ ε, 0 < ε →
      positiveLpNorm μ p (fun ω => g ω + ε) -
          positiveLpNorm μ p (fun ω => f ω + ε) ≤ R) :
    positiveLpNorm μ p g - positiveLpNorm μ p f ≤ R := by
  have hp0 : 0 < p := by linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlowerG := positiveLpNorm_le_add_const μ hp0 hε.le hg0 hg
  have hupperF := positiveLpNorm_add_const_le μ hp hε.le hf0 hf
  have hreg := hshift ε hε
  linarith

/-- Passing the regularized transport estimate to zero gives the unshifted
all-order inequality for every `p > 1`. -/
theorem p12_unregularized_heat_transport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y G Γ L : ℝ → Ω → ℝ) {p vbar : ℝ} (hp : 1 < p)
    (hvbar : 0 ≤ vbar) (hY0 : ∀ t ω, 0 ≤ Y t ω) (hL0 : ∀ t ω, 0 ≤ L t ω)
    (hYmem : ∀ t, MemLp (Y t) (ENNReal.ofReal p) μ)
    (hLmem : ∀ t, MemLp (L t) (ENNReal.ofReal p) μ)
    (hdata : ∀ ε, 0 < ε → P12RegularizedHeatData μ Y G Γ p ε)
    (hgen : ∀ t ω, G t ω ≤ 19 * vbar * L t ω)
    (hbracket : ∀ t ω, Γ t ω ≤ 16 * vbar * Y t ω * L t ω)
    (hU : IntegrableOn (fun t => (19 + 8 * (p - 1)) * vbar *
      positiveLpNorm μ p (L t)) (Icc 0 1)) :
    (s t : ℝ) → 0 ≤ s → s ≤ t → t ≤ 1 →
      positiveLpNorm μ p (Y t) - positiveLpNorm μ p (Y s) ≤
        ∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
          positiveLpNorm μ p (L r) := by
  intro s t hs hst ht
  apply p12_pass_to_zero_shift μ (le_of_lt hp) (hY0 s) (hY0 t)
    (hYmem s) (hYmem t)
  intro ε hε
  let D := hdata ε hε
  have hregularized := p12_regularized_heat_transport μ Y G Γ L hp hε hvbar
    hY0 hL0 hYmem hLmem D.moment_continuous D.moment_positive
    D.heat_derivative D.heat_integrable hgen hbracket hU
  have hroot := hregularized.2 s t hs hst ht
  have hshift (r : ℝ) :
      positiveLpNorm μ p (fun ω => Y r ω + ε) =
        (∫ ω, (Y r ω + ε) ^ p ∂μ) ^ p⁻¹ := rfl
  rw [hshift t, hshift s]
  exact hroot

/-- The first-moment endpoint of the all-order transport, using the ordinary
heat derivative (GA-HEAT) and the generator half of those bounds. -/
theorem p12_first_moment_heat_transport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y G L : ℝ → Ω → ℝ) {vbar : ℝ}
    (hLmem : ∀ t, MemLp (L t) 1 μ)
    (hFcont : ContinuousOn (fun t => ∫ ω, Y t ω ∂μ) (Icc 0 1))
    (hheat : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, Y r ω ∂μ) (∫ ω, G t ω ∂μ) t)
    (hGint : ∀ t ∈ Ioo (0 : ℝ) 1, Integrable (G t) μ)
    (hgen : ∀ t ω, G t ω ≤ 19 * vbar * L t ω)
    (hU : IntegrableOn (fun t => 19 * vbar * positiveLpNorm μ 1 (L t))
      (Icc 0 1)) :
    (s t : ℝ) → 0 ≤ s → s ≤ t → t ≤ 1 →
      positiveLpNorm μ 1 (Y t) - positiveLpNorm μ 1 (Y s) ≤
        ∫ r in s..t, 19 * vbar * positiveLpNorm μ 1 (L r) := by
  let F : ℝ → ℝ := fun t => ∫ ω, Y t ω ∂μ
  let DF : ℝ → ℝ := fun t => ∫ ω, G t ω ∂μ
  let U : ℝ → ℝ := fun t => 19 * vbar * positiveLpNorm μ 1 (L t)
  have hFcont' : ContinuousOn F (Icc (0 : ℝ) 1) := by simpa [F] using hFcont
  have hFder : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (DF r) r := by
    intro r hr
    simpa [F, DF] using hheat r hr
  have hbound : ∀ r ∈ Ioo (0 : ℝ) 1, DF r ≤ U r := by
    intro r hr
    have hGint' := hGint r hr
    have hLint : Integrable (L r) μ := (hLmem r).integrable (by norm_num)
    have hpoint : G r ≤ fun ω => 19 * vbar * L r ω := by
      intro ω
      exact hgen r ω
    have hle := integral_mono hGint' (hLint.const_mul (19 * vbar)) hpoint
    have hLp : positiveLpNorm μ 1 (L r) = ∫ ω, L r ω ∂μ := by
      simp [positiveLpNorm, Real.rpow_one]
    rw [integral_const_mul] at hle
    calc
      DF r = ∫ ω, G r ω ∂μ := rfl
      _ ≤ 19 * vbar * (∫ ω, L r ω ∂μ) := hle
      _ = U r := by simp [U, hLp]
  have hU' : IntegrableOn U (Icc (0 : ℝ) 1) := by simpa [U] using hU
  intro s t hs hst ht
  have hmain : F t - F s ≤ ∫ r in s..t, U r := by
    let hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs ht
    have hFcont'' : ContinuousOn F (Icc s t) := hFcont'.mono hsub
    have hUsub : IntegrableOn U (Icc s t) := hU'.mono_set hsub
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst
      (g := F) (g' := DF) hFcont'' ?_ hUsub ?_
    · intro r hr
      have hr' : r ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt hs hr.1, lt_of_lt_of_le hr.2 ht⟩
      convert (hFder r hr').hasDerivWithinAt (s := Ioi r) using 1
    · intro r hr
      have hr' : r ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt hs hr.1, lt_of_lt_of_le hr.2 ht⟩
      simpa [DF, U] using hbound r hr'
  simpa [F, U, positiveLpNorm, Real.rpow_one] using hmain

/-- The all-real-order P12 transport: the first moment uses the ordinary heat
identity, and every order above one uses the positive-shift argument. -/
theorem p12_all_order_heat_transport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y G Γ L : ℝ → Ω → ℝ) {p vbar : ℝ} (hp : 1 ≤ p)
    (hvbar : 0 ≤ vbar) (hY0 : ∀ t ω, 0 ≤ Y t ω) (hL0 : ∀ t ω, 0 ≤ L t ω)
    (hYmem : ∀ q, 1 < q → ∀ t, MemLp (Y t) (ENNReal.ofReal q) μ)
    (hLmem : ∀ q, 1 ≤ q → ∀ t, MemLp (L t) (ENNReal.ofReal q) μ)
    (hdata : ∀ q, 1 < q → ∀ ε, 0 < ε →
      P12RegularizedHeatData μ Y G Γ q ε)
    (hgen : ∀ t ω, G t ω ≤ 19 * vbar * L t ω)
    (hbracket : ∀ t ω, Γ t ω ≤ 16 * vbar * Y t ω * L t ω)
    (hFcont1 : ContinuousOn (fun t => ∫ ω, Y t ω ∂μ) (Icc 0 1))
    (hheat1 : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, Y r ω ∂μ) (∫ ω, G t ω ∂μ) t)
    (hGint : ∀ t ∈ Ioo (0 : ℝ) 1, Integrable (G t) μ)
    (hU : IntegrableOn (fun t => (19 + 8 * (p - 1)) * vbar *
      positiveLpNorm μ p (L t)) (Icc 0 1)) :
    ((1 < p ∧ p < 2) → ∀ ε, 0 < ε →
      ∀ t ∈ Ioo (0 : ℝ) 1,
        deriv (fun r => (∫ ω, (Y r ω + ε) ^ p ∂μ) ^ p⁻¹) t ≤
          (19 + 8 * (p - 1)) * vbar * positiveLpNorm μ p (L t)) ∧
    ((s t : ℝ) → 0 ≤ s → s ≤ t → t ≤ 1 →
      positiveLpNorm μ p (Y t) - positiveLpNorm μ p (Y s) ≤
        ∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
          positiveLpNorm μ p (L r)) := by
  constructor
  · intro hprange ε hε t ht
    have hpgt : 1 < p := hprange.1
    have hregularized := p12_regularized_heat_transport μ Y G Γ L hpgt hε
      hvbar hY0 hL0 (hYmem p hpgt) (hLmem p hp) 
      (hdata p hpgt ε hε).moment_continuous (hdata p hpgt ε hε).moment_positive
      (hdata p hpgt ε hε).heat_derivative (hdata p hpgt ε hε).heat_integrable
      hgen hbracket hU
    exact hregularized.1 t ht
  · intro s t hs hst ht
    by_cases hp1 : p = 1
    · subst p
      have hLmem1 : ∀ t, MemLp (L t) 1 μ := by
        intro t
        simpa using hLmem 1 (by norm_num) t
      have hU1 : IntegrableOn (fun t => 19 * vbar *
          positiveLpNorm μ 1 (L t)) (Icc 0 1) := by
        simpa using hU
      simpa [show (19 + 8 * ((1 : ℝ) - 1)) = 19 by ring] using
        (p12_first_moment_heat_transport μ Y G L hLmem1
          hFcont1 hheat1 hGint hgen hU1 s t hs hst ht)
    · have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
      exact (p12_unregularized_heat_transport μ Y G Γ L hpgt hvbar hY0 hL0
        (hYmem p hpgt) (hLmem p hp) (hdata p hpgt) hgen hbracket hU)
        s t hs hst ht

end ASDExplicitGamma.Gaussian
