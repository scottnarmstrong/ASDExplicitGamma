module

public import ASDExplicitGamma.Scalar.Lambda3Residue
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Real-variable core of the pure-source cross bound (source: `sensitivity_pure_source_full_norm_cross`
(1.1)-(2.1)). Cell-sum form: for a finite family of cells with inverse histories `B`, the pure source's
positive Haar energies `p`, circle energies `circ ≤ p`, cell energies `E`, splits `X + Y ≤ B E`, and weak
norms `a ≥ 0` (first output), `b ≥ 0` (reciprocal output), the pairing against an arbitrary source with
positive energies `pf, pg` is at most `1.41 √(Σ B p) √(Σ B (pf+pg))`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Finset

noncomputable section

theorem cs_sum {ι : Type*} (S : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ S, f i * g i ≤ Real.sqrt (∑ i ∈ S, f i ^ 2) * Real.sqrt (∑ i ∈ S, g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S f g
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc ∑ i ∈ S, f i * g i ≤ |∑ i ∈ S, f i * g i| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ S, f i * g i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt h

theorem sqrt_mul_form {B p b : ℝ} (hB : 0 ≤ B) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (h0 : B = 0 → b = 0) : Real.sqrt p * b ≤ Real.sqrt (B * p) * Real.sqrt (b ^ 2 / B) := by
  by_cases hB0 : B = 0
  · simp [h0 hB0]
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    rw [← Real.sqrt_mul (by positivity)]
    have : B * p * (b ^ 2 / B) = p * b ^ 2 := by field_simp
    rw [this, Real.sqrt_mul hp, Real.sqrt_sq hb]

theorem a_form {B X circ a c0 : ℝ} (hB : 0 ≤ B) (hX : 0 ≤ X) (hc : 0 ≤ circ) (hc0 : 0 ≤ c0)
    (ha0 : 0 ≤ a) (ha : a ≤ Real.sqrt X + c0 * B * Real.sqrt circ) :
    a ^ 2 / B ≤ (Real.sqrt (X / B) + c0 * Real.sqrt (B * circ)) ^ 2 := by
  by_cases hB0 : B = 0
  · simp [hB0]
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    set s := Real.sqrt B with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hBp
    have hss : s ^ 2 = B := Real.sq_sqrt hB
    have e1 : Real.sqrt (X / B) = Real.sqrt X / s := Real.sqrt_div hX B
    have e2 : Real.sqrt (B * circ) = s * Real.sqrt circ := Real.sqrt_mul hB circ
    rw [e1, e2]
    have h1 : a / s ≤ Real.sqrt X / s + c0 * (s * Real.sqrt circ) := by
      rw [div_le_iff₀ hs0]
      have : (Real.sqrt X / s + c0 * (s * Real.sqrt circ)) * s = Real.sqrt X + c0 * B * Real.sqrt circ := by
        rw [← hss]; field_simp
      rw [this]; exact ha
    have h2 : a ^ 2 / B = (a / s) ^ 2 := by rw [div_pow, hss]
    rw [h2]
    exact pow_le_pow_left₀ (div_nonneg ha0 hs0.le) h1 2

theorem pair_form_sum {ι : Type*} (S : Finset ι) (B p b : ι → ℝ)
    (hB : ∀ i ∈ S, 0 ≤ B i) (hp : ∀ i ∈ S, 0 ≤ p i) (hb0 : ∀ i ∈ S, 0 ≤ b i)
    (hbz : ∀ i ∈ S, B i = 0 → b i = 0) :
    ∑ i ∈ S, Real.sqrt (p i) * b i ≤
      Real.sqrt (∑ i ∈ S, B i * p i) * Real.sqrt (∑ i ∈ S, b i ^ 2 / B i) := by
  calc ∑ i ∈ S, Real.sqrt (p i) * b i
      ≤ ∑ i ∈ S, Real.sqrt (B i * p i) * Real.sqrt (b i ^ 2 / B i) :=
        Finset.sum_le_sum fun i hi => sqrt_mul_form (hB i hi) (hp i hi) (hb0 i hi) (hbz i hi)
    _ ≤ _ := by
      have := cs_sum S (fun i => Real.sqrt (B i * p i)) (fun i => Real.sqrt (b i ^ 2 / B i))
      have e1 : ∑ i ∈ S, Real.sqrt (B i * p i) ^ 2 = ∑ i ∈ S, B i * p i :=
        Finset.sum_congr rfl fun i hi => Real.sq_sqrt (mul_nonneg (hB i hi) (hp i hi))
      have e2 : ∑ i ∈ S, Real.sqrt (b i ^ 2 / B i) ^ 2 = ∑ i ∈ S, b i ^ 2 / B i :=
        Finset.sum_congr rfl fun i hi => Real.sq_sqrt (div_nonneg (sq_nonneg _) (hB i hi))
      rw [e1, e2] at this
      exact this

theorem two_cs (s1 s2 t1 t2 : ℝ) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    Real.sqrt s1 * Real.sqrt t1 + Real.sqrt s2 * Real.sqrt t2 ≤
      Real.sqrt (s1 + s2) * Real.sqrt (t1 + t2) := by
  rw [← Real.sqrt_mul (add_nonneg hs1 hs2)]
  set u := Real.sqrt s1
  set v := Real.sqrt s2
  set w1 := Real.sqrt t1
  set w2 := Real.sqrt t2
  have hu : u ^ 2 = s1 := Real.sq_sqrt hs1
  have hv : v ^ 2 = s2 := Real.sq_sqrt hs2
  have hw1 : w1 ^ 2 = t1 := Real.sq_sqrt ht1
  have hw2 : w2 ^ 2 = t2 := Real.sq_sqrt ht2
  refine Real.le_sqrt_of_sq_le ?_
  have e : (s1 + s2) * (t1 + t2) = (u ^ 2 + v ^ 2) * (w1 ^ 2 + w2 ^ 2) := by rw [hu, hv, hw1, hw2]
  rw [e]
  nlinarith [sq_nonneg (u * w2 - v * w1)]

theorem disk_total (Z y x Tn c0 : ℝ) (hZ : 0 ≤ Z) (hy : 0 ≤ y) (hx : 0 ≤ x) (hT : 0 ≤ Tn)
    (hc0 : 0 ≤ c0) (hc0le : c0 ≤ lambda3Alpha) (hen : x ^ 2 + y ^ 2 ≤ Z * y) (hTn : Tn ≤ c0 * Z) :
    y ^ 2 + (x + Tn) ^ 2 ≤ (141 / 100 : ℝ) ^ 2 * Z ^ 2 := by
  by_cases hZpos : Z = 0
  · subst hZpos
    have hx0 : x = 0 := by nlinarith
    have hy0 : y = 0 := by nlinarith
    have hT0 : Tn = 0 := le_antisymm (by simpa using hTn) hT
    rw [hx0, hy0, hT0]; norm_num
  · have hZp : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hZpos)
    have hyZ : y ≤ Z := by nlinarith
    set t := y / Z with ht
    set q := Tn / Z with hq
    have ht0 : 0 ≤ t := div_nonneg hy hZ
    have ht1 : t ≤ 1 := (div_le_one hZp).2 hyZ
    have hq0 : 0 ≤ q := div_nonneg hT hZ
    have hqle : q ≤ c0 := (div_le_iff₀ hZp).2 (by linarith)
    have hTq : Tn = q * Z := by rw [hq]; field_simp
    have hyt : y = t * Z := by rw [ht]; field_simp
    have hxle : x ≤ Z * Real.sqrt (t - t ^ 2) := by
      have hxx' : x ^ 2 ≤ Z ^ 2 * (t - t ^ 2) := by
        have : Z ^ 2 * (t - t ^ 2) = Z * y - y ^ 2 := by rw [hyt]; ring
        rw [this]; linarith
      calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
        _ ≤ Real.sqrt (Z ^ 2 * (t - t ^ 2)) := Real.sqrt_le_sqrt hxx'
        _ = Z * Real.sqrt (t - t ^ 2) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hZ]
    have hdisk := lambda3_joint_disk_residue t q ht0 ht1
    have hxT : x * Tn ≤ Z * Real.sqrt (t - t ^ 2) * (q * Z) := by
      rw [hTq]; exact mul_le_mul_of_nonneg_right hxle (by positivity)
    have hZy : Z * y = Z ^ 2 * t := by rw [hyt]; ring
    have hT2 : Tn ^ 2 = Z ^ 2 * q ^ 2 := by rw [hTq]; ring
    have h1 : y ^ 2 + (x + Tn) ^ 2 ≤ Z ^ 2 * (t + q ^ 2 + 2 * q * Real.sqrt (t - t ^ 2)) := by
      nlinarith [hen, hZy, hT2, hxT]
    have hmono : q ^ 2 + 1 / 2 + Real.sqrt (1 / 4 + q ^ 2) ≤
        lambda3Alpha ^ 2 + 1 / 2 + Real.sqrt (1 / 4 + lambda3Alpha ^ 2) := by
      have hqa : q ≤ lambda3Alpha := hqle.trans hc0le
      have h2 : q ^ 2 ≤ lambda3Alpha ^ 2 := pow_le_pow_left₀ hq0 hqa 2
      have := Real.sqrt_le_sqrt (show 1 / 4 + q ^ 2 ≤ 1 / 4 + lambda3Alpha ^ 2 by linarith)
      linarith
    have hfac2 : lambda3PureFactor ^ 2 ≤ (141 / 100 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) lambda3_pure_factor_lt_Dx.le 2
    have hfac3 : lambda3PureFactor ^ 2 = lambda3Alpha ^ 2 + 1 / 2 +
        Real.sqrt (1 / 4 + lambda3Alpha ^ 2) := by
      unfold lambda3PureFactor
      rw [Real.sq_sqrt (by positivity)]
    calc y ^ 2 + (x + Tn) ^ 2 ≤ Z ^ 2 * (t + q ^ 2 + 2 * q * Real.sqrt (t - t ^ 2)) := h1
      _ ≤ Z ^ 2 * (q ^ 2 + 1 / 2 + Real.sqrt (1 / 4 + q ^ 2)) :=
        mul_le_mul_of_nonneg_left hdisk (sq_nonneg _)
      _ ≤ Z ^ 2 * (lambda3PureFactor ^ 2) := by
        rw [hfac3]; exact mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      _ ≤ Z ^ 2 * (141 / 100 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hfac2 (sq_nonneg _)
      _ = _ := by ring

theorem first_output_sum {ι : Type*} (S : Finset ι) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (B X circ a : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hX : ∀ i ∈ S, 0 ≤ X i)
    (hcirc : ∀ i ∈ S, 0 ≤ circ i) (ha0 : ∀ i ∈ S, 0 ≤ a i)
    (ha : ∀ i ∈ S, a i ≤ Real.sqrt (X i) + c0 * B i * Real.sqrt (circ i)) :
    ∑ i ∈ S, a i ^ 2 / B i ≤
      (Real.sqrt (∑ i ∈ S, X i / B i) +
        Real.sqrt (∑ i ∈ S, (c0 * Real.sqrt (B i * circ i)) ^ 2)) ^ 2 := by
  set ξ : ι → ℝ := fun i => Real.sqrt (X i / B i) with hξ
  set τ : ι → ℝ := fun i => c0 * Real.sqrt (B i * circ i) with hτ
  have hξsq : ∑ i ∈ S, ξ i ^ 2 = ∑ i ∈ S, X i / B i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (div_nonneg (hX i hi) (hB i hi))
  have hxx0 : 0 ≤ ∑ i ∈ S, X i / B i := Finset.sum_nonneg fun i hi => div_nonneg (hX i hi) (hB i hi)
  have hT0 : 0 ≤ ∑ i ∈ S, τ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := cs_sum S ξ τ
  rw [hξsq] at hcs
  have hxs := Real.sq_sqrt hxx0
  have hTs := Real.sq_sqrt hT0
  calc ∑ i ∈ S, a i ^ 2 / B i ≤ ∑ i ∈ S, (ξ i + τ i) ^ 2 :=
        Finset.sum_le_sum fun i hi => a_form (hB i hi) (hX i hi) (hcirc i hi) hc0
          (ha0 i hi) (ha i hi)
    _ = ∑ i ∈ S, ξ i ^ 2 + 2 * ∑ i ∈ S, ξ i * τ i + ∑ i ∈ S, τ i ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        rw [hξsq]
        nlinarith [hcs, hxs, hTs]

theorem pure_cross_cells {ι : Type*} (S : Finset ι) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hc0le : c0 ≤ lambda3Alpha)
    (B p circ E X Y a b pf pg : ι → ℝ)
    (hB : ∀ i ∈ S, 0 ≤ B i) (hp : ∀ i ∈ S, 0 ≤ p i) (hcirc : ∀ i ∈ S, 0 ≤ circ i ∧ circ i ≤ p i)
    (hE : ∀ i ∈ S, 0 ≤ E i) (hX : ∀ i ∈ S, 0 ≤ X i) (hY : ∀ i ∈ S, 0 ≤ Y i)
    (hXY : ∀ i ∈ S, X i + Y i ≤ B i * E i)
    (ha0 : ∀ i ∈ S, 0 ≤ a i) (hb0 : ∀ i ∈ S, 0 ≤ b i)
    (ha : ∀ i ∈ S, a i ≤ Real.sqrt (X i) + c0 * B i * Real.sqrt (circ i))
    (hb : ∀ i ∈ S, b i ≤ Real.sqrt (Y i))
    (hpf : ∀ i ∈ S, 0 ≤ pf i) (hpg : ∀ i ∈ S, 0 ≤ pg i)
    (hen : ∑ i ∈ S, E i ≤ ∑ i ∈ S, Real.sqrt (p i) * b i) :
    ∑ i ∈ S, (Real.sqrt (pf i) * b i + Real.sqrt (pg i) * a i) ≤
      (141 / 100 : ℝ) * Real.sqrt (∑ i ∈ S, B i * p i) *
        Real.sqrt (∑ i ∈ S, B i * (pf i + pg i)) := by
  have hBz : ∀ i ∈ S, B i = 0 → X i = 0 ∧ Y i = 0 := by
    intro i hi h0
    have := hXY i hi
    rw [h0, zero_mul] at this
    exact ⟨le_antisymm (by linarith [hY i hi]) (hX i hi), le_antisymm (by linarith [hX i hi]) (hY i hi)⟩
  have hbz : ∀ i ∈ S, B i = 0 → b i = 0 := fun i hi h0 => by
    have := (hBz i hi h0).2
    have h := hb i hi
    rw [this, Real.sqrt_zero] at h
    exact le_antisymm h (hb0 i hi)
  have haz : ∀ i ∈ S, B i = 0 → a i = 0 := fun i hi h0 => by
    have := (hBz i hi h0).1
    have h := ha i hi
    rw [this, Real.sqrt_zero, h0] at h
    simp at h
    exact le_antisymm h (ha0 i hi)
  have hZ20 : 0 ≤ ∑ i ∈ S, B i * p i := Finset.sum_nonneg fun i hi => mul_nonneg (hB i hi) (hp i hi)
  have hyy0 : 0 ≤ ∑ i ∈ S, Y i / B i := Finset.sum_nonneg fun i hi => div_nonneg (hY i hi) (hB i hi)
  have hxx0 : 0 ≤ ∑ i ∈ S, X i / B i := Finset.sum_nonneg fun i hi => div_nonneg (hX i hi) (hB i hi)
  have hwbY : ∑ i ∈ S, b i ^ 2 / B i ≤ ∑ i ∈ S, Y i / B i := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact div_le_div_of_nonneg_right (by
      calc b i ^ 2 ≤ Real.sqrt (Y i) ^ 2 := pow_le_pow_left₀ (hb0 i hi) (hb i hi) 2
        _ = Y i := Real.sq_sqrt (hY i hi)) (hB i hi)
  have hxy : ∑ i ∈ S, X i / B i + ∑ i ∈ S, Y i / B i ≤ ∑ i ∈ S, E i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases h0 : B i = 0
    · obtain ⟨h1, h2⟩ := hBz i hi h0
      simp [h1, h2, hE i hi]
    · have hBp : 0 < B i := lt_of_le_of_ne (hB i hi) (Ne.symm h0)
      rw [← add_div, div_le_iff₀ hBp]
      linarith [hXY i hi]
  have hpair := pair_form_sum S B p b hB hp hb0 hbz
  set Z := Real.sqrt (∑ i ∈ S, B i * p i) with hZ
  set y := Real.sqrt (∑ i ∈ S, Y i / B i) with hy
  set x := Real.sqrt (∑ i ∈ S, X i / B i) with hx
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hZsq : Z ^ 2 = ∑ i ∈ S, B i * p i := Real.sq_sqrt hZ20
  have hysq : y ^ 2 = ∑ i ∈ S, Y i / B i := Real.sq_sqrt hyy0
  have hxsq : x ^ 2 = ∑ i ∈ S, X i / B i := Real.sq_sqrt hxx0
  have hwbs : Real.sqrt (∑ i ∈ S, b i ^ 2 / B i) ≤ y := Real.sqrt_le_sqrt hwbY
  have hen2 : x ^ 2 + y ^ 2 ≤ Z * y := by
    rw [hxsq, hysq]
    calc _ ≤ ∑ i ∈ S, E i := hxy
      _ ≤ _ := hen
      _ ≤ _ := hpair
      _ ≤ Z * y := mul_le_mul_of_nonneg_left hwbs hZ0
  set Tn := Real.sqrt (∑ i ∈ S, (c0 * Real.sqrt (B i * circ i)) ^ 2) with hTn
  have hTn0 : 0 ≤ Tn := Real.sqrt_nonneg _
  have hTnle : Tn ≤ c0 * Z := by
    have h1 : ∑ i ∈ S, (c0 * Real.sqrt (B i * circ i)) ^ 2 ≤ c0 ^ 2 * ∑ i ∈ S, B i * p i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (hB i hi) (hcirc i hi).1)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcirc i hi).2 (hB i hi)) (sq_nonneg _)
    calc Tn ≤ Real.sqrt (c0 ^ 2 * ∑ i ∈ S, B i * p i) := Real.sqrt_le_sqrt h1
      _ = c0 * Z := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc0]
  have hwaS : ∑ i ∈ S, a i ^ 2 / B i ≤ (x + Tn) ^ 2 :=
    first_output_sum S c0 hc0 B X circ a hB hX (fun i hi => (hcirc i hi).1) ha0 ha
  have hTtot := disk_total Z y x Tn c0 hZ0 hy0 hx0 hTn0 hc0 hc0le hen2 hTnle
  have hcross1 := pair_form_sum S B pf b hB hpf hb0 hbz
  have hcross2 := pair_form_sum S B pg a hB hpg ha0 haz
  have hsplit : ∑ i ∈ S, B i * (pf i + pg i) = ∑ i ∈ S, B i * pf i + ∑ i ∈ S, B i * pg i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have hF0 : 0 ≤ ∑ i ∈ S, B i * pf i := Finset.sum_nonneg fun i hi => mul_nonneg (hB i hi) (hpf i hi)
  have hG0 : 0 ≤ ∑ i ∈ S, B i * pg i := Finset.sum_nonneg fun i hi => mul_nonneg (hB i hi) (hpg i hi)
  have hWb0 : 0 ≤ ∑ i ∈ S, b i ^ 2 / B i := Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hB i hi)
  have hWa0 : 0 ≤ ∑ i ∈ S, a i ^ 2 / B i := Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hB i hi)
  have h2d := two_cs _ _ _ _ hF0 hG0 hWb0 hWa0
  have hWtot : ∑ i ∈ S, b i ^ 2 / B i + ∑ i ∈ S, a i ^ 2 / B i ≤ (141 / 100 : ℝ) ^ 2 * Z ^ 2 := by
    have := add_le_add hwbY hwaS
    rw [← hysq] at this
    linarith
  rw [hsplit]
  calc ∑ i ∈ S, (Real.sqrt (pf i) * b i + Real.sqrt (pg i) * a i)
      = ∑ i ∈ S, Real.sqrt (pf i) * b i + ∑ i ∈ S, Real.sqrt (pg i) * a i := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hcross1 hcross2
    _ ≤ _ := h2d
    _ ≤ Real.sqrt (∑ i ∈ S, B i * pf i + ∑ i ∈ S, B i * pg i) * Real.sqrt ((141 / 100 : ℝ) ^ 2 * Z ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hWtot) (Real.sqrt_nonneg _)
    _ = (141 / 100 : ℝ) * Z * Real.sqrt (∑ i ∈ S, B i * pf i + ∑ i ∈ S, B i * pg i) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num), Real.sqrt_sq hZ0]; ring

end

end ASDExplicitGamma.Scalar
