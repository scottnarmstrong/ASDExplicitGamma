module

public import ASDExplicitGamma.Native.GenericSourceRows

/-! The source's p=20 finite generic recurrence, kept separate from its
analytic transport hypotheses.  This module proves that each of its four
refinement passes preserves the degree split `a,e : degree one`, `f : degree
zero` recorded in the source recurrence. -/
@[expose] public section

namespace ASDExplicitGamma.Native

/-- The OLD order-128 inverse cap carried by the source recurrence. -/
noncomputable def nativeSourceB128 : ℝ := 3683 / 2500

/-- The projected coefficient in the p=20 source recurrence. -/
noncomputable def nativeSourceK : ℝ := 521 / 1000

/-- The generator coefficient in the p=20 source recurrence. -/
noncomputable def nativeSourceM : ℝ := 1975 / 1000

/-- The quadratic coefficient in the p=20 source recurrence. -/
noncomputable def nativeSourceQ : ℝ := 1565 / 1000

/-- The exact Holder interpolation exponent `20/(128-20)`. -/
noncomputable def nativeSourceEll : ℝ := 5 / 27

/-- The raw p=20 moment increment, with the source's inverse
cap and covariance coefficients. -/
noncomputable def nativeSourceRawMomentIncrement (h : ℕ) (e f : ℝ) : ℝ :=
  e * (((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128) +
    2 * nativeSourceK * nativeSourceB128 * f +
    (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f)

/-- The finite-Holder denominator cap `d`. -/
noncomputable def nativeSourceInterpolationD (x : ℝ) : ℝ :=
  min (2 * nativeSourceB128) (2 + x + Real.sqrt (2 * x))

/-- The two finite-Holder interpolation caps. -/
noncomputable def nativeSourceInterpolationU1 (x f : ℝ) : ℝ :=
  min f (4 + x ^ (1 - nativeSourceEll) * f ^ nativeSourceEll)

noncomputable def nativeSourceInterpolationU2 (x f : ℝ) : ℝ :=
  min f (4 + x ^ (1 - 2 * nativeSourceEll) * f ^ (2 * nativeSourceEll))

/-- The refined p=20 moment increment. -/
noncomputable def nativeSourceRefinedMomentIncrement (h : ℕ) (e f x : ℝ) : ℝ :=
  e * (((39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x) +
    2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x f +
    (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 *
      nativeSourceInterpolationU2 x f)

/-- The source's successive individual-cap minima.  Pass zero is the raw
moment bound; each later pass refines it using the previous individual cap. -/
noncomputable def nativeSourceGenericPassCap (h : ℕ) (a e f : ℝ) : ℕ → ℝ
  | 0 => nativeSourceRawMomentIncrement h e f
  | n + 1 => min (nativeSourceGenericPassCap h a e f n)
      (nativeSourceRefinedMomentIncrement h e f
        (7 / 2 * a + nativeSourceGenericPassCap h a e f n))

/-- The corresponding individual p=20 source cap after `n` refinements. -/
noncomputable def nativeSourceGenericIndividualCap (h : ℕ) (a e f : ℝ) (n : ℕ) : ℝ :=
  7 / 2 * a + nativeSourceGenericPassCap h a e f n

/-- The Holder minima are monotone under nonnegative source endpoint domination. -/
theorem native_source_interpolation_caps_monotone
    {theta x x0 f f0 : ℝ}
    (htheta1 : theta ≤ 1)
    (hx : 0 ≤ x) (hx0 : 0 ≤ x0) (hscale : x ≤ theta * x0)
    (hf : 0 ≤ f) (hfcap : f ≤ f0) :
    nativeSourceInterpolationD x ≤ nativeSourceInterpolationD x0 ∧
    nativeSourceInterpolationU1 x f ≤ nativeSourceInterpolationU1 x0 f0 ∧
    nativeSourceInterpolationU2 x f ≤ nativeSourceInterpolationU2 x0 f0 := by
  have hxx0 : x ≤ x0 := by
    calc
      x ≤ theta * x0 := hscale
      _ ≤ 1 * x0 := mul_le_mul_of_nonneg_right htheta1 hx0
      _ = x0 := one_mul _
  have h2x : 2 * x ≤ 2 * x0 := mul_le_mul_of_nonneg_left hxx0 (by norm_num)
  have hsqrt : Real.sqrt (2 * x) ≤ Real.sqrt (2 * x0) :=
    Real.sqrt_le_sqrt h2x
  have hd : nativeSourceInterpolationD x ≤ nativeSourceInterpolationD x0 := by
    unfold nativeSourceInterpolationD
    apply min_le_min le_rfl
    have hsum : 2 + x ≤ 2 + x0 := add_le_add (le_of_eq rfl) hxx0
    exact add_le_add hsum hsqrt
  have hx1 : x ^ (1 - nativeSourceEll) ≤ x0 ^ (1 - nativeSourceEll) :=
    Real.rpow_le_rpow hx hxx0 (by norm_num [nativeSourceEll])
  have hf1 : f ^ nativeSourceEll ≤ f0 ^ nativeSourceEll :=
    Real.rpow_le_rpow hf hfcap (by norm_num [nativeSourceEll])
  have hprod1 : x ^ (1 - nativeSourceEll) * f ^ nativeSourceEll ≤
      x0 ^ (1 - nativeSourceEll) * f0 ^ nativeSourceEll :=
    mul_le_mul hx1 hf1 (Real.rpow_nonneg hf _) (Real.rpow_nonneg hx0 _)
  have hu1 : nativeSourceInterpolationU1 x f ≤ nativeSourceInterpolationU1 x0 f0 := by
    unfold nativeSourceInterpolationU1
    apply min_le_min hfcap
    exact add_le_add (le_of_eq rfl) hprod1
  have hx2 : x ^ (1 - 2 * nativeSourceEll) ≤ x0 ^ (1 - 2 * nativeSourceEll) :=
    Real.rpow_le_rpow hx hxx0 (by norm_num [nativeSourceEll])
  have hf2 : f ^ (2 * nativeSourceEll) ≤ f0 ^ (2 * nativeSourceEll) :=
    Real.rpow_le_rpow hf hfcap (by norm_num [nativeSourceEll])
  have hprod2 : x ^ (1 - 2 * nativeSourceEll) * f ^ (2 * nativeSourceEll) ≤
      x0 ^ (1 - 2 * nativeSourceEll) * f0 ^ (2 * nativeSourceEll) :=
    mul_le_mul hx2 hf2 (Real.rpow_nonneg hf _) (Real.rpow_nonneg hx0 _)
  have hu2 : nativeSourceInterpolationU2 x f ≤ nativeSourceInterpolationU2 x0 f0 := by
    unfold nativeSourceInterpolationU2
    apply min_le_min hfcap
    exact add_le_add (le_of_eq rfl) hprod2
  exact ⟨hd, hu1, hu2⟩

private theorem source_raw_increment_degree
    {theta e e0 f f0 : ℝ} (h : ℕ)
    (htheta : 0 ≤ theta) (he0 : 0 ≤ e0)
    (hecap : e ≤ theta * e0) (hf : 0 ≤ f)
    (hfcap : f ≤ f0) :
    nativeSourceRawMomentIncrement h e f ≤
      theta * nativeSourceRawMomentIncrement h e0 f0 := by
  have hconst : 0 ≤ (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 := by
    apply mul_nonneg
    · exact add_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (by norm_num [nativeSourceK])
    · norm_num [nativeSourceB128]
  have hcoef : 0 ≤ 2 * nativeSourceK * nativeSourceB128 +
      (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 := by
    norm_num [nativeSourceK, nativeSourceB128, nativeSourceM, nativeSourceQ]
  have hbracket :
      (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          (2 * nativeSourceK * nativeSourceB128 + (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2) * f ≤
        (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          (2 * nativeSourceK * nativeSourceB128 + (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2) * f0 :=
    add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_left hfcap hcoef)
  have hbracket0 : 0 ≤
      (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
        (2 * nativeSourceK * nativeSourceB128 + (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2) * f :=
    add_nonneg hconst (mul_nonneg hcoef hf)
  have hscale : 0 ≤ theta * e0 := mul_nonneg htheta he0
  unfold nativeSourceRawMomentIncrement
  calc
    _ = e * ((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          (2 * nativeSourceK * nativeSourceB128 +
            (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2) * f) := by ring
    _ ≤ (theta * e0) * ((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          (2 * nativeSourceK * nativeSourceB128 + (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2) * f) :=
      mul_le_mul_of_nonneg_right hecap hbracket0
    _ ≤ (theta * e0) * ((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          (2 * nativeSourceK * nativeSourceB128 + (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2) * f0) :=
      mul_le_mul_of_nonneg_left hbracket hscale
    _ = theta * (e0 * (((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128) +
          2 * nativeSourceK * nativeSourceB128 * f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f0)) := by ring

private theorem source_refined_increment_degree
    {theta e e0 f f0 x x0 : ℝ} (h : ℕ)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (he0 : 0 ≤ e0) (hecap : e ≤ theta * e0)
    (hf : 0 ≤ f) (hfcap : f ≤ f0)
    (hx : 0 ≤ x) (hx0 : 0 ≤ x0) (hxcap : x ≤ theta * x0) :
    nativeSourceRefinedMomentIncrement h e f x ≤
      theta * nativeSourceRefinedMomentIncrement h e0 f0 x0 := by
  have hinterp := native_source_interpolation_caps_monotone htheta1
    hx hx0 hxcap hf hfcap
  have hd0 : 0 ≤ nativeSourceInterpolationD x := by
    unfold nativeSourceInterpolationD
    apply le_min
    · norm_num [nativeSourceB128]
    · exact add_nonneg (add_nonneg (by norm_num) hx) (Real.sqrt_nonneg _)
  have hu10 : 0 ≤ nativeSourceInterpolationU1 x f := by
    unfold nativeSourceInterpolationU1
    apply le_min hf
    exact add_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hf _))
  have hu20 : 0 ≤ nativeSourceInterpolationU2 x f := by
    unfold nativeSourceInterpolationU2
    apply le_min hf
    exact add_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hf _))
  have hcd : 0 ≤ (39 * (h : ℝ) + 38 * nativeSourceK) := by
    exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by norm_num [nativeSourceK])
  have hcu1 : 0 ≤ 2 * nativeSourceK * nativeSourceB128 := by
    norm_num [nativeSourceK, nativeSourceB128]
  have hcu2 : 0 ≤ (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 := by
    norm_num [nativeSourceM, nativeSourceQ, nativeSourceB128]
  have hbracket :
      (39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x +
          2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x f +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * nativeSourceInterpolationU2 x f ≤
        (39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x0 +
          2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x0 f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * nativeSourceInterpolationU2 x0 f0 := by
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hinterp.1 hcd)
      (mul_le_mul_of_nonneg_left hinterp.2.1 hcu1))
      (mul_le_mul_of_nonneg_left hinterp.2.2 hcu2)
  have hbracket0 : 0 ≤
      (39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x +
          2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x f +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * nativeSourceInterpolationU2 x f := by
    exact add_nonneg (add_nonneg (mul_nonneg hcd hd0) (mul_nonneg hcu1 hu10))
      (mul_nonneg hcu2 hu20)
  have hscale : 0 ≤ theta * e0 := mul_nonneg htheta he0
  unfold nativeSourceRefinedMomentIncrement
  calc
    _ ≤ (theta * e0) * ((39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x +
          2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x f +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * nativeSourceInterpolationU2 x f) :=
      mul_le_mul_of_nonneg_right hecap hbracket0
    _ ≤ (theta * e0) * ((39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x0 +
          2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x0 f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * nativeSourceInterpolationU2 x0 f0) :=
      mul_le_mul_of_nonneg_left hbracket hscale
    _ = theta * (e0 * ((39 * (h : ℝ) + 38 * nativeSourceK) * nativeSourceInterpolationD x0 +
          2 * nativeSourceK * nativeSourceB128 * nativeSourceInterpolationU1 x0 f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * nativeSourceInterpolationU2 x0 f0)) := by ring

private theorem native_source_generic_pass_nonneg
    (h : ℕ) {a e f : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f) :
    ∀ n, 0 ≤ nativeSourceGenericPassCap h a e f n := by
  intro n
  induction n with
  | zero =>
      unfold nativeSourceGenericPassCap nativeSourceRawMomentIncrement
      have hA : 0 ≤ (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 := by
        apply mul_nonneg
        · exact add_nonneg
            (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (by norm_num [nativeSourceK])
        · norm_num [nativeSourceB128]
      have hB : 0 ≤ 2 * nativeSourceK * nativeSourceB128 := by
        norm_num [nativeSourceK, nativeSourceB128]
      have hC : 0 ≤ (nativeSourceM + 38 * nativeSourceQ) *
          nativeSourceB128 ^ 2 := by
        norm_num [nativeSourceM, nativeSourceQ, nativeSourceB128]
      exact mul_nonneg he (add_nonneg (add_nonneg hA (mul_nonneg hB hf))
        (mul_nonneg hC hf))
  | succ n ih =>
      unfold nativeSourceGenericPassCap
      have hx : 0 ≤ 7 / 2 * a + nativeSourceGenericPassCap h a e f n := by
        positivity
      have hr : 0 ≤ nativeSourceRefinedMomentIncrement h e f
          (7 / 2 * a + nativeSourceGenericPassCap h a e f n) := by
        have hd : 0 ≤ nativeSourceInterpolationD
            (7 / 2 * a + nativeSourceGenericPassCap h a e f n) := by
          apply le_min
          · norm_num [nativeSourceB128]
          · exact add_nonneg
              (add_nonneg (by norm_num) (by positivity)) (Real.sqrt_nonneg _)
        have hu1 : 0 ≤ nativeSourceInterpolationU1
            (7 / 2 * a + nativeSourceGenericPassCap h a e f n) f := by
          apply le_min hf
          exact add_nonneg (by norm_num)
            (mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg hf _))
        have hu2 : 0 ≤ nativeSourceInterpolationU2
            (7 / 2 * a + nativeSourceGenericPassCap h a e f n) f := by
          apply le_min hf
          exact add_nonneg (by norm_num)
            (mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg hf _))
        have hc1 : 0 ≤ (39 * (h : ℝ) + 38 * nativeSourceK) := by
          exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (by norm_num [nativeSourceK])
        have hc2 : 0 ≤ 2 * nativeSourceK * nativeSourceB128 := by
          norm_num [nativeSourceK, nativeSourceB128]
        have hc3 : 0 ≤ (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 := by
          norm_num [nativeSourceM, nativeSourceQ, nativeSourceB128]
        exact mul_nonneg he (add_nonneg
          (add_nonneg (mul_nonneg hc1 hd) (mul_nonneg hc2 hu1))
          (mul_nonneg hc3 hu2))
      exact le_min ih hr

/-- Nonnegativity of the corresponding individual source cap. -/
theorem native_source_generic_individual_nonneg
    (h : ℕ) (a e f : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f)
    (n : ℕ) :
    0 ≤ nativeSourceGenericIndividualCap h a e f n := by
  unfold nativeSourceGenericIndividualCap
  exact add_nonneg (mul_nonneg (by norm_num) ha)
    (native_source_generic_pass_nonneg h ha he hf n)

/-- Each source refinement preserves degree one for the moment increment and
degree zero for the p=128 response cap. -/
theorem native_source_generic_pass_degree_split
    (h : ℕ) {theta a a0 e e0 f f0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (ha : 0 ≤ a) (ha0 : 0 ≤ a0) (hacap : a ≤ theta * a0)
    (he : 0 ≤ e) (he0 : 0 ≤ e0) (hecap : e ≤ theta * e0)
    (hf : 0 ≤ f) (hf0 : 0 ≤ f0) (hfcap : f ≤ f0) :
    ∀ n, nativeSourceGenericPassCap h a e f n ≤
      theta * nativeSourceGenericPassCap h a0 e0 f0 n := by
  intro n
  induction n with
  | zero =>
      exact source_raw_increment_degree h htheta he0 hecap hf hfcap
  | succ n ih =>
      have hx : 0 ≤ 7 / 2 * a + nativeSourceGenericPassCap h a e f n := by
        have hcur := native_source_generic_pass_nonneg h ha he hf n
        positivity
      have hx0 : 0 ≤ 7 / 2 * a0 + nativeSourceGenericPassCap h a0 e0 f0 n := by
        have hcur0 := native_source_generic_pass_nonneg h ha0 he0 hf0 n
        positivity
      have hxcap : 7 / 2 * a + nativeSourceGenericPassCap h a e f n ≤
          theta * (7 / 2 * a0 + nativeSourceGenericPassCap h a0 e0 f0 n) := by
        calc
          _ ≤ 7 / 2 * (theta * a0) +
              theta * nativeSourceGenericPassCap h a0 e0 f0 n :=
            add_le_add (mul_le_mul_of_nonneg_left hacap (by norm_num)) ih
          _ = _ := by ring
      have href := source_refined_increment_degree h htheta htheta1 he0 hecap
        hf hfcap hx hx0 hxcap
      have hmin :
          min (nativeSourceGenericPassCap h a e f n)
            (nativeSourceRefinedMomentIncrement h e f
              (7 / 2 * a + nativeSourceGenericPassCap h a e f n)) ≤
          min (theta * nativeSourceGenericPassCap h a0 e0 f0 n)
            (theta * nativeSourceRefinedMomentIncrement h e0 f0
              (7 / 2 * a0 + nativeSourceGenericPassCap h a0 e0 f0 n)) :=
        min_le_min ih href
      have hminScale :
          min (theta * nativeSourceGenericPassCap h a0 e0 f0 n)
              (theta * nativeSourceRefinedMomentIncrement h e0 f0
                (7 / 2 * a0 + nativeSourceGenericPassCap h a0 e0 f0 n)) =
            theta * min (nativeSourceGenericPassCap h a0 e0 f0 n)
              (nativeSourceRefinedMomentIncrement h e0 f0
                (7 / 2 * a0 + nativeSourceGenericPassCap h a0 e0 f0 n)) := by
        rw [← mul_min_of_nonneg _ _ htheta]
      simpa only [nativeSourceGenericPassCap] using hmin.trans_eq hminScale

/-- The individual p=20 cap itself remains of degree one after any finite
number of the source's refinement passes. -/
theorem native_source_generic_individual_degree_split
    (h : ℕ) {theta a a0 e e0 f f0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (ha : 0 ≤ a) (ha0 : 0 ≤ a0) (hacap : a ≤ theta * a0)
    (he : 0 ≤ e) (he0 : 0 ≤ e0) (hecap : e ≤ theta * e0)
    (hf : 0 ≤ f) (hf0 : 0 ≤ f0) (hfcap : f ≤ f0)
    (n : ℕ) :
    nativeSourceGenericIndividualCap h a e f n ≤
      theta * nativeSourceGenericIndividualCap h a0 e0 f0 n := by
  unfold nativeSourceGenericIndividualCap
  have hpass := native_source_generic_pass_degree_split h htheta htheta1
    ha ha0 hacap he he0 hecap hf hf0 hfcap n
  calc
    _ ≤ 7 / 2 * (theta * a0) +
        theta * nativeSourceGenericPassCap h a0 e0 f0 n :=
      add_le_add (mul_le_mul_of_nonneg_left hacap (by norm_num)) hpass
    _ = _ := by ring

end ASDExplicitGamma.Native
