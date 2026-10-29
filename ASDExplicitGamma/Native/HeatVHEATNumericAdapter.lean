module

public import ASDExplicitGamma.Native.HeatRemainderControl
public import ASDExplicitGamma.Native.HeatVHEATBounds

/-! A first-row bridge from the stable real VHEAT error to the rounded
numeric forcing row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- Below the top Hölder degree, the rational rare-row producer is an
outward-rounded upper bound for the stable real `J` interface. -/
theorem nativeHeatRareJ_ge_vheatJ_of_lt
    (frames : NativeHeatFrameInputs) (j l : ℕ) (hl : l < 20)
    (hx : 0 ≤ frames.x) :
    nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 j l ≤
      (nativeHeatRareJ frames j l : ℚ) := by
  have heps : 0 ≤ nativeHeatEps := by decide +kernel
  have hq : 0 ≤ nativeHeatEps ^ j * frames.x ^ l :=
    mul_nonneg (pow_nonneg heps _) (pow_nonneg hx _)
  have hup := nativeUp_ge (nativeHeatEps ^ j * frames.x ^ l)
  have hround :
      nativeHeatEps ^ j * frames.x ^ l ≤
        nativeHeatRareJ frames j l := by
    simpa [nativeHeatRareJ, show l ≠ 20 by omega] using hup
  rw [nativeHeatVHEATJ_of_lt _ _ _ _ _ _ hl]
  exact_mod_cast hround

private theorem nativePowUp_five27_eq (q : ℚ) :
    nativePowUp q (5 / 27 : ℚ) = nativeRootUp (q ^ 5) 27 := by
  have hnum : (5 / 27 : ℚ).num = 5 := by decide +kernel
  have hden : (5 / 27 : ℚ).den = 27 := by decide +kernel
  simp [nativePowUp, hnum, hden]

private theorem nativePowUp_ten27_eq (q : ℚ) :
    nativePowUp q (10 / 27 : ℚ) = nativeRootUp (q ^ 10) 27 := by
  have hnum : (10 / 27 : ℚ).num = 10 := by decide +kernel
  have hden : (10 / 27 : ℚ).den = 27 := by decide +kernel
  simp [nativePowUp, hnum, hden]

/-- The checked 27th-root certificate validates the rational producer for the
first top-degree generalized-Hölder exponent. -/
private theorem nativePowUp_ge_rpow_five27 (q : ℚ) (hq : 0 ≤ q)
    (hvalid : nativeRootValid (q ^ 5) 27 = true) :
    Real.rpow (q : ℝ) (((5 : ℕ) : ℝ) / 27) ≤
      (nativePowUp q (5 / 27 : ℚ) : ℝ) := by
  rw [nativePowUp_five27_eq]
  have hroot := nativeRoot_sound hvalid
  have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hpow : ((q ^ 5 : ℚ) : ℝ) = (q : ℝ) ^ 5 := by norm_num
  have hexp : ((5 : ℕ) : ℝ) / 27 = ((5 : ℕ) : ℝ) * ((27 : ℝ)⁻¹) := by
    norm_num
  have heq : Real.rpow (q : ℝ) (((5 : ℕ) : ℝ) / 27) =
      ((q ^ 5 : ℚ) : ℝ) ^ ((27 : ℝ)⁻¹) := by
    calc
      _ = Real.rpow (q : ℝ) (((5 : ℕ) : ℝ) * ((27 : ℝ)⁻¹)) := by rw [hexp]
      _ = ((q : ℝ) ^ 5) ^ ((27 : ℝ)⁻¹) :=
        Real.rpow_natCast_mul hqR 5 ((27 : ℝ)⁻¹)
      _ = ((q ^ 5 : ℚ) : ℝ) ^ ((27 : ℝ)⁻¹) := by rw [hpow]
  rw [heq]
  exact hroot

/-- The checked 27th-root certificate validates the rational producer for the
second top-degree generalized-Hölder exponent. -/
private theorem nativePowUp_ge_rpow_ten27 (q : ℚ) (hq : 0 ≤ q)
    (hvalid : nativeRootValid (q ^ 10) 27 = true) :
    Real.rpow (q : ℝ) (((10 : ℕ) : ℝ) / 27) ≤
      (nativePowUp q (10 / 27 : ℚ) : ℝ) := by
  rw [nativePowUp_ten27_eq]
  have hroot := nativeRoot_sound hvalid
  have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hpow : ((q ^ 10 : ℚ) : ℝ) = (q : ℝ) ^ 10 := by norm_num
  have hexp : ((10 : ℕ) : ℝ) / 27 = ((10 : ℕ) : ℝ) * ((27 : ℝ)⁻¹) := by
    norm_num
  have heq : Real.rpow (q : ℝ) (((10 : ℕ) : ℝ) / 27) =
      ((q ^ 10 : ℚ) : ℝ) ^ ((27 : ℝ)⁻¹) := by
    calc
      _ = Real.rpow (q : ℝ) (((10 : ℕ) : ℝ) * ((27 : ℝ)⁻¹)) := by rw [hexp]
      _ = ((q : ℝ) ^ 10) ^ ((27 : ℝ)⁻¹) :=
        Real.rpow_natCast_mul hqR 10 ((27 : ℝ)⁻¹)
      _ = ((q ^ 10 : ℚ) : ℝ) ^ ((27 : ℝ)⁻¹) := by rw [hpow]
  rw [heq]
  exact hroot

/-- At the top Hölder degree, the outward-rounded rare row dominates the
stable first-order `J` term whenever its checked root certificate is supplied. -/
theorem nativeHeatRareJ_ge_vheatJ_top_one
    (frames : NativeHeatFrameInputs) (hx : 0 < frames.x) (hraw : 0 ≤ frames.raw)
    (hvalid : nativeRootValid ((frames.raw / frames.x) ^ 5) 27 = true) :
    nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 1 20 ≤ (nativeHeatRareJ frames 1 20 : ℚ) := by
  let q : ℚ := frames.raw / frames.x
  have hq : 0 ≤ q := by dsimp [q]; exact div_nonneg hraw hx.le
  have hqR : (q : ℝ) = (frames.raw : ℝ) / (frames.x : ℝ) := by
    dsimp [q]
    norm_cast
  have hexp : ((1 * 20 : ℕ) : ℝ) / ((128 - 20 : ℕ) : ℝ) =
      ((5 : ℕ) : ℝ) / 27 := by norm_num
  have hpow := nativePowUp_ge_rpow_five27 q hq hvalid
  have hcoef : 0 ≤ (nativeHeatEps : ℝ) ^ 1 * (frames.x : ℝ) ^ 20 := by
    have heps : 0 ≤ nativeHeatEps := by decide +kernel
    have hepsR : 0 ≤ (nativeHeatEps : ℝ) := by exact_mod_cast heps
    have hxR : 0 ≤ (frames.x : ℝ) := by exact_mod_cast hx.le
    positivity
  have hmul :
      (nativeHeatEps : ℝ) ^ 1 * (frames.x : ℝ) ^ 20 *
          Real.rpow (q : ℝ) (((5 : ℕ) : ℝ) / 27) ≤
        ((nativeHeatEps ^ 1 * frames.x ^ 20 * nativePowUp q (5 / 27 : ℚ) : ℚ) : ℝ) := by
    calc
      _ ≤ (nativeHeatEps : ℝ) ^ 1 * (frames.x : ℝ) ^ 20 *
          (nativePowUp q (5 / 27 : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hpow hcoef
      _ = _ := by push_cast; ring
  have hupR :
      ((nativeHeatEps ^ 1 * frames.x ^ 20 * nativePowUp q (5 / 27 : ℚ) : ℚ) : ℝ) ≤
        ((nativeUp (nativeHeatEps ^ 1 * frames.x ^ 20 *
          nativePowUp q (5 / 27 : ℚ)) : ℚ) : ℝ) := by
    exact_mod_cast nativeUp_ge _
  have hrare : nativeHeatRareJ frames 1 20 =
      nativeUp (nativeHeatEps ^ 1 * frames.x ^ 20 * nativePowUp q (5 / 27 : ℚ)) := by
    dsimp [q]
    have hqpow : nativePowUp (frames.raw / frames.x) (20 / 108 : ℚ) =
        nativePowUp (frames.raw / frames.x) (5 / 27 : ℚ) := by
      congr 1
      norm_num
    simp [nativeHeatRareJ, hqpow]
  rw [nativeHeatVHEATJ_top, hexp, ← hqR]
  exact hmul.trans (hupR.trans (by rw [hrare]))

/-- The corresponding checked top-degree rare row for the quadratic `J` term. -/
theorem nativeHeatRareJ_ge_vheatJ_top_two
    (frames : NativeHeatFrameInputs) (hx : 0 < frames.x) (hraw : 0 ≤ frames.raw)
    (hvalid : nativeRootValid ((frames.raw / frames.x) ^ 10) 27 = true) :
    nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 2 20 ≤ (nativeHeatRareJ frames 2 20 : ℚ) := by
  let q : ℚ := frames.raw / frames.x
  have hq : 0 ≤ q := by dsimp [q]; exact div_nonneg hraw hx.le
  have hqR : (q : ℝ) = (frames.raw : ℝ) / (frames.x : ℝ) := by
    dsimp [q]
    norm_cast
  have hexp : ((2 * 20 : ℕ) : ℝ) / ((128 - 20 : ℕ) : ℝ) =
      ((10 : ℕ) : ℝ) / 27 := by norm_num
  have hpow := nativePowUp_ge_rpow_ten27 q hq hvalid
  have hcoef : 0 ≤ (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ 20 := by
    have heps : 0 ≤ nativeHeatEps := by decide +kernel
    have hepsR : 0 ≤ (nativeHeatEps : ℝ) := by exact_mod_cast heps
    have hxR : 0 ≤ (frames.x : ℝ) := by exact_mod_cast hx.le
    positivity
  have hmul :
      (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ 20 *
          Real.rpow (q : ℝ) (((10 : ℕ) : ℝ) / 27) ≤
        ((nativeHeatEps ^ 2 * frames.x ^ 20 * nativePowUp q (10 / 27 : ℚ) : ℚ) : ℝ) := by
    calc
      _ ≤ (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ 20 *
          (nativePowUp q (10 / 27 : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hpow hcoef
      _ = _ := by push_cast; ring
  have hupR :
      ((nativeHeatEps ^ 2 * frames.x ^ 20 * nativePowUp q (10 / 27 : ℚ) : ℚ) : ℝ) ≤
        ((nativeUp (nativeHeatEps ^ 2 * frames.x ^ 20 *
          nativePowUp q (10 / 27 : ℚ)) : ℚ) : ℝ) := by
    exact_mod_cast nativeUp_ge _
  have hrare : nativeHeatRareJ frames 2 20 =
      nativeUp (nativeHeatEps ^ 2 * frames.x ^ 20 * nativePowUp q (10 / 27 : ℚ)) := by
    dsimp [q]
    have hqpow : nativePowUp (frames.raw / frames.x) (40 / 108 : ℚ) =
        nativePowUp (frames.raw / frames.x) (10 / 27 : ℚ) := by
      congr 1
      norm_num
    simp [nativeHeatRareJ, hqpow]
  rw [nativeHeatVHEATJ_top, hexp, ← hqR]
  exact hmul.trans (hupR.trans (by rw [hrare]))

/-- The explicit numeric remainder used downstream dominates the stable degree
one `E_k` row. The quadratic Young bracket is absent in this degree, and the
four lower-degree `J` terms are converted without changing the stable API. -/
theorem nativeHeatVHEATErrorEk_one_le_fixedAt
    (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (hold : 0 ≤ old.e) (hx : 0 ≤ frames.x) :
    nativeHeatVHEATErrorEk 1 20 (old.e : ℝ)
        (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
        (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
        0 (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
      (nativeHeatFixedAt old frames 1 : ℚ) := by
  have hJ10 := nativeHeatRareJ_ge_vheatJ_of_lt frames 1 0 (by norm_num) hx
  have hJ11 := nativeHeatRareJ_ge_vheatJ_of_lt frames 1 1 (by norm_num) hx
  have hJ20 := nativeHeatRareJ_ge_vheatJ_of_lt frames 2 0 (by norm_num) hx
  have hJ21 := nativeHeatRareJ_ge_vheatJ_of_lt frames 2 1 (by norm_num) hx
  have hK : 0 ≤ (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  have hM : 0 ≤ (nativeHeatM : ℝ) := by norm_num [nativeHeatM]
  have hb : 0 ≤ (nativeHeatB : ℝ) := by
    have hq : 0 ≤ nativeHeatB := by decide +kernel
    exact_mod_cast hq
  have hbase :
      nativeHeatVHEATErrorEk 1 20 (old.e : ℝ)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
          0 (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
        (nativeHeatFixedAnalyticRemainder old frames 1 : ℚ) := by
    unfold nativeHeatFixedAnalyticRemainder
    simp only [show ¬ 1 ≥ 2 by omega, ↓reduceIte, Nat.cast_one]
    have hcoef : 0 ≤ 2 * (nativeHeatK : ℝ) +
        2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ) := by positivity
    have hcoefM : 0 ≤ (nativeHeatM : ℝ) := hM
    have hE : 0 ≤ (old.e : ℝ) := by exact_mod_cast hold
    have hinner :
        (2 * (nativeHeatK : ℝ) +
            2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ)) *
            (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 1 0 +
              nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 1 1) +
          (nativeHeatM : ℝ) *
            (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 2 0 +
              nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 2 1) ≤
        (2 * (nativeHeatK : ℝ) +
            2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ)) *
            (4 * (nativeHeatRareJ frames 1 0 : ℚ) +
              (nativeHeatRareJ frames 1 1 : ℚ)) +
          (nativeHeatM : ℝ) *
            (4 * (nativeHeatRareJ frames 2 0 : ℚ) +
              (nativeHeatRareJ frames 2 1 : ℚ)) := by
      gcongr
    calc
      _ = (old.e : ℝ) *
          ((2 * (nativeHeatK : ℝ) +
              2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ)) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 0 +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 1) +
            (nativeHeatM : ℝ) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 2 0 +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 2 1)) := by
                rw [nativeHeatVHEATErrorEk_one_eq 20 (by norm_num)]
                simp [nativeHeatVHEATJ]
      _ ≤ (old.e : ℝ) *
          ((2 * (nativeHeatK : ℝ) +
              2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ)) *
              (4 * (nativeHeatRareJ frames 1 0 : ℚ) +
                (nativeHeatRareJ frames 1 1 : ℚ)) +
            (nativeHeatM : ℝ) *
              (4 * (nativeHeatRareJ frames 2 0 : ℚ) +
                (nativeHeatRareJ frames 2 1 : ℚ))) :=
          mul_le_mul_of_nonneg_left hinner hE
      _ = (1 * old.e *
          ((2 * nativeHeatK + 2 * nativeHeatB * nativeHeatM) *
              (4 * nativeHeatRareJ frames 1 0 + nativeHeatRareJ frames 1 1) +
            nativeHeatM *
              (4 * nativeHeatRareJ frames 2 0 + nativeHeatRareJ frames 2 1)) : ℚ) := by
          push_cast
          ring
  have hround :
      (nativeHeatFixedAnalyticRemainder old frames 1 : ℚ) ≤
        nativeHeatFixedAt old frames 1 := by
    rw [nativeHeatFixedAt_eq_explicit_remainder]
    exact nativeUp_ge _
  have hroundR :
      ((nativeHeatFixedAnalyticRemainder old frames 1 : ℚ) : ℝ) ≤
        ((nativeHeatFixedAt old frames 1 : ℚ) : ℝ) := by exact_mod_cast hround
  exact hbase.trans hroundR

/-- In every non-top degree at least two, the stable VHEAT error is bounded by
the corresponding rounded forcing row once the supplied fixed vector covers
the analytic fixed remainder. The explicit quadratic OLD bracket is retained
inside the forcing row. -/
theorem nativeHeatVHEATErrorEk_le_forcingAt_of_lt
    (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed : List ℚ) (k : ℕ) (hk2 : 2 ≤ k) (hkp : k < 20)
    (hold : 0 ≤ old.e) (hx : 0 ≤ frames.x)
    (hfixed : nativeHeatFixedAnalyticRemainder old frames k ≤
      fixed.getD (k - 1) 0) :
    nativeHeatVHEATErrorEk k 20 (old.e : ℝ)
        (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
        (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
        (frames.y : ℝ) (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
      (nativeHeatForcingAt old frames fixed frames.y k : ℚ) := by
  have hJ1lo := nativeHeatRareJ_ge_vheatJ_of_lt frames 1 (k - 1) (by omega) hx
  have hJ1hi := nativeHeatRareJ_ge_vheatJ_of_lt frames 1 k (by omega) hx
  have hJ2lo := nativeHeatRareJ_ge_vheatJ_of_lt frames 2 (k - 1) (by omega) hx
  have hJ2hi := nativeHeatRareJ_ge_vheatJ_of_lt frames 2 k (by omega) hx
  have hJ1loR : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 1 (k - 1) ≤
      (nativeHeatRareJ frames 1 (k - 1) : ℚ) := by exact_mod_cast hJ1lo
  have hJ1hiR : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 1 k ≤ (nativeHeatRareJ frames 1 k : ℚ) := by
    exact_mod_cast hJ1hi
  have hJ2loR : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 2 (k - 1) ≤
      (nativeHeatRareJ frames 2 (k - 1) : ℚ) := by exact_mod_cast hJ2lo
  have hJ2hiR : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 2 k ≤ (nativeHeatRareJ frames 2 k : ℚ) := by
    exact_mod_cast hJ2hi
  have hJ1loPow : (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) ≤
      (nativeHeatRareJ frames 1 (k - 1) : ℚ) := by
    rw [nativeHeatVHEATJ_of_lt (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 1 (k - 1) (by omega)] at hJ1loR
    simpa only [pow_one] using hJ1loR
  have hJ1hiPow : (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k ≤
      (nativeHeatRareJ frames 1 k : ℚ) := by
    rw [nativeHeatVHEATJ_of_lt (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 1 k hkp] at hJ1hiR
    simpa only [pow_one] using hJ1hiR
  have hJ2loPow : (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) ≤
      (nativeHeatRareJ frames 2 (k - 1) : ℚ) := by
    rw [nativeHeatVHEATJ_of_lt (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 2 (k - 1) (by omega)] at hJ2loR
    exact hJ2loR
  have hJ2hiPow : (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k ≤
      (nativeHeatRareJ frames 2 k : ℚ) := by
    rw [nativeHeatVHEATJ_of_lt (nativeHeatEps : ℝ) (frames.x : ℝ)
      (frames.raw : ℝ) 20 2 k hkp] at hJ2hiR
    exact hJ2hiR
  have he : 0 ≤ (old.e : ℝ) := by exact_mod_cast hold
  have hK : 0 ≤ (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  have hM : 0 ≤ (nativeHeatM : ℝ) := by norm_num [nativeHeatM]
  have hb : 0 ≤ (nativeHeatB : ℝ) := by
    have hq : 0 ≤ nativeHeatB := by decide +kernel
    exact_mod_cast hq
  let c : ℝ := 2 * (k : ℝ) * ((k : ℝ) - 1) * (old.e : ℝ) *
    (nativeHeatSB : ℝ) * (1 + (nativeHeatTheta : ℝ)⁻¹)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hk : 0 ≤ (k : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ k by omega))
    have hsb : 0 ≤ (nativeHeatSB : ℝ) := by norm_num [nativeHeatSB]
    have htheta : 0 < (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
    positivity
  have hbase :
      (k : ℝ) * (old.e : ℝ) *
          ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
              (nativeHeatM : ℝ)) *
              (4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
                (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k) +
            (nativeHeatM : ℝ) *
              (4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
                (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k)) ≤
        (k : ℝ) * (old.e : ℝ) *
          ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
              (nativeHeatM : ℝ)) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
            (nativeHeatM : ℝ) *
              (4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 2 k : ℚ))) := by
    have hcoef : 0 ≤ 2 * (nativeHeatK : ℝ) +
        2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ) := by positivity
    have hscale : 0 ≤ (k : ℝ) * (old.e : ℝ) := by positivity
    have hrow1 :
        4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
            (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k ≤
          4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 1 k : ℚ) := by
      calc
        _ = 4 * ((nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1)) +
            (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k := by ring
        _ ≤ 4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 1 k : ℚ) :=
          add_le_add (mul_le_mul_of_nonneg_left hJ1loPow (by norm_num)) hJ1hiPow
    have hrow2 :
        4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
            (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k ≤
          4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 2 k : ℚ) := by
      calc
        _ = 4 * ((nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1)) +
            (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k := by ring
        _ ≤ 4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 2 k : ℚ) :=
          add_le_add (mul_le_mul_of_nonneg_left hJ2loPow (by norm_num)) hJ2hiPow
    have hinner := add_le_add
      (mul_le_mul_of_nonneg_left hrow1 hcoef)
      (mul_le_mul_of_nonneg_left hrow2 hM)
    exact mul_le_mul_of_nonneg_left hinner hscale
  have hmixed :
      c *
          (2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
                (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k) +
            4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
              (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k) ≤
        c *
          (2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
            4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
              (nativeHeatRareJ frames 2 k : ℚ)) := by
    have hrow1 :
        4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
            (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k ≤
          4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 1 k : ℚ) := by
      calc
        _ = 4 * ((nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1)) +
            (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k := by ring
        _ ≤ 4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 1 k : ℚ) :=
          add_le_add (mul_le_mul_of_nonneg_left hJ1loPow (by norm_num)) hJ1hiPow
    have hrow2 :
        4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
            (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k ≤
          4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 2 k : ℚ) := by
      calc
        _ = 4 * ((nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1)) +
            (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k := by ring
        _ ≤ 4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 2 k : ℚ) :=
          add_le_add (mul_le_mul_of_nonneg_left hJ2loPow (by norm_num)) hJ2hiPow
    have hinner :
        2 * (nativeHeatB : ℝ) *
            (4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
              (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k) +
          4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
            (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k ≤
        2 * (nativeHeatB : ℝ) *
            (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
              (nativeHeatRareJ frames 1 k : ℚ)) +
          4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 2 k : ℚ) := by
      calc
        _ = 2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
                (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k) +
            (4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
              (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k) := by ring
        _ ≤ 2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
            (4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
              (nativeHeatRareJ frames 2 k : ℚ)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrow1
              (by positivity : 0 ≤ 2 * (nativeHeatB : ℝ))) hrow2
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left hinner hc
  have hE :
      nativeHeatVHEATErrorEk k 20 (old.e : ℝ)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
          (frames.y : ℝ) (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
        ((nativeHeatFixedAnalyticRemainder old frames k +
          nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := by
    calc
      _ = (k : ℝ) * (old.e : ℝ) *
            ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
                (nativeHeatM : ℝ)) *
                (4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
                  (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k) +
              (nativeHeatM : ℝ) *
                (4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
                  (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k)) +
          c *
            (2 * (nativeHeatB : ℝ) *
                (4 * (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ (k - 1) +
                  (nativeHeatEps : ℝ) * (frames.x : ℝ) ^ k) +
              4 * (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ (k - 1) +
                (nativeHeatEps : ℝ) ^ 2 * (frames.x : ℝ) ^ k) +
          c * ((nativeHeatB : ℝ) ^ 2 * (frames.y : ℝ) ^ (k - 2) *
            (4 * (frames.x : ℝ) + (frames.x : ℝ) ^ 2)) := by
        rw [nativeHeatVHEATErrorEk_of_lt k 20 hk2 hkp]
        dsimp [c]
        ring
      _ ≤ (k : ℝ) * (old.e : ℝ) *
            ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
                (nativeHeatM : ℝ)) *
                (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                  (nativeHeatRareJ frames 1 k : ℚ)) +
              (nativeHeatM : ℝ) *
                (4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
                  (nativeHeatRareJ frames 2 k : ℚ))) +
          c *
            (2 * (nativeHeatB : ℝ) *
                (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                  (nativeHeatRareJ frames 1 k : ℚ)) +
              4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 2 k : ℚ)) +
          c * ((nativeHeatB : ℝ) ^ 2 * (frames.y : ℝ) ^ (k - 2) *
            (4 * (frames.x : ℝ) + (frames.x : ℝ) ^ 2)) := by
        exact add_le_add (add_le_add hbase hmixed) le_rfl
      _ = ((nativeHeatFixedAnalyticRemainder old frames k +
          nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := by
        unfold nativeHeatFixedAnalyticRemainder nativeHeatBracketRemainderAt
        simp [show 2 ≤ k from hk2]
        dsimp [c]
        ring
  have hfixedR :
      ((nativeHeatFixedAnalyticRemainder old frames k : ℚ) : ℝ) ≤
        (fixed.getD (k - 1) 0 : ℝ) := by exact_mod_cast hfixed
  have hcombined :
      ((nativeHeatFixedAnalyticRemainder old frames k : ℚ) : ℝ) +
          ((nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) ≤
        (fixed.getD (k - 1) 0 : ℝ) +
          ((nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) :=
    add_le_add hfixedR le_rfl
  have hround :
      (((fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℚ) : ℝ) ≤
        ((nativeUp (fixed.getD (k - 1) 0 +
          nativeHeatBracketRemainderAt old frames frames.y k) : ℚ) : ℝ) := by
    exact_mod_cast nativeUp_ge _
  have hcastA :
      ((nativeHeatFixedAnalyticRemainder old frames k +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) =
        (nativeHeatFixedAnalyticRemainder old frames k : ℝ) +
          (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := by
    exact_mod_cast (Rat.cast_add _ _)
  have hcastF :
      ((fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) =
        (fixed.getD (k - 1) 0 : ℝ) +
          (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := by
    exact_mod_cast (Rat.cast_add _ _)
  calc
    _ ≤ ((nativeHeatFixedAnalyticRemainder old frames k +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := hE
    _ = (nativeHeatFixedAnalyticRemainder old frames k : ℝ) +
        (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := hcastA
    _ ≤ (fixed.getD (k - 1) 0 : ℝ) +
        (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := hcombined
    _ = ((fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := hcastF.symm
    _ ≤ ((nativeUp (fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k) : ℚ) : ℝ) := hround
    _ = (nativeHeatForcingAt old frames fixed frames.y k : ℚ) := by
      rw [nativeHeatForcingAt_eq_explicit_remainder]

/-- Generic row comparison: once the four stable `J` entries are covered by
the rational rare table and the fixed vector covers the analytic remainder,
the whole VHEAT error, including the quadratic bracket, is below the rounded
forcing row. -/
theorem nativeHeatVHEATErrorEk_le_forcingAt_of_J_bounds
    (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed : List ℚ) (k : ℕ) (hk2 : 2 ≤ k)
    (hJ1lo : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 1 (k - 1) ≤ (nativeHeatRareJ frames 1 (k - 1) : ℚ))
    (hJ1hi : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 1 k ≤ (nativeHeatRareJ frames 1 k : ℚ))
    (hJ2lo : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 2 (k - 1) ≤ (nativeHeatRareJ frames 2 (k - 1) : ℚ))
    (hJ2hi : nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
        (frames.raw : ℝ) 20 2 k ≤ (nativeHeatRareJ frames 2 k : ℚ))
    (hold : 0 ≤ old.e)
    (hfixed : nativeHeatFixedAnalyticRemainder old frames k ≤
      fixed.getD (k - 1) 0) :
    nativeHeatVHEATErrorEk k 20 (old.e : ℝ)
        (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
        (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
        (frames.y : ℝ) (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
      (nativeHeatForcingAt old frames fixed frames.y k : ℚ) := by
  have he : 0 ≤ (old.e : ℝ) := by exact_mod_cast hold
  have hK : 0 ≤ (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  have hM : 0 ≤ (nativeHeatM : ℝ) := by norm_num [nativeHeatM]
  have hb : 0 ≤ (nativeHeatB : ℝ) := by
    have hq : 0 ≤ nativeHeatB := by decide +kernel
    exact_mod_cast hq
  let c : ℝ := 2 * (k : ℝ) * ((k : ℝ) - 1) * (old.e : ℝ) *
    (nativeHeatSB : ℝ) * (1 + (nativeHeatTheta : ℝ)⁻¹)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hk : 0 ≤ (k : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ k by omega))
    have hsb : 0 ≤ (nativeHeatSB : ℝ) := by norm_num [nativeHeatSB]
    have htheta : 0 < (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
    positivity
  have hrow1 :
      4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
          (frames.raw : ℝ) 20 1 (k - 1) +
        nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
          (frames.raw : ℝ) 20 1 k ≤
      4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
        (nativeHeatRareJ frames 1 k : ℚ) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hJ1lo (by norm_num)) hJ1hi
  have hrow2 :
      4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
          (frames.raw : ℝ) 20 2 (k - 1) +
        nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
          (frames.raw : ℝ) 20 2 k ≤
      4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
        (nativeHeatRareJ frames 2 k : ℚ) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hJ2lo (by norm_num)) hJ2hi
  have hcoef : 0 ≤ 2 * (nativeHeatK : ℝ) +
      2 * (nativeHeatB : ℝ) * (nativeHeatM : ℝ) := by positivity
  have hscale : 0 ≤ (k : ℝ) * (old.e : ℝ) := by positivity
  have hbase :
      (k : ℝ) * (old.e : ℝ) *
          ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
              (nativeHeatM : ℝ)) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 (k - 1) +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 k) +
            (nativeHeatM : ℝ) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 2 (k - 1) +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 2 k)) ≤
        (k : ℝ) * (old.e : ℝ) *
          ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
              (nativeHeatM : ℝ)) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
            (nativeHeatM : ℝ) *
              (4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 2 k : ℚ))) := by
    have hinner := add_le_add
      (mul_le_mul_of_nonneg_left hrow1 hcoef)
      (mul_le_mul_of_nonneg_left hrow2 hM)
    exact mul_le_mul_of_nonneg_left hinner hscale
  have hmixed :
      c *
          (2 * (nativeHeatB : ℝ) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 (k - 1) +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 k) +
            4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 2 (k - 1) +
              nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 2 k) ≤
        c *
          (2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
            4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
              (nativeHeatRareJ frames 2 k : ℚ)) := by
    have hinner :
        2 * (nativeHeatB : ℝ) *
            (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 1 (k - 1) +
              nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 1 k) +
          4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
              (frames.raw : ℝ) 20 2 (k - 1) +
            nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
              (frames.raw : ℝ) 20 2 k ≤
        2 * (nativeHeatB : ℝ) *
            (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
              (nativeHeatRareJ frames 1 k : ℚ)) +
          4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
            (nativeHeatRareJ frames 2 k : ℚ) := by
      calc
        _ = 2 * (nativeHeatB : ℝ) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 (k - 1) +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 k) +
            (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 2 (k - 1) +
              nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                (frames.raw : ℝ) 20 2 k) := by ring
        _ ≤ 2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
            (4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
              (nativeHeatRareJ frames 2 k : ℚ)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrow1
              (by positivity : 0 ≤ 2 * (nativeHeatB : ℝ))) hrow2
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left hinner hc
  have hE :
      nativeHeatVHEATErrorEk k 20 (old.e : ℝ)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
          (frames.y : ℝ) (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
        ((nativeHeatFixedAnalyticRemainder old frames k +
          nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := by
    calc
      _ = (k : ℝ) * (old.e : ℝ) *
            ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
                (nativeHeatM : ℝ)) *
                (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                    (frames.raw : ℝ) 20 1 (k - 1) +
                  nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                    (frames.raw : ℝ) 20 1 k) +
              (nativeHeatM : ℝ) *
                (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                    (frames.raw : ℝ) 20 2 (k - 1) +
                  nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                    (frames.raw : ℝ) 20 2 k)) +
          c * (2 * (nativeHeatB : ℝ) *
              (4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 (k - 1) +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 1 k) +
              4 * nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 2 (k - 1) +
                nativeHeatVHEATJ (nativeHeatEps : ℝ) (frames.x : ℝ)
                  (frames.raw : ℝ) 20 2 k) +
          c * ((nativeHeatB : ℝ) ^ 2 * (frames.y : ℝ) ^ (k - 2) *
            (4 * (frames.x : ℝ) + (frames.x : ℝ) ^ 2)) := by
        unfold nativeHeatVHEATErrorEk
        simp only [ite_eq_left hk2]
        dsimp [c]
        ring
      _ ≤ (k : ℝ) * (old.e : ℝ) *
            ((2 * (nativeHeatK : ℝ) + 2 * (nativeHeatB : ℝ) *
                (nativeHeatM : ℝ)) *
                (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                  (nativeHeatRareJ frames 1 k : ℚ)) +
              (nativeHeatM : ℝ) *
                (4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
                  (nativeHeatRareJ frames 2 k : ℚ))) +
          c * (2 * (nativeHeatB : ℝ) *
              (4 * (nativeHeatRareJ frames 1 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 1 k : ℚ)) +
              4 * (nativeHeatRareJ frames 2 (k - 1) : ℚ) +
                (nativeHeatRareJ frames 2 k : ℚ)) +
          c * ((nativeHeatB : ℝ) ^ 2 * (frames.y : ℝ) ^ (k - 2) *
            (4 * (frames.x : ℝ) + (frames.x : ℝ) ^ 2)) := by
        exact add_le_add (add_le_add hbase hmixed) le_rfl
      _ = ((nativeHeatFixedAnalyticRemainder old frames k +
          nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := by
        unfold nativeHeatFixedAnalyticRemainder nativeHeatBracketRemainderAt
        simp [show 2 ≤ k from hk2]
        dsimp [c]
        ring
  have hfixedR :
      ((nativeHeatFixedAnalyticRemainder old frames k : ℚ) : ℝ) ≤
        (fixed.getD (k - 1) 0 : ℝ) := by exact_mod_cast hfixed
  have hcombined :
      ((nativeHeatFixedAnalyticRemainder old frames k : ℚ) : ℝ) +
          ((nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) ≤
        (fixed.getD (k - 1) 0 : ℝ) +
          ((nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) :=
    add_le_add hfixedR le_rfl
  have hround :
      (((fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℚ) : ℝ) ≤
        ((nativeUp (fixed.getD (k - 1) 0 +
          nativeHeatBracketRemainderAt old frames frames.y k) : ℚ) : ℝ) := by
    exact_mod_cast nativeUp_ge _
  have hcastA :
      ((nativeHeatFixedAnalyticRemainder old frames k +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) =
        (nativeHeatFixedAnalyticRemainder old frames k : ℝ) +
          (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := by
    exact_mod_cast (Rat.cast_add _ _)
  have hcastF :
      ((fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) =
        (fixed.getD (k - 1) 0 : ℝ) +
          (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := by
    exact_mod_cast (Rat.cast_add _ _)
  calc
    _ ≤ ((nativeHeatFixedAnalyticRemainder old frames k +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := hE
    _ = (nativeHeatFixedAnalyticRemainder old frames k : ℝ) +
        (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := hcastA
    _ ≤ (fixed.getD (k - 1) 0 : ℝ) +
        (nativeHeatBracketRemainderAt old frames frames.y k : ℝ) := hcombined
    _ = ((fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k : ℚ) : ℝ) := hcastF.symm
    _ ≤ ((nativeUp (fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames frames.y k) : ℚ) : ℝ) := hround
    _ = (nativeHeatForcingAt old frames fixed frames.y k : ℚ) := by
      rw [nativeHeatForcingAt_eq_explicit_remainder]

/-- The final degree-20 error row is covered by the native forcing row when
the source frame supplies the two checked generalized-Hölder root certificates. -/
theorem nativeHeatVHEATErrorEk_top_le_forcingAt
    (old : NativeOldRow) (frames : NativeHeatFrameInputs) (fixed : List ℚ)
    (hold : 0 ≤ old.e) (hx : 0 < frames.x) (hraw : 0 ≤ frames.raw)
    (hvalid₁ : nativeRootValid ((frames.raw / frames.x) ^ 5) 27 = true)
    (hvalid₂ : nativeRootValid ((frames.raw / frames.x) ^ 10) 27 = true)
    (hfixed : nativeHeatFixedAnalyticRemainder old frames 20 ≤
      fixed.getD 19 0) :
    nativeHeatVHEATErrorEk 20 20 (old.e : ℝ)
        (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
        (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ)
        (frames.y : ℝ) (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
      (nativeHeatForcingAt old frames fixed frames.y 20 : ℚ) := by
  apply nativeHeatVHEATErrorEk_le_forcingAt_of_J_bounds
      old frames fixed 20 (by norm_num)
  · exact nativeHeatRareJ_ge_vheatJ_of_lt frames 1 19 (by norm_num) hx.le
  · exact nativeHeatRareJ_ge_vheatJ_top_one frames hx hraw hvalid₁
  · exact nativeHeatRareJ_ge_vheatJ_of_lt frames 2 19 (by norm_num) hx.le
  · exact nativeHeatRareJ_ge_vheatJ_top_two frames hx hraw hvalid₂
  · exact hold
  · exact hfixed

end ASDExplicitGamma.Native
