module

public import ASDExplicitGamma.Native.HeatVHEATBounds

/-! Theta scaling of the VHEAT error row with the rare amplitude `ε` held fixed (the OLD-bank
`3·10⁻⁴⁶`): the drift coefficient `e` carries the extra factor `τ`, so the error scales by `τ^k`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

/-- With `ε` and `F` fixed and `X` scaled by `τ ∈ (0,1]`, the envelope `J j l` at `l ∈ {k-1,k}`
loses at most `τ^(k-1)` (the top degree loses `τ^(20-5j/27)`, and `20-5j/27 ≥ 19`). -/
theorem nativeHeatVHEATJ_fixedEps_scaled_le
    (τ ε X F : ℝ) (j k l : ℕ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hX : 0 < X) (hF : 0 ≤ F) (hj : j ≤ 2) (hk1 : 1 ≤ k) (hk20 : k ≤ 20)
    (hl : k - 1 ≤ l) (hlk : l ≤ k) :
    nativeHeatVHEATJ ε (τ * X) F 20 j l ≤ τ ^ (k - 1) * nativeHeatVHEATJ ε X F 20 j l := by
  by_cases hlt : l < 20
  · simp only [nativeHeatVHEATJ, if_pos hlt, mul_pow]
    have : τ ^ l ≤ τ ^ (k - 1) := pow_le_pow_of_le_one hτ.le hτ1 hl
    have h0 : 0 ≤ ε ^ j * X ^ l := by positivity
    calc ε ^ j * (τ ^ l * X ^ l) = τ ^ l * (ε ^ j * X ^ l) := by ring
      _ ≤ τ ^ (k - 1) * (ε ^ j * X ^ l) := mul_le_mul_of_nonneg_right this h0
  · have hl20 : l = 20 := by omega
    subst l
    have hk : k = 20 := by omega
    subst k
    set α : ℝ := ((j * 20 : ℕ) : ℝ) / ((128 - 20 : ℕ) : ℝ) with hα
    have hα0 : 0 ≤ α := by positivity
    have hα1 : α ≤ 1 := by
      rw [hα, div_le_one (by norm_num)]
      have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      push_cast
      norm_num
      nlinarith
    simp only [nativeHeatVHEATJ, lt_irrefl, if_false]
    have hratio : F / (τ * X) = (F / X) / τ := by
      field_simp
    have hd : Real.rpow ((F / X) / τ) α = Real.rpow (F / X) α / Real.rpow τ α :=
      Real.div_rpow (div_nonneg hF hX.le) hτ.le α
    rw [hratio, hd]
    have hq : (τ ^ 19 : ℝ) * Real.rpow τ (1 - α) = τ ^ 20 / Real.rpow τ α * 1 := by
      have e1 : Real.rpow τ (1 - α) = τ / Real.rpow τ α := by
        have := Real.rpow_sub hτ 1 α
        rw [Real.rpow_one] at this
        exact this
      rw [e1]
      field_simp
    have hle : Real.rpow τ (1 - α) ≤ 1 := Real.rpow_le_one hτ.le hτ1 (by linarith)
    have hτα : 0 < Real.rpow τ α := Real.rpow_pos_of_pos hτ α
    have key : τ ^ 20 / Real.rpow τ α ≤ τ ^ 19 := by
      have : τ ^ 20 / Real.rpow τ α = τ ^ 19 * Real.rpow τ (1 - α) := by
        rw [hq]; ring
      rw [this]
      calc τ ^ 19 * Real.rpow τ (1 - α) ≤ τ ^ 19 * 1 :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = τ ^ 19 := by ring
    have hR : 0 ≤ ε ^ j * X ^ 20 * Real.rpow (F / X) α := by
      have := Real.rpow_nonneg (div_nonneg hF hX.le) α
      positivity
    calc ε ^ j * (τ * X) ^ 20 * (Real.rpow (F / X) α / Real.rpow τ α)
        = (τ ^ 20 / Real.rpow τ α) * (ε ^ j * X ^ 20 * Real.rpow (F / X) α) := by
          rw [mul_pow]; ring
      _ ≤ τ ^ 19 * (ε ^ j * X ^ 20 * Real.rpow (F / X) α) :=
          mul_le_mul_of_nonneg_right key hR

theorem nativeHeatVHEATErrorEk_fixedEps_scaled_le
    (τ e K M SB θ b X Y ε F : ℝ) (k : ℕ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (he : 0 ≤ e) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hSB : 0 ≤ SB) (hθ : 0 < θ) (hb : 0 ≤ b)
    (hX : 0 < X) (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hF : 0 ≤ F)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeHeatVHEATErrorEk k 20 (τ * e) K M SB θ b (τ * X) (τ * Y) ε F ≤
      τ ^ k * nativeHeatVHEATErrorEk k 20 e K M SB θ b X Y ε F := by
  let J : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X F 20
  let Jτ : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε (τ * X) F 20
  have hJn (j l : ℕ) : 0 ≤ J j l := nativeHeatVHEATJ_nonneg ε X F 20 j l hε hX hF
  have hJp (j l : ℕ) (hj : j ≤ 2) (hl : k - 1 ≤ l) (hlk : l ≤ k) :
      Jτ j l ≤ τ ^ (k - 1) * J j l :=
    nativeHeatVHEATJ_fixedEps_scaled_le τ ε X F j k l hτ hτ1 hε hX hF hj hk1 hk20 hl hlk
  have hpow : τ * τ ^ (k - 1) = τ ^ k := by
    rw [← pow_succ']; congr 1; omega
  have hs1 : 4 * Jτ 1 (k - 1) + Jτ 1 k ≤ τ ^ (k - 1) * (4 * J 1 (k - 1) + J 1 k) := by
    have a := hJp 1 (k - 1) (by norm_num) le_rfl (by omega)
    have b' := hJp 1 k (by norm_num) (by omega) le_rfl
    nlinarith
  have hs2 : 4 * Jτ 2 (k - 1) + Jτ 2 k ≤ τ ^ (k - 1) * (4 * J 2 (k - 1) + J 2 k) := by
    have a := hJp 2 (k - 1) (by norm_num) le_rfl (by omega)
    have b' := hJp 2 k (by norm_num) (by omega) le_rfl
    nlinarith
  have hc1 : 0 ≤ 2 * K + 2 * b * M := by
    have : 0 ≤ b * M := mul_nonneg hb hM
    positivity
  have hfirst :
      (2 * K + 2 * b * M) * (4 * Jτ 1 (k - 1) + Jτ 1 k) + M * (4 * Jτ 2 (k - 1) + Jτ 2 k) ≤
      τ ^ (k - 1) * ((2 * K + 2 * b * M) * (4 * J 1 (k - 1) + J 1 k) +
        M * (4 * J 2 (k - 1) + J 2 k)) := by
    have := mul_le_mul_of_nonneg_left hs1 hc1
    have := mul_le_mul_of_nonneg_left hs2 hM
    nlinarith
  have hfn : 0 ≤ (2 * K + 2 * b * M) * (4 * J 1 (k - 1) + J 1 k) +
        M * (4 * J 2 (k - 1) + J 2 k) := by
    have := hJn 1 (k - 1); have := hJn 1 k; have := hJn 2 (k - 1); have := hJn 2 k
    positivity
  have hbase : (k : ℝ) * (τ * e) *
      ((2 * K + 2 * b * M) * (4 * Jτ 1 (k - 1) + Jτ 1 k) + M * (4 * Jτ 2 (k - 1) + Jτ 2 k)) ≤
      τ ^ k * ((k : ℝ) * e * ((2 * K + 2 * b * M) * (4 * J 1 (k - 1) + J 1 k) +
        M * (4 * J 2 (k - 1) + J 2 k))) := by
    have hco : 0 ≤ (k : ℝ) * (τ * e) := by positivity
    calc _ ≤ (k : ℝ) * (τ * e) * (τ ^ (k - 1) * ((2 * K + 2 * b * M) * (4 * J 1 (k - 1) + J 1 k) +
        M * (4 * J 2 (k - 1) + J 2 k))) := mul_le_mul_of_nonneg_left hfirst hco
      _ = _ := by rw [← hpow]; ring
  have hYterm (hk : 2 ≤ k) :
      (τ * Y) ^ (k - 2) * (4 * (τ * X) + (τ * X) ^ 2) ≤
        τ ^ (k - 1) * (Y ^ (k - 2) * (4 * X + X ^ 2)) := by
    have h1 : τ ^ (k - 2) * τ = τ ^ (k - 1) := by
      rw [← pow_succ]; congr 1; omega
    have h2 : τ ^ (k - 2) * τ ^ 2 = τ ^ k := by
      rw [← pow_add]; congr 1; omega
    have h3 : τ ^ k ≤ τ ^ (k - 1) := pow_le_pow_of_le_one hτ.le hτ1 (by omega)
    have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
    have hYp : 0 ≤ Y ^ (k - 2) := pow_nonneg hY _
    calc (τ * Y) ^ (k - 2) * (4 * (τ * X) + (τ * X) ^ 2)
        = Y ^ (k - 2) * (4 * (τ ^ (k - 2) * τ) * X + (τ ^ (k - 2) * τ ^ 2) * X ^ 2) := by
          rw [mul_pow, mul_pow]; ring
      _ = Y ^ (k - 2) * (4 * τ ^ (k - 1) * X + τ ^ k * X ^ 2) := by rw [h1, h2]
      _ ≤ Y ^ (k - 2) * (4 * τ ^ (k - 1) * X + τ ^ (k - 1) * X ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hYp
          have := mul_le_mul_of_nonneg_right h3 hX2
          linarith
      _ = _ := by ring
  have hbr (hk : 2 ≤ k) :
      2 * (k : ℝ) * ((k : ℝ) - 1) * (τ * e) * SB * (1 + θ⁻¹) *
        (b ^ 2 * (τ * Y) ^ (k - 2) * (4 * (τ * X) + (τ * X) ^ 2) +
          2 * b * (4 * Jτ 1 (k - 1) + Jτ 1 k) + 4 * Jτ 2 (k - 1) + Jτ 2 k) ≤
      τ ^ k * (2 * (k : ℝ) * ((k : ℝ) - 1) * e * SB * (1 + θ⁻¹) *
        (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
          2 * b * (4 * J 1 (k - 1) + J 1 k) + 4 * J 2 (k - 1) + J 2 k)) := by
    have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkm : 0 ≤ (k : ℝ) - 1 := by linarith
    have hco : 0 ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) * e * SB * (1 + θ⁻¹) := by positivity
    have hin : b ^ 2 * (τ * Y) ^ (k - 2) * (4 * (τ * X) + (τ * X) ^ 2) +
          2 * b * (4 * Jτ 1 (k - 1) + Jτ 1 k) + 4 * Jτ 2 (k - 1) + Jτ 2 k ≤
        τ ^ (k - 1) * (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
          2 * b * (4 * J 1 (k - 1) + J 1 k) + 4 * J 2 (k - 1) + J 2 k) := by
      have a1 := mul_le_mul_of_nonneg_left (hYterm hk) (sq_nonneg b)
      have a2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 2 * b)
      nlinarith [a1, a2, hs2]
    calc _ = (2 * (k : ℝ) * ((k : ℝ) - 1) * e * SB * (1 + θ⁻¹)) * (τ * (b ^ 2 * (τ * Y) ^ (k - 2) *
          (4 * (τ * X) + (τ * X) ^ 2) + 2 * b * (4 * Jτ 1 (k - 1) + Jτ 1 k) +
          4 * Jτ 2 (k - 1) + Jτ 2 k)) := by ring
      _ ≤ (2 * (k : ℝ) * ((k : ℝ) - 1) * e * SB * (1 + θ⁻¹)) * (τ * (τ ^ (k - 1) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) + 2 * b * (4 * J 1 (k - 1) + J 1 k) +
            4 * J 2 (k - 1) + J 2 k))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin hτ.le) hco
      _ = _ := by rw [← mul_assoc τ, hpow]; ring
  change (k : ℝ) * (τ * e) *
      ((2 * K + 2 * b * M) * (4 * Jτ 1 (k - 1) + Jτ 1 k) + M * (4 * Jτ 2 (k - 1) + Jτ 2 k)) +
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * (τ * e) * SB * (1 + θ⁻¹) *
          (b ^ 2 * (τ * Y) ^ (k - 2) * (4 * (τ * X) + (τ * X) ^ 2) +
            2 * b * (4 * Jτ 1 (k - 1) + Jτ 1 k) + 4 * Jτ 2 (k - 1) + Jτ 2 k) else 0) ≤
      τ ^ k * ((k : ℝ) * e * ((2 * K + 2 * b * M) * (4 * J 1 (k - 1) + J 1 k) +
          M * (4 * J 2 (k - 1) + J 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e * SB * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * J 1 (k - 1) + J 1 k) + 4 * J 2 (k - 1) + J 2 k) else 0))
  by_cases hk : 2 ≤ k
  · simp only [if_pos hk]
    have := add_le_add hbase (hbr hk)
    rw [mul_add]
    linarith
  · simp only [if_neg hk, add_zero]
    exact hbase

end ASDExplicitGamma.Native
