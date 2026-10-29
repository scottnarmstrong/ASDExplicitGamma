module

public import ASDExplicitGamma.Native.HeatVHEATError

/-! Sign bounds for the stable native VHEAT error interface. -/

@[expose] public section

namespace ASDExplicitGamma.Native

/-- The VHEAT generalized-Hölder envelope is nonnegative on the source range. -/
theorem nativeHeatVHEATJ_nonneg
    (ε X F : ℝ) (p j l : ℕ) (hε : 0 ≤ ε) (hX : 0 < X) (hF : 0 ≤ F) :
    0 ≤ nativeHeatVHEATJ ε X F p j l := by
  unfold nativeHeatVHEATJ
  split_ifs with hlt
  · positivity
  · apply mul_nonneg
    · exact mul_nonneg (pow_nonneg hε j) (pow_nonneg hX.le p)
    · apply Real.rpow_nonneg
      exact div_nonneg hF hX.le

/-- Below the top degree, the VHEAT envelope is the ordinary power term. -/
theorem nativeHeatVHEATJ_of_lt
    (ε X F : ℝ) (p j l : ℕ) (hl : l < p) :
    nativeHeatVHEATJ ε X F p j l = ε ^ j * X ^ l := by
  simp [nativeHeatVHEATJ, hl]

/-- At the top degree, the VHEAT envelope carries the generalized-Hölder
factor with denominator `128-p`. -/
theorem nativeHeatVHEATJ_top
    (ε X F : ℝ) (p j : ℕ) :
    nativeHeatVHEATJ ε X F p j p =
      ε ^ j * X ^ p * Real.rpow (F / X)
        (((j * p : ℕ) : ℝ) / ((128 - p : ℕ) : ℝ)) := by
  simp [nativeHeatVHEATJ]

/-- Increasing the raw remainder envelope can only increase `J`, provided the
source exponent denominator is positive. -/
theorem nativeHeatVHEATJ_mono_F
    (ε X F₁ F₂ : ℝ) (p j l : ℕ)
    (hε : 0 ≤ ε) (hX : 0 < X) (hF₁ : 0 ≤ F₁) (hF : F₁ ≤ F₂)
    (hp : p < 128) :
    nativeHeatVHEATJ ε X F₁ p j l ≤ nativeHeatVHEATJ ε X F₂ p j l := by
  unfold nativeHeatVHEATJ
  split_ifs with hl
  · rfl
  · have hden : 0 < ((128 - p : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 128 - p by omega)
    have hexp : 0 ≤ (((j * p : ℕ) : ℝ) / ((128 - p : ℕ) : ℝ)) :=
      div_nonneg (Nat.cast_nonneg _) hden.le
    have hbase : 0 ≤ F₁ / X := div_nonneg hF₁ hX.le
    have hbasele : F₁ / X ≤ F₂ / X :=
      div_le_div_of_nonneg_right hF hX.le
    have hrpow := Real.rpow_le_rpow hbase hbasele hexp
    apply mul_le_mul_of_nonneg_left hrpow
    exact mul_nonneg (pow_nonneg hε j) (pow_nonneg hX.le p)

/-- Increasing the inverse-error coefficient can only increase the complete
generalized-Hölder envelope, including its top-degree row. -/
theorem nativeHeatVHEATJ_mono_eps
    (ε₁ ε₂ X F : ℝ) (p j l : ℕ)
    (hε₁ : 0 ≤ ε₁) (hε : ε₁ ≤ ε₂) (hX : 0 < X) (hF : 0 ≤ F) :
    nativeHeatVHEATJ ε₁ X F p j l ≤ nativeHeatVHEATJ ε₂ X F p j l := by
  have hpow : ε₁ ^ j ≤ ε₂ ^ j := pow_le_pow_left₀ hε₁ hε j
  unfold nativeHeatVHEATJ
  split_ifs with hl
  · exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hX.le l)
  · apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (pow_nonneg hX.le p))
    exact Real.rpow_nonneg (div_nonneg hF hX.le) _

/-- At the producer degree twenty, the top generalized-Hölder envelope is
increasing in the trace cap `X`: its power `20` absorbs the denominator in
`(F/X)^(jp/108)` for the two source orders `j≤2`. -/
theorem nativeHeatVHEATJ_mono_X_p20
    (ε F X₁ X₂ : ℝ) (j l : ℕ)
    (hε : 0 ≤ ε) (hF : 0 ≤ F) (hX₁ : 0 < X₁) (hX : X₁ ≤ X₂)
    (hj : j ≤ 2) (hl : l ≤ 20) :
    nativeHeatVHEATJ ε X₁ F 20 j l ≤ nativeHeatVHEATJ ε X₂ F 20 j l := by
  have hX₂ : 0 < X₂ := lt_of_lt_of_le hX₁ hX
  by_cases hlt : l < 20
  · simp [nativeHeatVHEATJ, hlt]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hX₁.le hX l) (pow_nonneg hε j)
  · have hlEq : l = 20 := by omega
    subst l
    let α : ℝ := ((j * 20 : ℕ) : ℝ) / ((128 - 20 : ℕ) : ℝ)
    let r : ℝ := X₂ / X₁
    have hα_nonneg : 0 ≤ α := by dsimp [α]; positivity
    have hj20 : j * 20 ≤ 40 := by omega
    have hα_le : α ≤ 20 := by
      dsimp [α]
      have hj20R : ((j * 20 : ℕ) : ℝ) ≤ 40 := by exact_mod_cast hj20
      norm_num at hj20R ⊢
      nlinarith [hj20R]
    have hrone : 1 ≤ r := by
      dsimp [r]
      exact (le_div_iff₀ hX₁).2 (by nlinarith)
    have hrnonneg : 0 ≤ r := by linarith
    have hrpow : r ^ α ≤ r ^ (20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hrone hα_le
    have hratio : F / X₁ = (F / X₂) * r := by
      dsimp [r]
      field_simp [ne_of_gt hX₁, ne_of_gt hX₂]
    have hpowmul : (F / X₁) ^ α = (F / X₂) ^ α * r ^ α := by
      rw [hratio, Real.mul_rpow (div_nonneg hF hX₂.le) hrnonneg]
    have hcore : X₁ ^ 20 * r ^ α ≤ X₂ ^ 20 := by
      calc
        X₁ ^ 20 * r ^ α ≤ X₁ ^ 20 * r ^ (20 : ℝ) :=
          mul_le_mul_of_nonneg_left hrpow (pow_nonneg hX₁.le 20)
        _ = X₁ ^ 20 * (X₂ / X₁) ^ 20 := by
          change X₁ ^ 20 * Real.rpow r ((20 : ℕ) : ℝ) = _
          rw [← Real.rpow_natCast r 20]
          rfl
        _ = X₂ ^ 20 := by
          field_simp [ne_of_gt hX₁]
    have hcoef : 0 ≤ ε ^ j * (F / X₂) ^ α := by
      exact mul_nonneg (pow_nonneg hε j)
        (Real.rpow_nonneg (div_nonneg hF hX₂.le) α)
    have htop : ε ^ j * X₁ ^ 20 * (F / X₁) ^ α ≤
        ε ^ j * X₂ ^ 20 * (F / X₂) ^ α := by
      calc
        ε ^ j * X₁ ^ 20 * (F / X₁) ^ α =
            ε ^ j * (F / X₂) ^ α * (X₁ ^ 20 * r ^ α) := by
              rw [hpowmul]
              ring
        _ ≤ ε ^ j * (F / X₂) ^ α * X₂ ^ 20 :=
          mul_le_mul_of_nonneg_left hcore hcoef
        _ = ε ^ j * X₂ ^ 20 * (F / X₂) ^ α := by ring
    simpa [nativeHeatVHEATJ, α] using htop

/-- The degree-one VHEAT error contains only the two inverse-history orders;
the higher-order Young bracket vanishes, and for every producer order p≥2
the generalized-Hölder rows reduce to their ordinary powers. -/
theorem nativeHeatVHEATErrorEk_one_eq
    (p : ℕ) (hp : 2 ≤ p)
    (e_h K M S_B θ b X Y ε F : ℝ) :
    nativeHeatVHEATErrorEk 1 p e_h K M S_B θ b X Y ε F =
      e_h * ((2 * K + 2 * b * M) * (4 * ε + ε * X) +
        M * (4 * ε ^ 2 + ε ^ 2 * X)) := by
  unfold nativeHeatVHEATErrorEk
  simp only [nativeHeatVHEATJ,
    ite_eq_left (show 0 < p by omega), ite_eq_left (show 1 < p by omega),
    ite_eq_right (show ¬ 2 ≤ 1 by omega), pow_one, Nat.cast_one]
  ring

/-- Every non-top degree has a closed VHEAT error row: all four generalized-
Hölder inputs reduce to their ordinary-power expressions, while the full
quadratic Young bracket remains explicit. -/
theorem nativeHeatVHEATErrorEk_of_lt
    (k p : ℕ) (hk2 : 2 ≤ k) (hkp : k < p)
    (e_h K M S_B θ b X Y ε F : ℝ) :
    nativeHeatVHEATErrorEk k p e_h K M S_B θ b X Y ε F =
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) *
              (4 * ε * X ^ (k - 1) + ε * X ^ k) +
            M * (4 * ε ^ 2 * X ^ (k - 1) + ε ^ 2 * X ^ k)) +
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * ε * X ^ (k - 1) + ε * X ^ k) +
            4 * ε ^ 2 * X ^ (k - 1) + ε ^ 2 * X ^ k) := by
  have hklo : k - 1 < p := by omega
  unfold nativeHeatVHEATErrorEk
  simp [nativeHeatVHEATJ, hk2, hkp, hklo]
  ring

/-- Raising the raw remainder envelope can only raise the complete VHEAT
error row. This keeps the inverse part, the Young bracket, and the explicit
`k < 2` zero convention together under the same `E_k` interface. -/
theorem nativeHeatVHEATErrorEk_mono_F
    (k p : ℕ) (e_h K M S_B θ b X Y F₁ F₂ ε : ℝ)
    (he : 0 ≤ e_h) (hK : 0 ≤ K) (hM : 0 ≤ M) (hSB : 0 ≤ S_B)
    (hθ : 0 < θ) (hb : 0 ≤ b) (hX : 0 < X)
    (hε : 0 ≤ ε) (hF₁ : 0 ≤ F₁) (hF : F₁ ≤ F₂)
    (hp : p < 128) :
    nativeHeatVHEATErrorEk k p e_h K M S_B θ b X Y ε F₁ ≤
      nativeHeatVHEATErrorEk k p e_h K M S_B θ b X Y ε F₂ := by
  let JL : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X F₁ p
  let JR : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X F₂ p
  have hJ (j l : ℕ) : JL j l ≤ JR j l := by
    exact nativeHeatVHEATJ_mono_F ε X F₁ F₂ p j l hε hX hF₁ hF hp
  have hJL (j l : ℕ) : 0 ≤ JL j l :=
    nativeHeatVHEATJ_nonneg ε X F₁ p j l hε hX hF₁
  have hsum1 : 4 * JL 1 (k - 1) + JL 1 k ≤
      4 * JR 1 (k - 1) + JR 1 k := by
    nlinarith [hJ 1 (k - 1), hJ 1 k]
  have hsum2 : 4 * JL 2 (k - 1) + JL 2 k ≤
      4 * JR 2 (k - 1) + JR 2 k := by
    nlinarith [hJ 2 (k - 1), hJ 2 k]
  have hcoef1 : 0 ≤ 2 * K + 2 * b * M := by positivity
  have hcoef2 : 0 ≤ M := hM
  have hfirst :
      (2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
        M * (4 * JL 2 (k - 1) + JL 2 k) ≤
      (2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
        M * (4 * JR 2 (k - 1) + JR 2 k) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hcoef1)
      (mul_le_mul_of_nonneg_left hsum2 hcoef2)
  have hbase :
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
            M * (4 * JL 2 (k - 1) + JL 2 k)) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
            M * (4 * JR 2 (k - 1) + JR 2 k)) := by
    exact mul_le_mul_of_nonneg_left hfirst
      (mul_nonneg (Nat.cast_nonneg k) he)
  have hbracket :
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
            4 * JL 2 (k - 1) + JL 2 k)
       else 0) ≤
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
            4 * JR 2 (k - 1) + JR 2 k)
       else 0) := by
    by_cases hk : 2 ≤ k
    · simp [hk]
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (show 1 ≤ k by omega)
      have hcoeff : 0 ≤
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) := by
        have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.le
        positivity
      have hinner :
          b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
            4 * JL 2 (k - 1) + JL 2 k ≤
          b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
            4 * JR 2 (k - 1) + JR 2 k := by
        have hB := mul_le_mul_of_nonneg_left hsum1 (by positivity : 0 ≤ 2 * b)
        nlinarith [hB, hsum2]
      exact mul_le_mul_of_nonneg_left hinner hcoeff
    · simp [hk]
  change
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
            M * (4 * JL 2 (k - 1) + JL 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
              4 * JL 2 (k - 1) + JL 2 k)
         else 0) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
            M * (4 * JR 2 (k - 1) + JR 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
              4 * JR 2 (k - 1) + JR 2 k)
         else 0)
  exact add_le_add hbase hbracket

/-- Raising the inverse-error coefficient raises every nonnegative term in the
full VHEAT `E_k` expression. The zero bracket for `k < 2` is preserved. -/
theorem nativeHeatVHEATErrorEk_mono_eps
    (k p : ℕ) (e_h K M S_B θ b X Y F ε₁ ε₂ : ℝ)
    (he : 0 ≤ e_h) (hK : 0 ≤ K) (hM : 0 ≤ M) (hSB : 0 ≤ S_B)
    (hθ : 0 < θ) (hb : 0 ≤ b) (hX : 0 < X)
    (hF : 0 ≤ F) (hε₁ : 0 ≤ ε₁) (hε : ε₁ ≤ ε₂) :
    nativeHeatVHEATErrorEk k p e_h K M S_B θ b X Y ε₁ F ≤
      nativeHeatVHEATErrorEk k p e_h K M S_B θ b X Y ε₂ F := by
  let JL : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε₁ X F p
  let JR : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε₂ X F p
  have hJ (j l : ℕ) : JL j l ≤ JR j l := by
    exact nativeHeatVHEATJ_mono_eps ε₁ ε₂ X F p j l hε₁ hε hX hF
  have hsum1 : 4 * JL 1 (k - 1) + JL 1 k ≤
      4 * JR 1 (k - 1) + JR 1 k := by
    nlinarith [hJ 1 (k - 1), hJ 1 k]
  have hsum2 : 4 * JL 2 (k - 1) + JL 2 k ≤
      4 * JR 2 (k - 1) + JR 2 k := by
    nlinarith [hJ 2 (k - 1), hJ 2 k]
  have hcoef1 : 0 ≤ 2 * K + 2 * b * M := by positivity
  have hfirst :
      (2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
        M * (4 * JL 2 (k - 1) + JL 2 k) ≤
      (2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
        M * (4 * JR 2 (k - 1) + JR 2 k) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hcoef1)
      (mul_le_mul_of_nonneg_left hsum2 hM)
  have hbase :
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
            M * (4 * JL 2 (k - 1) + JL 2 k)) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
            M * (4 * JR 2 (k - 1) + JR 2 k)) := by
    exact mul_le_mul_of_nonneg_left hfirst
      (mul_nonneg (Nat.cast_nonneg k) he)
  have hbracket :
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
            4 * JL 2 (k - 1) + JL 2 k)
       else 0) ≤
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
            4 * JR 2 (k - 1) + JR 2 k)
       else 0) := by
    by_cases hk : 2 ≤ k
    · simp [hk]
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (show 1 ≤ k by omega)
      have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.le
      have hcoeff : 0 ≤
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) := by
        positivity
      have hB := mul_le_mul_of_nonneg_left hsum1 (by positivity : 0 ≤ 2 * b)
      have hinner :
          b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
            4 * JL 2 (k - 1) + JL 2 k ≤
          b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
            4 * JR 2 (k - 1) + JR 2 k := by
        nlinarith [hB, hsum2]
      exact mul_le_mul_of_nonneg_left hinner hcoeff
    · simp [hk]
  change
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
            M * (4 * JL 2 (k - 1) + JL 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
              4 * JL 2 (k - 1) + JL 2 k)
         else 0) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
            M * (4 * JR 2 (k - 1) + JR 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
              4 * JR 2 (k - 1) + JR 2 k)
         else 0)
  exact add_le_add hbase hbracket

/-- Raising the degree-twenty trace cap can only raise the complete VHEAT
error. This comparison covers both the generalized-Hölder top row and the
explicit quadratic heat bracket. -/
theorem nativeHeatVHEATErrorEk_mono_X_p20
    (k : ℕ) (e_h K M S_B θ b X₁ X₂ Y ε F : ℝ)
    (hk : k ≤ 20)
    (he : 0 ≤ e_h) (hK : 0 ≤ K) (hM : 0 ≤ M) (hSB : 0 ≤ S_B)
    (hθ : 0 < θ) (hb : 0 ≤ b) (hX₁ : 0 < X₁) (hX : X₁ ≤ X₂)
    (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hF : 0 ≤ F) :
    nativeHeatVHEATErrorEk k 20 e_h K M S_B θ b X₁ Y ε F ≤
      nativeHeatVHEATErrorEk k 20 e_h K M S_B θ b X₂ Y ε F := by
  let JL : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X₁ F 20
  let JR : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X₂ F 20
  have hX₂ : 0 < X₂ := lt_of_lt_of_le hX₁ hX
  have hkminus : k - 1 ≤ 20 := by omega
  have hJ (j l : ℕ) (hj : j ≤ 2) (hl : l ≤ 20) : JL j l ≤ JR j l := by
    exact nativeHeatVHEATJ_mono_X_p20 ε F X₁ X₂ j l
      hε hF hX₁ hX hj hl
  have hsum1 : 4 * JL 1 (k - 1) + JL 1 k ≤
      4 * JR 1 (k - 1) + JR 1 k := by
    have h1 := hJ 1 (k - 1) (by norm_num) hkminus
    have h2 := hJ 1 k (by norm_num) hk
    nlinarith [h1, h2]
  have hsum2 : 4 * JL 2 (k - 1) + JL 2 k ≤
      4 * JR 2 (k - 1) + JR 2 k := by
    have h1 := hJ 2 (k - 1) (by norm_num) hkminus
    have h2 := hJ 2 k (by norm_num) hk
    nlinarith [h1, h2]
  have hcoef1 : 0 ≤ 2 * K + 2 * b * M := by positivity
  have hfirst :
      (2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
        M * (4 * JL 2 (k - 1) + JL 2 k) ≤
      (2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
        M * (4 * JR 2 (k - 1) + JR 2 k) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hcoef1)
      (mul_le_mul_of_nonneg_left hsum2 hM)
  have hbase :
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
            M * (4 * JL 2 (k - 1) + JL 2 k)) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
            M * (4 * JR 2 (k - 1) + JR 2 k)) := by
    exact mul_le_mul_of_nonneg_left hfirst
      (mul_nonneg (Nat.cast_nonneg k) he)
  have hquad : 4 * X₁ + X₁ ^ 2 ≤ 4 * X₂ + X₂ ^ 2 := by
    have hsq := mul_le_mul hX₁.le hX (by positivity) (by positivity)
    nlinarith [hsq]
  have hbracket :
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X₁ + X₁ ^ 2) +
            2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
            4 * JL 2 (k - 1) + JL 2 k)
       else 0) ≤
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) +
            2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
            4 * JR 2 (k - 1) + JR 2 k)
       else 0) := by
    by_cases hk : 2 ≤ k
    · simp [hk]
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (show 1 ≤ k by omega)
      have hthetaInv : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.le
      have hcoeff : 0 ≤
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) := by
        positivity
      have hXterm : b ^ 2 * Y ^ (k - 2) * (4 * X₁ + X₁ ^ 2) ≤
          b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hquad
          (mul_nonneg (sq_nonneg b) (pow_nonneg hY _))
      have hJterm : 2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
          4 * JL 2 (k - 1) + JL 2 k ≤
          2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
          4 * JR 2 (k - 1) + JR 2 k := by
        have hB := mul_le_mul_of_nonneg_left hsum1
          (by positivity : 0 ≤ 2 * b)
        nlinarith only [hB, hsum2]
      have hinner : b ^ 2 * Y ^ (k - 2) * (4 * X₁ + X₁ ^ 2) +
          2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
          4 * JL 2 (k - 1) + JL 2 k ≤
          b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) +
          2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
          4 * JR 2 (k - 1) + JR 2 k := by
        nlinarith only [hXterm, hJterm]
      exact mul_le_mul_of_nonneg_left hinner hcoeff
    · simp [hk]
  change
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
            M * (4 * JL 2 (k - 1) + JL 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X₁ + X₁ ^ 2) +
              2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
              4 * JL 2 (k - 1) + JL 2 k)
         else 0) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
            M * (4 * JR 2 (k - 1) + JR 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) +
              2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
              4 * JR 2 (k - 1) + JR 2 k)
         else 0)
  exact add_le_add hbase hbracket

/-- Raising the OLD local inverse-bank cap can only raise the full VHEAT
error row. This comparison keeps both the linear inverse contribution and
the quadratic shear bracket under the same stable `E_k` interface. -/
theorem nativeHeatVHEATErrorEk_mono_b
    (k p : ℕ) (e_h K M S_B θ b₁ b₂ X Y ε F : ℝ)
    (he : 0 ≤ e_h) (hM : 0 ≤ M) (hSB : 0 ≤ S_B)
    (hθ : 0 < θ) (hb₁ : 0 ≤ b₁) (hb : b₁ ≤ b₂) (hX : 0 < X)
    (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hF : 0 ≤ F) :
    nativeHeatVHEATErrorEk k p e_h K M S_B θ b₁ X Y ε F ≤
      nativeHeatVHEATErrorEk k p e_h K M S_B θ b₂ X Y ε F := by
  let J : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X F p
  have hJ (j l : ℕ) : 0 ≤ J j l :=
    nativeHeatVHEATJ_nonneg ε X F p j l hε hX hF
  have hsum1 : 0 ≤ 4 * J 1 (k - 1) + J 1 k :=
    add_nonneg (mul_nonneg (by norm_num) (hJ 1 (k - 1))) (hJ 1 k)
  have hsum2 : 0 ≤ 4 * J 2 (k - 1) + J 2 k :=
    add_nonneg (mul_nonneg (by norm_num) (hJ 2 (k - 1))) (hJ 2 k)
  have hcoef : 2 * K + 2 * b₁ * M ≤ 2 * K + 2 * b₂ * M := by
    have hmul : b₁ * M ≤ b₂ * M := mul_le_mul_of_nonneg_right hb hM
    nlinarith [hmul]
  have hfirst :
      (2 * K + 2 * b₁ * M) * (4 * J 1 (k - 1) + J 1 k) +
        M * (4 * J 2 (k - 1) + J 2 k) ≤
      (2 * K + 2 * b₂ * M) * (4 * J 1 (k - 1) + J 1 k) +
        M * (4 * J 2 (k - 1) + J 2 k) := by
    exact add_le_add (mul_le_mul_of_nonneg_right hcoef hsum1) le_rfl
  have hbase :
      (k : ℝ) * e_h *
          ((2 * K + 2 * b₁ * M) * (4 * J 1 (k - 1) + J 1 k) +
            M * (4 * J 2 (k - 1) + J 2 k)) ≤
      (k : ℝ) * e_h *
          ((2 * K + 2 * b₂ * M) * (4 * J 1 (k - 1) + J 1 k) +
            M * (4 * J 2 (k - 1) + J 2 k)) := by
    exact mul_le_mul_of_nonneg_left hfirst
      (mul_nonneg (Nat.cast_nonneg k) he)
  by_cases hk : 2 ≤ k
  · have hkR : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show 1 ≤ k by omega)
    have hcoeff : 0 ≤
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) := by
      have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.le
      positivity
    have hsq : b₁ ^ 2 ≤ b₂ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb)
        (add_nonneg hb₁ (le_trans hb₁ hb))]
    have hYpow : 0 ≤ Y ^ (k - 2) := pow_nonneg hY _
    have hXfactor : 0 ≤ 4 * X + X ^ 2 := by positivity
    have hquad :
        b₁ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) ≤
          b₂ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hXfactor
      exact mul_le_mul_of_nonneg_right hsq hYpow
    have hlinear : 2 * b₁ * (4 * J 1 (k - 1) + J 1 k) ≤
        2 * b₂ * (4 * J 1 (k - 1) + J 1 k) := by
      apply mul_le_mul_of_nonneg_right _ hsum1
      nlinarith
    have hinner :
        b₁ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b₁ * (4 * J 1 (k - 1) + J 1 k) +
            4 * J 2 (k - 1) + J 2 k ≤
          b₂ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b₂ * (4 * J 1 (k - 1) + J 1 k) +
            4 * J 2 (k - 1) + J 2 k := by
      calc
        _ = (b₁ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b₁ * (4 * J 1 (k - 1) + J 1 k)) +
            (4 * J 2 (k - 1) + J 2 k) := by ring
        _ ≤ (b₂ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b₂ * (4 * J 1 (k - 1) + J 1 k)) +
            (4 * J 2 (k - 1) + J 2 k) :=
          add_le_add (add_le_add hquad hlinear) le_rfl
        _ = _ := by ring
    have hbracket :
        2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b₁ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b₁ * (4 * J 1 (k - 1) + J 1 k) +
              4 * J 2 (k - 1) + J 2 k) ≤
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b₂ ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b₂ * (4 * J 1 (k - 1) + J 1 k) +
              4 * J 2 (k - 1) + J 2 k) :=
      mul_le_mul_of_nonneg_left hinner hcoeff
    simpa [nativeHeatVHEATErrorEk, hk, J] using add_le_add hbase hbracket
  · simpa [nativeHeatVHEATErrorEk, hk, J] using hbase

/-- The complete VHEAT error is monotone when the drift rate and remainder
coefficients are raised together. This lets later heat bounds substitute
certified upper caps without expanding or changing the `E_k` interface. -/
theorem nativeHeatVHEATErrorEk_mono_drift_remainder
    (k p : ℕ) (e₁ e₂ K₁ K₂ M₁ M₂ S₁ S₂ θ b X Y ε F : ℝ)
    (he₁ : 0 ≤ e₁) (he : e₁ ≤ e₂)
    (hK₁ : 0 ≤ K₁) (hK : K₁ ≤ K₂)
    (hM₁ : 0 ≤ M₁) (hM : M₁ ≤ M₂)
    (hS₁ : 0 ≤ S₁) (hS : S₁ ≤ S₂)
    (hθ : 0 < θ) (hb : 0 ≤ b) (hX : 0 < X) (hY : 0 ≤ Y)
    (hε : 0 ≤ ε) (hF : 0 ≤ F) :
    nativeHeatVHEATErrorEk k p e₁ K₁ M₁ S₁ θ b X Y ε F ≤
      nativeHeatVHEATErrorEk k p e₂ K₂ M₂ S₂ θ b X Y ε F := by
  let J : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X F p
  have hK₂ : 0 ≤ K₂ := le_trans hK₁ hK
  have hM₂ : 0 ≤ M₂ := le_trans hM₁ hM
  have hS₂ : 0 ≤ S₂ := le_trans hS₁ hS
  have he₂ : 0 ≤ e₂ := le_trans he₁ he
  have hJ (j l : ℕ) : 0 ≤ J j l :=
    nativeHeatVHEATJ_nonneg ε X F p j l hε hX hF
  have hsum₁ : 0 ≤ 4 * J 1 (k - 1) + J 1 k :=
    add_nonneg (mul_nonneg (by norm_num) (hJ 1 (k - 1))) (hJ 1 k)
  have hsum₂ : 0 ≤ 4 * J 2 (k - 1) + J 2 k :=
    add_nonneg (mul_nonneg (by norm_num) (hJ 2 (k - 1))) (hJ 2 k)
  have hcoef : 2 * K₁ + 2 * b * M₁ ≤ 2 * K₂ + 2 * b * M₂ := by
    have hbm : b * M₁ ≤ b * M₂ := mul_le_mul_of_nonneg_left hM hb
    nlinarith [hK]
  have hfirst :
      (2 * K₁ + 2 * b * M₁) * (4 * J 1 (k - 1) + J 1 k) +
          M₁ * (4 * J 2 (k - 1) + J 2 k) ≤
        (2 * K₂ + 2 * b * M₂) * (4 * J 1 (k - 1) + J 1 k) +
          M₂ * (4 * J 2 (k - 1) + J 2 k) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right hcoef hsum₁)
      (mul_le_mul_of_nonneg_right hM hsum₂)
  have hfirst₂ : 0 ≤
      (2 * K₂ + 2 * b * M₂) * (4 * J 1 (k - 1) + J 1 k) +
        M₂ * (4 * J 2 (k - 1) + J 2 k) := by
    have hcoef₂ : 0 ≤ 2 * K₂ + 2 * b * M₂ := by positivity
    exact add_nonneg (mul_nonneg hcoef₂ hsum₁) (mul_nonneg hM₂ hsum₂)
  have hfirst₁ : 0 ≤
      (2 * K₁ + 2 * b * M₁) * (4 * J 1 (k - 1) + J 1 k) +
        M₁ * (4 * J 2 (k - 1) + J 2 k) := by
    have hcoef₁ : 0 ≤ 2 * K₁ + 2 * b * M₁ := by positivity
    exact add_nonneg (mul_nonneg hcoef₁ hsum₁) (mul_nonneg hM₁ hsum₂)
  have hbase :
      (k : ℝ) * e₁ *
          ((2 * K₁ + 2 * b * M₁) * (4 * J 1 (k - 1) + J 1 k) +
            M₁ * (4 * J 2 (k - 1) + J 2 k)) ≤
        (k : ℝ) * e₂ *
          ((2 * K₂ + 2 * b * M₂) * (4 * J 1 (k - 1) + J 1 k) +
            M₂ * (4 * J 2 (k - 1) + J 2 k)) := by
    have hscaled := mul_le_mul he hfirst hfirst₁ he₂
    calc
      (k : ℝ) * e₁ *
          ((2 * K₁ + 2 * b * M₁) * (4 * J 1 (k - 1) + J 1 k) +
            M₁ * (4 * J 2 (k - 1) + J 2 k)) =
          (k : ℝ) * (e₁ *
            ((2 * K₁ + 2 * b * M₁) * (4 * J 1 (k - 1) + J 1 k) +
              M₁ * (4 * J 2 (k - 1) + J 2 k))) := by ring
      _ ≤ (k : ℝ) * (e₂ *
            ((2 * K₂ + 2 * b * M₂) * (4 * J 1 (k - 1) + J 1 k) +
              M₂ * (4 * J 2 (k - 1) + J 2 k))) :=
        mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg k)
      _ = (k : ℝ) * e₂ *
          ((2 * K₂ + 2 * b * M₂) * (4 * J 1 (k - 1) + J 1 k) +
            M₂ * (4 * J 2 (k - 1) + J 2 k)) := by ring
  have hbracket :
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e₁ * S₁ * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * J 1 (k - 1) + J 1 k) +
            4 * J 2 (k - 1) + J 2 k)
       else 0) ≤
      (if 2 ≤ k then
        2 * (k : ℝ) * ((k : ℝ) - 1) * e₂ * S₂ * (1 + θ⁻¹) *
          (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * J 1 (k - 1) + J 1 k) +
            4 * J 2 (k - 1) + J 2 k)
       else 0) := by
    by_cases hk : 2 ≤ k
    · simp [hk]
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (show 1 ≤ k by omega)
      have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.le
      have hfactor : 0 ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) * (1 + θ⁻¹) := by
        positivity
      have hES : e₁ * S₁ ≤ e₂ * S₂ := by
        calc
          e₁ * S₁ ≤ e₂ * S₁ := mul_le_mul_of_nonneg_right he hS₁
          _ ≤ e₂ * S₂ := mul_le_mul_of_nonneg_left hS he₂
      have hcoeff :
          2 * (k : ℝ) * ((k : ℝ) - 1) * e₁ * S₁ * (1 + θ⁻¹) ≤
            2 * (k : ℝ) * ((k : ℝ) - 1) * e₂ * S₂ * (1 + θ⁻¹) := by
        calc
          2 * (k : ℝ) * ((k : ℝ) - 1) * e₁ * S₁ * (1 + θ⁻¹) =
              (2 * (k : ℝ) * ((k : ℝ) - 1) * (1 + θ⁻¹)) * (e₁ * S₁) := by ring
          _ ≤ (2 * (k : ℝ) * ((k : ℝ) - 1) * (1 + θ⁻¹)) * (e₂ * S₂) :=
            mul_le_mul_of_nonneg_left hES hfactor
          _ = 2 * (k : ℝ) * ((k : ℝ) - 1) * e₂ * S₂ * (1 + θ⁻¹) := by ring
      have hJ11lo : 0 ≤ J 1 (k - 1) := hJ 1 (k - 1)
      have hJ11hi : 0 ≤ J 1 k := hJ 1 k
      have hJ21lo : 0 ≤ J 2 (k - 1) := hJ 2 (k - 1)
      have hJ21hi : 0 ≤ J 2 k := hJ 2 k
      have hinner : 0 ≤
          b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
            2 * b * (4 * J 1 (k - 1) + J 1 k) +
            4 * J 2 (k - 1) + J 2 k := by positivity
      exact mul_le_mul_of_nonneg_right hcoeff hinner
    · simp [hk]
  change
      (k : ℝ) * e₁ *
          ((2 * K₁ + 2 * b * M₁) * (4 * J 1 (k - 1) + J 1 k) +
            M₁ * (4 * J 2 (k - 1) + J 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e₁ * S₁ * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * J 1 (k - 1) + J 1 k) +
              4 * J 2 (k - 1) + J 2 k)
         else 0) ≤
      (k : ℝ) * e₂ *
          ((2 * K₂ + 2 * b * M₂) * (4 * J 1 (k - 1) + J 1 k) +
            M₂ * (4 * J 2 (k - 1) + J 2 k)) +
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e₂ * S₂ * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
              2 * b * (4 * J 1 (k - 1) + J 1 k) +
              4 * J 2 (k - 1) + J 2 k)
         else 0)
  exact add_le_add hbase hbracket

end ASDExplicitGamma.Native
