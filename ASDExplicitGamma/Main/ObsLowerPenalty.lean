module

public import ASDExplicitGamma.Main.InverseLowerAlgebra

/-! Coefficient comparison for the observer-level inverse trace row, with the source coercivity
(1.2) through the history `B` (no ellipticity constant): the two-component penalty with the
uncentered mesh column/row coefficients is bounded by the explicit MA lower root. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- One actual load. `a`, `c` are the physical column/row coefficients (`a ≤ KA`, `c ≤ KB`),
`B` the cell history bound, and the joint coercivity is `Wv + Wg ≤ B E`. -/
theorem obs_penalty_le (B a c Wv Wg E KA KB : ℝ)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (ha : 0 ≤ a) (hc : 0 ≤ c) (hWv : 0 ≤ Wv) (hWg : 0 ≤ Wg)
    (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hka : a ≤ KA) (hkb : c ≤ KB)
    (hbud : Wv + Wg ≤ B * E) :
    -(2 * ((63 / 50 : ℝ) * B * a * c * Real.sqrt Wv * Real.sqrt Wg) +
        (c * Real.sqrt B * Real.sqrt Wg) ^ 2) ≥
      -(mainInverseMuMinus KA KB * (max 1 B) ^ 2 * E) := by
  set X := Real.sqrt Wv with hX
  set Y := Real.sqrt Wg with hY
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = Wv := Real.sq_sqrt hWv
  have hY2 : Y ^ 2 = Wg := Real.sq_sqrt hWg
  have hsB : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
  set Bs : ℝ := max 1 B with hBs
  have hBs1 : 1 ≤ Bs := le_max_left _ _
  have hBsB : B ≤ Bs := le_max_right _ _
  have hBB : B * B ≤ Bs ^ 2 := by nlinarith
  have hac : a * c ≤ KA * KB := mul_le_mul hka hkb hc hKA
  have hmu0 : 0 ≤ mainInverseMuMinus KA KB := by
    unfold mainInverseMuMinus; positivity
  have hquad := main_inverse_lower_quadratic KA KB Y X
  have hquad' : KB ^ 2 * Y ^ 2 + 2 * (63 / 50 : ℝ) * KA * KB * Y * X ≤
      mainInverseMuMinus KA KB * (X ^ 2 + Y ^ 2) := by
    simpa [mainInverseMuMinus, add_comm] using (neg_le_neg_iff.mp hquad)
  have hXY : 0 ≤ X * Y := mul_nonneg hX0 hY0
  have hinner : 2 * ((63 / 50 : ℝ) * a * c * X * Y) + c ^ 2 * Y ^ 2 ≤
      KB ^ 2 * Y ^ 2 + 2 * (63 / 50 : ℝ) * KA * KB * Y * X := by
    have h1 : (63 / 50 : ℝ) * a * c * (X * Y) ≤ (63 / 50 : ℝ) * (KA * KB) * (X * Y) :=
      by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hac (show (0 : ℝ) ≤ 63 / 50 by norm_num)) hXY
        calc (63 / 50 : ℝ) * a * c * (X * Y) = (63 / 50) * (a * c) * (X * Y) := by ring
          _ ≤ _ := this
    have h2 : c ^ 2 ≤ KB ^ 2 := (sq_le_sq₀ hc hKB).2 hkb
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg Y)
    nlinarith [h1, h3]
  have hlhs : 2 * ((63 / 50 : ℝ) * B * a * c * X * Y) + (c * Real.sqrt B * Y) ^ 2 =
      B * (2 * ((63 / 50 : ℝ) * a * c * X * Y) + c ^ 2 * Y ^ 2) := by
    calc _ = 2 * ((63 / 50 : ℝ) * B * a * c * X * Y) + c ^ 2 * (Real.sqrt B) ^ 2 * Y ^ 2 := by ring
      _ = _ := by rw [hsB]; ring
  have h4 : B * (2 * ((63 / 50 : ℝ) * a * c * X * Y) + c ^ 2 * Y ^ 2) ≤
      B * (mainInverseMuMinus KA KB * (X ^ 2 + Y ^ 2)) :=
    mul_le_mul_of_nonneg_left (hinner.trans hquad') hB
  have h5 : B * (mainInverseMuMinus KA KB * (X ^ 2 + Y ^ 2)) ≤
      mainInverseMuMinus KA KB * Bs ^ 2 * E := by
    have e1 : B * (mainInverseMuMinus KA KB * (X ^ 2 + Y ^ 2)) =
        mainInverseMuMinus KA KB * (B * (Wv + Wg)) := by
      rw [← hX2, ← hY2]; ring
    rw [e1]
    have e2 : B * (Wv + Wg) ≤ B * (B * E) := mul_le_mul_of_nonneg_left hbud hB
    have e3 : B * (B * E) ≤ Bs ^ 2 * E := by
      have := mul_le_mul_of_nonneg_right hBB hE
      nlinarith [this]
    calc mainInverseMuMinus KA KB * (B * (Wv + Wg))
        ≤ mainInverseMuMinus KA KB * (Bs ^ 2 * E) :=
          mul_le_mul_of_nonneg_left (e2.trans e3) hmu0
      _ = _ := by ring
  have hfin : 2 * ((63 / 50 : ℝ) * B * a * c * X * Y) + (c * Real.sqrt B * Y) ^ 2 ≤
      mainInverseMuMinus KA KB * Bs ^ 2 * E := by
    rw [hlhs]; exact h4.trans h5
  exact neg_le_neg hfin

end ASDExplicitGamma.Main
