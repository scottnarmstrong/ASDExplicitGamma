module

public import ASDExplicitGamma.Main.FlatFieldCellGeometry

/-! The scalar algebra in the stationary affine estimate, separated from its
source-specific construction of the local comparison matrices. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-! `p` and `q` are the two scalar excess means, `T` is the expected trace
excess, and `trD` is the expected inverse-block trace. The hypotheses below
are the source identities used by the stationary-affine reduction. -/
theorem main_affine_scalar_reduction
    (v Bflat B0 beta a T trD p q x2 y2 X Y deltaPlus deltaMinus Aff A2 : ℝ)
    (hB : 0 ≤ Bflat) (hB0 : Bflat ≤ B0)
    (hBcap : B0 ≤ 2 * v) (hbeta : 1 ≤ beta) (ha : 0 ≤ a)
    (hTle : T ≤ a)
    (htrD : trD ≤ 2 * beta)
    (hp : -1 ≤ p) (hq : -1 ≤ q)
    (hT : T = 2 * (p + q)) (htr : trD = 2 + 2 * q)
    (hxsum : x2 + y2 = 2 * v) (hxdiff : x2 - y2 = Bflat)
    (hX : X = x2 - deltaPlus) (hY : Y = y2 - deltaMinus)
    (hdeltaPlus : 0 ≤ deltaPlus) (hdeltaMinus : 0 ≤ deltaMinus)
    (hAff : Aff = q * X + p * Y)
    (hdelta : deltaPlus + deltaMinus ≤
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * A2 / 9) :
    Aff ≤ (v / 2) * a + B0 * (beta - 1) +
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * A2 / 9 := by
  have hx2 : x2 = v + Bflat / 2 := by linarith [hxsum, hxdiff]
  have hy2 : y2 = v - Bflat / 2 := by linarith [hxsum, hxdiff]
  have htr' : trD - 2 = 2 * q := by linarith [htr]
  have hscalar : q * x2 + p * y2 =
      (v / 2 - Bflat / 4) * T + (Bflat / 2) * (trD - 2) := by
    rw [hx2, hy2, hT, htr']
    ring
  have hcoef : 0 ≤ v / 2 - Bflat / 4 := by linarith [hBcap]
  have hcoef_le : v / 2 - Bflat / 4 ≤ v / 2 := by linarith [hB]
  have hBtr : (Bflat / 2) * (trD - 2) ≤ Bflat * (beta - 1) := by
    have htrle : trD - 2 ≤ 2 * (beta - 1) := by linarith [htrD]
    have hmul := mul_le_mul_of_nonneg_left htrle (show 0 ≤ Bflat / 2 by positivity)
    nlinarith
  have hBreplace : Bflat * (beta - 1) ≤ B0 * (beta - 1) :=
    mul_le_mul_of_nonneg_right hB0 (by linarith [hbeta])
  have hdeltaAff : q * X + p * Y ≤ q * x2 + p * y2 + deltaPlus + deltaMinus := by
    rw [hX, hY]
    have hqp : 0 ≤ q + 1 := by linarith [hq]
    have hpp : 0 ≤ p + 1 := by linarith [hp]
    have hqmul := mul_nonneg hqp hdeltaPlus
    have hpmul := mul_nonneg hpp hdeltaMinus
    nlinarith
  calc
    Aff = q * X + p * Y := hAff
    _ ≤ q * x2 + p * y2 + deltaPlus + deltaMinus := hdeltaAff
    _ = (v / 2 - Bflat / 4) * T +
          (Bflat / 2) * (trD - 2) + deltaPlus + deltaMinus := by rw [hscalar]
    _ ≤ (v / 2) * a + B0 * (beta - 1) +
          (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * A2 / 9 := by
      have hfirst : (v / 2 - Bflat / 4) * T ≤ (v / 2) * a := by
        calc
          _ ≤ (v / 2 - Bflat / 4) * a :=
            mul_le_mul_of_nonneg_left hTle hcoef
          _ ≤ (v / 2) * a := mul_le_mul_of_nonneg_right hcoef_le ha
      nlinarith [hBtr, hBreplace, hdelta]

end ASDExplicitGamma.Main

end
