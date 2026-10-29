module

public import ASDExplicitGamma.Triadic.TriadicDualNorms
import Homogenization.Besov.Duality.ProjectionLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact dimension-two constants for the weak/positive triadic estimates. -/

@[expose] public section

open Homogenization MeasureTheory

namespace ASDExplicitGamma.Triadic

variable {d : ℕ}

/-- The order-`1/4` weak Poincaré constant from the exact triadic series. -/
noncomputable def planarC0 : ℝ :=
  Real.sqrt (8 * Real.sqrt 3 / ((9 - Real.sqrt 3) * Real.pi ^ 2))

/-- The order-`1/4` positive Poincaré constant from the exact triadic series. -/
noncomputable def planarC1 : ℝ :=
  Real.sqrt ((Real.sqrt 3 - 1) / (Real.pi ^ 2 * (1 - Real.sqrt 3 / 9)))

/-- The planar Dirichlet Poincaré constant. -/
noncomputable def planarCD : ℝ :=
  Real.sqrt (planarC1 ^ 2 + 1 / (2 * Real.pi ^ 2))

/-- The sharp planar positive-norm Poincaré constant. -/
noncomputable def planarFD : ℝ := Real.sqrt (7 / 2) / Real.pi

/-- The exact forced-source coefficient, written with nested square roots. -/
noncomputable def forcedSourceD : ℝ :=
  1 / 2 + (Real.sqrt (Real.sqrt 3))⁻¹

theorem planarC0_sq :
    planarC0 ^ 2 = 8 * Real.sqrt 3 / ((9 - Real.sqrt 3) * Real.pi ^ 2) := by
  have hs3 : 0 ≤ (3 : ℝ) := by norm_num
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt hs3
  have hs3lt : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hden : 0 < (9 - Real.sqrt 3) * Real.pi ^ 2 := by
    apply mul_pos
    · linarith
    · exact pow_pos Real.pi_pos _
  have hrad : 0 ≤ 8 * Real.sqrt 3 / ((9 - Real.sqrt 3) * Real.pi ^ 2) := by
    exact div_nonneg (by positivity) hden.le
  unfold planarC0
  rw [Real.sq_sqrt hrad]

theorem planarC1_sq :
    planarC1 ^ 2 = (Real.sqrt 3 - 1) / (Real.pi ^ 2 * (1 - Real.sqrt 3 / 9)) := by
  have hs3 : 0 ≤ (3 : ℝ) := by norm_num
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt hs3
  have hs3gt : 1 < Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hs3lt : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hnum : 0 < Real.sqrt 3 - 1 := by linarith
  have hden : 0 < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) := by
    apply mul_pos
    · exact pow_pos Real.pi_pos _
    · have hfac : 0 < 1 - Real.sqrt 3 / 9 := by nlinarith [hs3lt]
      exact hfac
  have hrad : 0 ≤ (Real.sqrt 3 - 1) / (Real.pi ^ 2 * (1 - Real.sqrt 3 / 9)) :=
    (div_nonneg hnum.le hden.le)
  unfold planarC1
  rw [Real.sq_sqrt hrad]

theorem planarC0_sq_eq_planarC1_sq_add :
    planarC0 ^ 2 = planarC1 ^ 2 + 1 / Real.pi ^ 2 := by
  rw [planarC0_sq, planarC1_sq]
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hden : 9 - Real.sqrt 3 ≠ 0 := by
    have hlt : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ), hs3]
    linarith
  field_simp [Real.pi_ne_zero, hden]
  nlinarith [hs3]

theorem planarC0_exact_identity :
    planarC0 ^ 2 * (1 + 3 * (Real.sqrt 3 - 1) / 2) = 4 / Real.pi ^ 2 := by
  rw [planarC0_sq]
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hden : 9 - Real.sqrt 3 ≠ 0 := by
    have hlt : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ), hs3]
    linarith
  field_simp [Real.pi_ne_zero, hden]
  nlinarith [hs3]

theorem planarCD_sq : planarCD ^ 2 = planarC1 ^ 2 + 1 / (2 * Real.pi ^ 2) := by
  have hrad : 0 ≤ planarC1 ^ 2 + 1 / (2 * Real.pi ^ 2) := by positivity
  unfold planarCD
  rw [Real.sq_sqrt hrad]

theorem planarFD_exact : planarFD = Real.sqrt (7 / 2) / Real.pi := rfl

theorem forcedSourceD_exact :
    forcedSourceD = 1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hroot : Real.sqrt (Real.sqrt 3) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    calc
      ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
          (3 : ℝ) ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
      _ = (3 : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  unfold forcedSourceD
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), hroot]

theorem forcedSourceD_lt_126_over_100 : forcedSourceD < 126 / 100 := by
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsmall : (25 / 19 : ℝ) ^ 4 < 3 := by norm_num
  have hroot2 : (25 / 19 : ℝ) ^ 2 < Real.sqrt 3 := by
    apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg (3 : ℝ))).1
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hrootroot : (25 / 19 : ℝ) < Real.sqrt (Real.sqrt 3) := by
    apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg (Real.sqrt 3))).1
    rw [Real.sq_sqrt (Real.sqrt_nonneg (3 : ℝ))]
    exact hroot2
  have hinv : (Real.sqrt (Real.sqrt 3))⁻¹ < 19 / 25 := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 25 / 19) hrootroot
    norm_num at h ⊢
    exact h
  unfold forcedSourceD
  calc
    1 / 2 + (Real.sqrt (Real.sqrt 3))⁻¹ < 1 / 2 + 19 / 25 := by nlinarith [hinv]
    _ = 126 / 100 := by norm_num

/-- The positive Besov norm `P(F)` at exponent `1/4`, including the root mean. -/
noncomputable def positiveHaarNorm (Q : TriadicCube d) (F : Vec d → ℝ) : ℝ :=
  Real.sqrt (primalEnergy Q (Real.sqrt 3) F)

/-- The weak Besov norm `K(F)` at exponent `1/4`, including the root mean. -/
noncomputable def weakHaarNorm (Q : TriadicCube d) (F : Vec d → ℝ) : ℝ :=
  Real.sqrt (dualEnergy Q (Real.sqrt 3) F)

/-- Weak/positive pairing duality at exponent `1/4`; the positive series is an explicit domain condition. -/
theorem weak_positive_pairing_le (Q : TriadicCube d) {F G : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hFpos : Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) F))) :
    |pairing Q F G| ≤ positiveHaarNorm Q F * weakHaarNorm Q G := by
  have hsqrt : 1 < Real.sqrt 3 := by
    have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hconj : Homogenization.cubeBesovConjExponent (2 : ENNReal) = 2 := by
    simpa [Homogenization.cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ENNReal)) (q := (2 : ENNReal)))
  have hconjTop : Homogenization.cubeBesovConjExponent (2 : ENNReal) ≠ (⊤ : ENNReal) := by
    rw [hconj]
    norm_num
  have hconv := Homogenization.tendsto_cubeBesovPairing_projection_left_of_memLp
    Q (2 : ENNReal) G F hG (by simpa only [hconj] using hF)
      (by norm_num) (by norm_num) hconjTop
  have hpairconv : Filter.Tendsto
      (fun n => pairing Q (cubeProjection Q (n + 1) G) (cubeProjection Q (n + 1) F))
      Filter.atTop (nhds (pairing Q G F)) := by
    have hconv' : Filter.Tendsto
        (fun n => pairing Q (cubeProjection Q (n + 1) G) F)
        Filter.atTop (nhds (pairing Q G F)) := by
      simpa only [Homogenization.cubeBesovPairing, pairing] using hconv
    have heq : ∀ n,
        pairing Q (cubeProjection Q (n + 1) G) (cubeProjection Q (n + 1) F) =
          pairing Q (cubeProjection Q (n + 1) G) F := by
      intro n
      calc
        pairing Q (cubeProjection Q (n + 1) G) (cubeProjection Q (n + 1) F) =
            pairing Q G (cubeProjection Q (n + 1) F) := by
          simpa only [Nat.min_self] using
            (pairing_projections Q (n + 1) (n + 1) hG hF)
        _ = pairing Q (cubeProjection Q (n + 1) G) F :=
          (projection_selfAdjoint Q (n + 1) hG hF).symm
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => (heq n).symm) hconv'
  have hpairconv' : Filter.Tendsto
      (fun N => pairing Q (cubeProjection Q N G) (cubeProjection Q N F))
      Filter.atTop (nhds (pairing Q G F)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).1 hpairconv
  have h := abs_pairing_le_dual_primal_of_pairing_limit Q hsqrt hG hF hFpos hpairconv'
  have h' : |pairing Q G F| ≤ weakHaarNorm Q G * positiveHaarNorm Q F := by
    simpa only [weakHaarNorm, positiveHaarNorm] using h
  calc
    |pairing Q F G| = |pairing Q G F| := by rw [pairing_comm]
    _ ≤ weakHaarNorm Q G * positiveHaarNorm Q F := h'
    _ = positiveHaarNorm Q F * weakHaarNorm Q G := by ring

end ASDExplicitGamma.Triadic
