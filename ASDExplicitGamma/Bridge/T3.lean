module

public import ASDExplicitGamma.Statements.AllOrderBounds
public import ASDExplicitGamma.Statements.ShellVarianceSum
public import ASDExplicitGamma.Model.Cstar
public import ASDExplicitGamma.Numerics.Joint.BridgeRatio

/-! The explicit T1 corridor and all-order estimates imply the frozen T3 state. -/

@[expose] public section

namespace ASDExplicitGamma.Bridge

open Algsuperdiff.Section3
open Homogenization IndependentSums MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The pointwise source T1 corridor and same-label all-order bounds imply the
frozen T3 induction state with constant `2^16`. -/
theorem br_t3_induction_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000) (m0 : ℤ)
    (hT1 : ∀ m : ℤ, m ≤ m0 →
      M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma m + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2 ≤
        M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma m ∧
      AllOrderBounds M m) :
    Algsuperdiff.Frozen.Section3.inductionState M m0 ⟨2 ^ 16, by norm_num⟩ := by
  have hγpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hhpos : 0 < h := hM.1
  have hlog : Real.log (3 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hden : 1 - (3 : ℝ) ^ (-(2 * M.gamma)) ≠ 0 := by
    have hpow : (3 : ℝ) ^ (-(2 * M.gamma)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγpos])
    exact (sub_ne_zero.mpr (ne_of_gt hpow))
  have hBS (m : ℤ) :
      shellVarianceSum h M.gamma m =
        Numerics.Joint.kappa M.gamma *
          (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
    rw [Model.q3_cstar_exact M h hM]
    unfold shellVarianceSum Numerics.Joint.kappa
    field_simp [hden, hlog, hγpos.ne']
  constructor
  · intro m hm
    rcases hT1 m hm with ⟨_, hlow, hupp, _⟩
    let S : ℝ := Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
    let B : ℝ := shellVarianceSum h M.gamma m
    have hSpos : 0 < S := by
      dsimp [S]
      rw [Model.q3_cstar_exact M h hM]
      positivity
    have hSnonneg : 0 ≤ S := hSpos.le
    have hB_eq : B = Numerics.Joint.kappa M.gamma * S := by
      exact hBS m
    have hκ := Numerics.Joint.bridge_ratio_bounds M.gamma hγpos hγ
    rcases hκ with ⟨hκlo, _, hκ31, hκ19, hκ21, hκ4⟩
    have hκnonneg : 0 ≤ Numerics.Joint.kappa M.gamma := by linarith only [hκlo]
    have hνsq : 0 ≤ M.nu ^ 2 := sq_nonneg _
    have hBnonneg : 0 ≤ B := by
      rw [hB_eq]
      exact mul_nonneg hκnonneg hSnonneg
    have hmaxnonneg : 0 ≤ max S (M.nu ^ 2) := (hSnonneg.trans (le_max_left _ _))
    have hlowBridge :
        (1 / 4 : ℝ) * max S (M.nu ^ 2) ≤
          (31 / 50) * B + (19 / 50) * M.nu ^ 2 := by
      rw [mul_max_of_nonneg S (M.nu ^ 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      apply max_le
      · have hcoeff : (1 / 4 : ℝ) ≤ 31 * Numerics.Joint.kappa M.gamma / 50 := le_of_lt hκ31
        have hterm := mul_le_mul_of_nonneg_right hcoeff hSnonneg
        calc
          (1 / 4 : ℝ) * S ≤ (31 * Numerics.Joint.kappa M.gamma / 50) * S := hterm
          _ = (31 / 50) * B := by rw [hB_eq]; ring
          _ ≤ (31 / 50) * B + (19 / 50) * M.nu ^ 2 :=
            le_add_of_nonneg_right (mul_nonneg (by norm_num) hνsq)
      · have hcoeff : (1 / 4 : ℝ) ≤ 19 / 50 := le_of_lt hκ19
        have hterm := mul_le_mul_of_nonneg_right hcoeff hνsq
        calc
          (1 / 4 : ℝ) * M.nu ^ 2 ≤ (19 / 50) * M.nu ^ 2 := hterm
          _ ≤ (31 / 50) * B + (19 / 50) * M.nu ^ 2 := by
            exact le_add_of_nonneg_left (mul_nonneg (by norm_num) hBnonneg)
    have hupperBridge :
        M.nu ^ 2 + (13 / 8) * B ≤ 4 * max S (M.nu ^ 2) := by
      calc
        M.nu ^ 2 + (13 / 8) * B =
            M.nu ^ 2 + ((13 / 8) * Numerics.Joint.kappa M.gamma) * S := by
              rw [hB_eq]
              ring
        _ ≤ max S (M.nu ^ 2) +
            ((13 / 8) * Numerics.Joint.kappa M.gamma) * max S (M.nu ^ 2) := by
              apply add_le_add
              · exact le_max_right _ _
              · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg (by norm_num) hκnonneg)
        _ = (1 + (13 / 8) * Numerics.Joint.kappa M.gamma) * max S (M.nu ^ 2) := by ring
        _ ≤ ((21 / 8) * Numerics.Joint.kappa M.gamma) * max S (M.nu ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ hmaxnonneg
              nlinarith only [hκlo]
        _ ≤ 4 * max S (M.nu ^ 2) :=
              mul_le_mul_of_nonneg_right (le_of_lt (hκ21.trans hκ4)) hmaxnonneg
    constructor
    · exact hlowBridge.trans hlow
    · exact hupp.trans hupperBridge
  · intro m hm s hs
    rcases hT1 m hm with ⟨_, _, _, hall⟩
    rcases hall s hs with ⟨hTwo, _⟩
    rcases hTwo with ⟨Y, Z, hW⟩
    rcases hW with ⟨hΨ₁, hΨ₂, hA₁, hA₂, hX, hY, hZ, hpoint, hTail₁, hTail₂⟩
    have hscale₁ :
        (2 ^ 16 : ℝ) * Real.sqrt M.gamma / s =
          (2 ^ 16 : ℝ) * s⁻¹ * Real.sqrt M.gamma := by ring
    have hsquare : (s⁻¹) ^ 2 = 1 / s ^ 2 := by ring
    have hspos : 0 < s := by
      have hwindow : 0 < 8 * M.gamma := mul_pos (by norm_num) hγpos
      exact hwindow.trans_le hs.1
    have hpow : ((2 ^ 16 : ℝ)⁻¹) ^ 3 = (1 / 2 ^ 48 : ℝ) := by norm_num
    have hexp : ((2 ^ 16 : ℝ)⁻¹) ^ 3 * M.gamma⁻¹ =
        (1 / 2 ^ 48 : ℝ) / M.gamma := by
      rw [hpow]
      ring
    have hscale₂ :
        Real.exp (-(Real.log 2 / (8192 * M.gamma))) ≤
          (s⁻¹) ^ 2 * Real.exp (-(((2 ^ 16 : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
      calc
        Real.exp (-(Real.log 2 / (8192 * M.gamma))) =
            Real.exp (-Real.log 2 / (8192 * M.gamma)) := by congr 1; ring
        _ ≤ 1 / s ^ 2 * Real.exp (-(1 / 2 ^ 48 : ℝ) / M.gamma) :=
          Numerics.Joint.bridge_tail_scale M.gamma s hγpos hspos hs.2
        _ = (s⁻¹) ^ 2 * Real.exp (-(((2 ^ 16 : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
          rw [hsquare, hexp]
          congr 2; ring
    have hA₂' :
        0 < (s⁻¹) ^ 2 * Real.exp (-(((2 ^ 16 : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) :=
      lt_of_lt_of_le hA₂ hscale₂
    refine ⟨Y, Z, ?_⟩
    refine ⟨hΨ₁, hΨ₂, ?_, ?_, hX, hY, hZ, hpoint, ?_, ?_⟩
    · rw [← hscale₁]
      exact hA₁
    · exact hA₂'
    · exact hTail₁.mono_scale (le_of_eq hscale₁)
    · exact hTail₂.mono_scale hscale₂

end ASDExplicitGamma.Bridge
