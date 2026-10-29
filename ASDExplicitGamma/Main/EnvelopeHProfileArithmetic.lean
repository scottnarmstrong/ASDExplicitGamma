module

public import ASDExplicitGamma.Main.EnvelopeHProfile
public import ASDExplicitGamma.Main.EnvelopeRatios
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact geometric-series assembly for the source H-profile slope. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open scoped BigOperators

noncomputable section

private theorem main_hprofile_ratio_lt_one
    (r : ℝ) (_hr0 : 0 ≤ r) (hr8 : r ≤ 8) (gamma : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (i : Fin 5) :
    mainBetaPrime * (3 : ℝ) ^ (r * gamma - i.val) < 1 := by
  have hg' : gamma ≤ 17 / 50000 := by
    simpa [gammaZero] using hg
  have hrγ : r * gamma ≤ 8 * gamma := by
    exact mul_le_mul_of_nonneg_right hr8 hg0
  have hγsmall : 8 * gamma ≤ 8 * (17 / 50000 : ℝ) := by nlinarith
  have hsmall : 8 * (17 / 50000 : ℝ) < 3 / 20 := by norm_num
  have hexp : r * gamma - (i.val : ℝ) - 3 / 20 < 0 := by
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg i.val
    linarith
  have hEq : mainBetaPrime * (3 : ℝ) ^ (r * gamma - i.val) =
      (3 : ℝ) ^ (r * gamma - (i.val : ℝ) - 3 / 20) := by
    rw [mainBetaPrime, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hEq]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp

/-- The source raw geometric profile is exactly the sum of its affine depth
coefficients. -/
theorem mainRawGeo_eq_depth_tsum_of_norm_lt_one
    (gamma q : ℝ) (hq : ‖q‖ < 1) :
    mainRawGeo gamma q =
      ∑' j : ℕ, (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j := by
  have hG := hasSum_geometric_of_norm_lt_one hq
  have hJ := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have hraw : Summable (fun j : ℕ =>
      (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j) := by
    have hpoint : (fun j : ℕ =>
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j) =
        fun j : ℕ => mainRawA gamma * q ^ j +
          mainRawS gamma * ((j : ℝ) * q ^ j) := by
      funext j
      ring
    rw [hpoint]
    exact (hG.summable.mul_left _).add (hJ.summable.mul_left _)
  calc
    mainRawGeo gamma q =
        mainRawA gamma * (∑' j : ℕ, q ^ j) +
          mainRawS gamma * (∑' j : ℕ, (j : ℝ) * q ^ j) := by
      rw [hG.tsum_eq, hJ.tsum_eq]
      unfold mainRawGeo
      ring
    _ = ∑' j : ℕ,
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j := by
      calc
        _ = (∑' j : ℕ, mainRawA gamma * q ^ j) +
              (∑' j : ℕ, mainRawS gamma * ((j : ℝ) * q ^ j)) := by
          rw [← tsum_mul_left, ← tsum_mul_left]
        _ = ∑' j : ℕ,
            (mainRawA gamma * q ^ j + mainRawS gamma * ((j : ℝ) * q ^ j)) :=
          ((hG.summable.mul_left _).tsum_add (hJ.summable.mul_left _)).symm
        _ = ∑' j : ℕ,
            (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j := by
          apply tsum_congr
          intro j
          ring

/-- The source geometric profile is exactly the unit-coefficient depth sum. -/
theorem mainGeo_eq_depth_tsum_of_norm_lt_one (q : ℝ) (hq : ‖q‖ < 1) :
    mainGeo q = ∑' j : ℕ, q ^ j := by
  unfold mainGeo
  exact (tsum_geometric_of_norm_lt_one hq).symm

/-- The old-history p=20 slope is exactly the discounted sum of its per-depth
coefficient row. -/
def mainEnvelopeHDepthGeneratorRow (v gamma : ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin 5, mainSlopeCoefficients v i *
    ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
        ((mainRawA gamma + mainRawS gamma * (j : ℝ)) *
          (mainBetaPrime * (3 : ℝ) ^ (8 * gamma - i.val)) ^ j) +
      26 * 48 * v * mainBetaOld ^ 3 *
        (mainBetaPrime * (3 : ℝ) ^ (6 * gamma - i.val)) ^ j)

/-- The explicit depth-generator row has a summable tail on the source gamma
interval. -/
theorem mainEnvelopeHDepthGeneratorRow_summable
    (v gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    Summable (mainEnvelopeHDepthGeneratorRow v gamma) := by
  let qA : Fin 5 → ℝ := fun i =>
    mainBetaPrime * (3 : ℝ) ^ (8 * gamma - i.val)
  let qB : Fin 5 → ℝ := fun i =>
    mainBetaPrime * (3 : ℝ) ^ (6 * gamma - i.val)
  have hqA (i : Fin 5) : ‖qA i‖ < 1 := by
    have hlt := main_hprofile_ratio_lt_one 8 (by norm_num) (by norm_num)
      gamma hg0 hg i
    have hnonneg : 0 ≤ qA i := by
      dsimp [qA, mainBetaPrime]
      positivity
    rw [Real.norm_of_nonneg hnonneg]
    simpa only [qA] using hlt
  have hqB (i : Fin 5) : ‖qB i‖ < 1 := by
    have hlt := main_hprofile_ratio_lt_one 6 (by norm_num) (by norm_num)
      gamma hg0 hg i
    have hnonneg : 0 ≤ qB i := by
      dsimp [qB, mainBetaPrime]
      positivity
    rw [Real.norm_of_nonneg hnonneg]
    simpa only [qB] using hlt
  have hrawSummable (i : Fin 5) : Summable (fun j : ℕ =>
      (mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) := by
    have hG := hasSum_geometric_of_norm_lt_one (hqA i)
    have hJ := hasSum_coe_mul_geometric_of_norm_lt_one (hqA i)
    have hpoint (j : ℕ) :
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j =
          mainRawA gamma * qA i ^ j + mainRawS gamma * ((j : ℝ) * qA i ^ j) := by
      ring
    have heq : (fun j : ℕ =>
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) =
        fun j : ℕ => mainRawA gamma * qA i ^ j +
          mainRawS gamma * ((j : ℝ) * qA i ^ j) := by
      funext j
      exact hpoint j
    rw [heq]
    exact (hG.summable.mul_left _).add (hJ.summable.mul_left _)
  have hgeoSummable (i : Fin 5) : Summable (fun j : ℕ => qB i ^ j) :=
    (hasSum_geometric_of_norm_lt_one (hqB i)).summable
  have hterm (i : Fin 5) : Summable (fun j : ℕ =>
      mainSlopeCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
            ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
          26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j)) := by
    have hpoint (j : ℕ) :
        mainSlopeCoefficients v i *
          ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
              ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j) =
        (mainSlopeCoefficients v i * ((26 / 25) * mainBetaOld ^ 2 *
          mainRawFactor gamma)) *
            ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
          (mainSlopeCoefficients v i * (26 * 48 * v * mainBetaOld ^ 3)) *
            qB i ^ j := by
      ring
    have heq : (fun j : ℕ =>
        mainSlopeCoefficients v i *
          ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
              ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j)) =
        fun j : ℕ =>
          (mainSlopeCoefficients v i * ((26 / 25) * mainBetaOld ^ 2 *
            mainRawFactor gamma)) *
              ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            (mainSlopeCoefficients v i * (26 * 48 * v * mainBetaOld ^ 3)) *
              qB i ^ j := by
      funext j
      exact hpoint j
    rw [heq]
    exact ((hrawSummable i).mul_left _).add ((hgeoSummable i).mul_left _)
  change Summable (fun j : ℕ =>
    ∑ i : Fin 5, mainSlopeCoefficients v i *
      ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
          ((mainRawA gamma + mainRawS gamma * (j : ℝ)) *
            (mainBetaPrime * (3 : ℝ) ^ (8 * gamma - i.val)) ^ j) +
        26 * 48 * v * mainBetaOld ^ 3 *
          (mainBetaPrime * (3 : ℝ) ^ (6 * gamma - i.val)) ^ j))
  exact summable_sum fun i (_ : i ∈ Finset.univ) => by
    simpa only [qA, qB] using hterm i

/-- Every explicit old-history depth-generator row is nonnegative. -/
theorem mainEnvelopeHDepthGeneratorRow_nonneg
    {v gamma : ℝ} (hv : 0 ≤ v) (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ gammaZero) (j : ℕ) :
    0 ≤ mainEnvelopeHDepthGeneratorRow v gamma j := by
  let qA : Fin 5 → ℝ := fun i =>
    mainBetaPrime * (3 : ℝ) ^ (8 * gamma - i.val)
  let qB : Fin 5 → ℝ := fun i =>
    mainBetaPrime * (3 : ℝ) ^ (6 * gamma - i.val)
  have hqA (i : Fin 5) : 0 ≤ qA i := by
    dsimp [qA, mainBetaPrime]
    positivity
  have hqB (i : Fin 5) : 0 ≤ qB i := by
    dsimp [qB, mainBetaPrime]
    positivity
  have hqA1 (i : Fin 5) : qA i < 1 := by
    have h := main_hprofile_ratio_lt_one 8 (by norm_num) (by norm_num)
      gamma hg0 hg i
    simpa only [qA] using h
  have hqB1 (i : Fin 5) : qB i < 1 := by
    have h := main_hprofile_ratio_lt_one 6 (by norm_num) (by norm_num)
      gamma hg0 hg i
    simpa only [qB] using h
  have hcoef (i : Fin 5) : 0 ≤ mainSlopeCoefficients v i := by
    fin_cases i <;> norm_num [mainSlopeCoefficients, mainPa, mainPb,
      mainA2, mainA4] <;> positivity
  have hrawA : 0 ≤ mainRawA gamma := mainRawA_nonneg hg0
  have hrawS : 0 ≤ mainRawS gamma := mainRawS_nonneg hg0
  have hfactor : 0 ≤ mainRawFactor gamma := by
    unfold mainRawFactor
    positivity
  have hβ : 0 ≤ mainBetaOld := by norm_num [mainBetaOld]
  unfold mainEnvelopeHDepthGeneratorRow
  apply Finset.sum_nonneg
  intro i hi
  have hinner : 0 ≤
      (26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
          ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
        26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j := by
    have hraw : 0 ≤ mainRawA gamma + mainRawS gamma * (j : ℝ) :=
      add_nonneg hrawA (mul_nonneg hrawS (Nat.cast_nonneg j))
    have hpowA : 0 ≤ qA i ^ j := pow_nonneg (hqA i) j
    have hpowB : 0 ≤ qB i ^ j := pow_nonneg (hqB i) j
    have hc₁ : 0 ≤ (26 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma := by
      positivity
    have hc₂ : 0 ≤ (26 : ℝ) * 48 * v * mainBetaOld ^ 3 := by
      positivity
    exact add_nonneg
      (mul_nonneg hc₁ (mul_nonneg hraw hpowA))
      (mul_nonneg hc₂ hpowB)
  exact mul_nonneg (hcoef i) hinner

theorem mainDeltaH_eq_depth_tsum
    (v gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    mainDeltaH v gamma = (1 - mainAlpha) *
      ∑' j : ℕ, mainEnvelopeHDepthGeneratorRow v gamma j := by
  let qA : Fin 5 → ℝ := fun i =>
    mainBetaPrime * (3 : ℝ) ^ (8 * gamma - i.val)
  let qB : Fin 5 → ℝ := fun i =>
    mainBetaPrime * (3 : ℝ) ^ (6 * gamma - i.val)
  have hqA (i : Fin 5) : ‖qA i‖ < 1 := by
    have hlt := main_hprofile_ratio_lt_one 8 (by norm_num) (by norm_num)
      gamma hg0 hg i
    have hnonneg : 0 ≤ qA i := by
      dsimp [qA, mainBetaPrime]
      positivity
    rw [Real.norm_of_nonneg hnonneg]
    simpa only [qA] using hlt
  have hqB (i : Fin 5) : ‖qB i‖ < 1 := by
    have hlt := main_hprofile_ratio_lt_one 6 (by norm_num) (by norm_num)
      gamma hg0 hg i
    have hnonneg : 0 ≤ qB i := by
      dsimp [qB, mainBetaPrime]
      positivity
    rw [Real.norm_of_nonneg hnonneg]
    simpa only [qB] using hlt
  have hrawSummable (i : Fin 5) : Summable (fun j : ℕ =>
      (mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) := by
    have hG := hasSum_geometric_of_norm_lt_one (hqA i)
    have hJ := hasSum_coe_mul_geometric_of_norm_lt_one (hqA i)
    have hpoint : (fun j : ℕ =>
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) =
        fun j : ℕ => mainRawA gamma * qA i ^ j +
          mainRawS gamma * ((j : ℝ) * qA i ^ j) := by
      funext j
      ring
    rw [hpoint]
    exact (hG.summable.mul_left _).add (hJ.summable.mul_left _)
  have hgeoSummable (i : Fin 5) : Summable (fun j : ℕ => qB i ^ j) :=
    (hasSum_geometric_of_norm_lt_one (hqB i)).summable
  have hterm (i : Fin 5) : Summable (fun j : ℕ =>
      mainSlopeCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
            ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
          26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j)) := by
    have hpoint : (fun j : ℕ =>
        mainSlopeCoefficients v i *
          ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
              ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j)) =
        fun j : ℕ =>
          (mainSlopeCoefficients v i * ((26 / 25) * mainBetaOld ^ 2 *
            mainRawFactor gamma)) *
              ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            (mainSlopeCoefficients v i * (26 * 48 * v * mainBetaOld ^ 3)) *
              qB i ^ j := by
      funext j
      ring
    rw [hpoint]
    exact ((hrawSummable i).mul_left _).add ((hgeoSummable i).mul_left _)
  have hrow : Summable (fun j : ℕ =>
      ∑ i : Fin 5, mainSlopeCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
            ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
          26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j)) :=
    summable_sum fun i _ => hterm i
  have hinner (i : Fin 5) :
      ∑' j : ℕ,
        mainSlopeCoefficients v i *
          ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
              ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j) =
      mainSlopeCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma * mainRawGeo gamma (qA i) +
          26 * 48 * v * mainBetaOld ^ 3 * mainGeo (qB i)) := by
    have hraw := mainRawGeo_eq_depth_tsum_of_norm_lt_one gamma (qA i) (hqA i)
    have hgeo := mainGeo_eq_depth_tsum_of_norm_lt_one (qB i) (hqB i)
    calc
      _ =
          (∑' j : ℕ,
            (mainSlopeCoefficients v i * ((26 / 25) * mainBetaOld ^ 2 *
              mainRawFactor gamma)) *
                ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j)) +
            ∑' j : ℕ,
              (mainSlopeCoefficients v i * (26 * 48 * v * mainBetaOld ^ 3)) *
                qB i ^ j := by
        calc
          _ = ∑' j : ℕ,
              ((mainSlopeCoefficients v i * ((26 / 25) * mainBetaOld ^ 2 *
                mainRawFactor gamma) *
                  ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
                (mainSlopeCoefficients v i * (26 * 48 * v * mainBetaOld ^ 3)) *
                  qB i ^ j)) := by
            apply tsum_congr
            intro j
            ring
          _ = _ :=
            ((hrawSummable i).mul_left _).tsum_add
              ((hgeoSummable i).mul_left _)
      _ = mainSlopeCoefficients v i *
          ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
              ∑' j : ℕ,
                (mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
            mainSlopeCoefficients v i * (26 * 48 * v * mainBetaOld ^ 3 *
              ∑' j : ℕ, qB i ^ j) := by
        rw [tsum_mul_left, tsum_mul_left]
        ring
      _ = _ := by rw [hraw, hgeo]; ring
  have hswap :
      (∑' j : ℕ, ∑ i : Fin 5, mainSlopeCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
            ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
          26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j)) =
        ∑ i : Fin 5, ∑' j : ℕ,
          mainSlopeCoefficients v i *
            ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
                ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
              26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j) := by
    exact Summable.tsum_finsetSum (fun i _ => hterm i)
  calc
    mainDeltaH v gamma = (1 - mainAlpha) *
        ∑ i : Fin 5, mainSlopeCoefficients v i *
          ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
              mainRawGeo gamma (qA i) +
            26 * 48 * v * mainBetaOld ^ 3 * mainGeo (qB i)) := by
      rfl
    _ = (1 - mainAlpha) * ∑ i : Fin 5, ∑' j : ℕ,
          mainSlopeCoefficients v i *
            ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
                ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * qA i ^ j) +
              26 * 48 * v * mainBetaOld ^ 3 * qB i ^ j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (hinner i).symm
    _ = (1 - mainAlpha) * ∑' j : ℕ, mainEnvelopeHDepthGeneratorRow v gamma j := by
      rw [← hswap]
      simp only [mainEnvelopeHDepthGeneratorRow, qA, qB]

end

end ASDExplicitGamma.Main

