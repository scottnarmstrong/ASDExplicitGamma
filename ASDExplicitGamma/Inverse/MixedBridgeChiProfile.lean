module

public import ASDExplicitGamma.Main.EnvelopeHProfileArithmetic
public import ASDExplicitGamma.Main.EnvelopeSigns

/-! Exact weighted geometric profile for the local OLD-slope comparison. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Main
open scoped BigOperators

noncomputable section

/-- A single `mainW` coefficient at local depth `j`, with its source weight. -/
def mixedBridgeChiProfileW (gamma growth : ℝ) (degree j : ℕ) : ℝ :=
  (1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
    (3 : ℝ) ^ ((growth * gamma - degree) * (j : ℝ))

/-- The affine raw-profile coefficient at local depth `j`. -/
def mixedBridgeChiProfileRawW (gamma growth : ℝ) (degree j : ℕ) : ℝ :=
  mixedBridgeChiProfileW gamma growth degree j *
    (mainRawA gamma + mainRawS gamma * (j : ℝ))

/-- The exact depthwise coefficient row that sums to `mainChi`. -/
def mixedBridgeChiProfileDepth (v gamma : ℝ) (j : ℕ) : ℝ :=
  (∑ i : Fin 3, mainXiCoefficients v i *
    ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma *
        mixedBridgeChiProfileRawW gamma 10 (i.val + 2) j +
      52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
        mixedBridgeChiProfileW gamma 8 (i.val + 2) j)) +
  2 * mainKf v *
    ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
        mixedBridgeChiProfileRawW gamma 8 2 j +
      52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
        mixedBridgeChiProfileW gamma 6 2 j) +
  2 * v * mainBetaOld ^ 2 * mixedBridgeChiProfileW gamma 4 0 j +
  2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
    ((1 - mainAlpha ^ 2) *
      (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j)

private theorem mixedBridgeChiProfileW_eq_geom
    (gamma growth : ℝ) (degree j : ℕ) :
    mixedBridgeChiProfileW gamma growth degree j =
      (1 - mainAlpha ^ 2) *
        (mainAlpha ^ 2 * (3 : ℝ) ^ (growth * gamma - degree)) ^ j := by
  unfold mixedBridgeChiProfileW
  have hα : mainAlpha ^ (2 * j) = (mainAlpha ^ 2) ^ j := by
    rw [← pow_mul]
  have h3 : (3 : ℝ) ^ ((growth * gamma - degree) * (j : ℝ)) =
      ((3 : ℝ) ^ (growth * gamma - degree)) ^ j := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hα, h3]
  calc
    (1 - mainAlpha ^ 2) * (mainAlpha ^ 2) ^ j *
        ((3 : ℝ) ^ (growth * gamma - degree)) ^ j =
      (1 - mainAlpha ^ 2) *
        ((mainAlpha ^ 2) ^ j * ((3 : ℝ) ^ (growth * gamma - degree)) ^ j) := by ring
    _ = (1 - mainAlpha ^ 2) *
        (mainAlpha ^ 2 * (3 : ℝ) ^ (growth * gamma - degree)) ^ j := by
          rw [← mul_pow]

private theorem mixedBridgeChiProfileRawW_eq_geom
    (gamma growth : ℝ) (degree j : ℕ) :
    mixedBridgeChiProfileRawW gamma growth degree j =
      (1 - mainAlpha ^ 2) *
        ((mainRawA gamma + mainRawS gamma * (j : ℝ)) *
          (mainAlpha ^ 2 * (3 : ℝ) ^ (growth * gamma - degree)) ^ j) := by
  rw [mixedBridgeChiProfileRawW, mixedBridgeChiProfileW_eq_geom]
  ring

private theorem mixedBridgeChiProfileRawW_hasSum
    (gamma growth : ℝ) (degree : ℕ) (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ gammaZero) (hgrowth : growth ≤ 10) :
    Summable (fun j : ℕ => mixedBridgeChiProfileRawW gamma growth degree j) ∧
      (∑' j : ℕ, mixedBridgeChiProfileRawW gamma growth degree j) =
        mainRawW gamma growth degree := by
  let q : ℝ := mainAlpha ^ 2 * (3 : ℝ) ^ (growth * gamma - degree)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have hq1 : q < 1 := by
    dsimp [q]
    apply main_weak_ratio_lt_one gamma (growth * gamma - degree) hg
    have hmul := mul_le_mul_of_nonneg_right hgrowth hg0
    have hdegree : (0 : ℝ) ≤ (degree : ℝ) := Nat.cast_nonneg _
    linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact hq1
  have hG := hasSum_geometric_of_norm_lt_one hqnorm
  have hJ := hasSum_coe_mul_geometric_of_norm_lt_one hqnorm
  have hseries : Summable (fun j : ℕ =>
      (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j) := by
    have hsplit : (fun j : ℕ =>
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j) =
        fun j : ℕ => mainRawA gamma * q ^ j +
          mainRawS gamma * ((j : ℝ) * q ^ j) := by
      funext j
      ring
    rw [hsplit]
    exact (hG.summable.mul_left _).add (hJ.summable.mul_left _)
  have hdepth (j : ℕ) :
      mixedBridgeChiProfileRawW gamma growth degree j =
        (1 - mainAlpha ^ 2) *
          ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j) := by
    rw [mixedBridgeChiProfileRawW_eq_geom]
  have hmain := mainRawGeo_eq_depth_tsum_of_norm_lt_one gamma q hqnorm
  refine ⟨hseries.mul_left (1 - mainAlpha ^ 2) |>.congr ?_, ?_⟩
  · intro j
    exact (hdepth j).symm
  · calc
      (∑' j : ℕ, mixedBridgeChiProfileRawW gamma growth degree j) =
          (1 - mainAlpha ^ 2) *
            ∑' j : ℕ, (mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j := by
              rw [show (fun j : ℕ => mixedBridgeChiProfileRawW gamma growth degree j) =
                fun j : ℕ => (1 - mainAlpha ^ 2) *
                  ((mainRawA gamma + mainRawS gamma * (j : ℝ)) * q ^ j) from
                funext (fun j => hdepth j)]
              rw [tsum_mul_left]
      _ = (1 - mainAlpha ^ 2) * mainRawGeo gamma q := by rw [hmain.symm]
      _ = mainRawW gamma growth degree := by rfl

private theorem mixedBridgeChiProfileW_hasSum
    (gamma growth : ℝ) (degree : ℕ) (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ gammaZero) (hgrowth : growth ≤ 10) :
    Summable (fun j : ℕ => mixedBridgeChiProfileW gamma growth degree j) ∧
      (∑' j : ℕ, mixedBridgeChiProfileW gamma growth degree j) =
        mainW gamma growth degree := by
  let q : ℝ := mainAlpha ^ 2 * (3 : ℝ) ^ (growth * gamma - degree)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have hq1 : q < 1 := by
    dsimp [q]
    apply main_weak_ratio_lt_one gamma (growth * gamma - degree) hg
    have hmul := mul_le_mul_of_nonneg_right hgrowth hg0
    have hdegree : (0 : ℝ) ≤ (degree : ℝ) := Nat.cast_nonneg _
    linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact hq1
  have hgeom := hasSum_geometric_of_norm_lt_one hqnorm
  have hdepth (j : ℕ) :
      mixedBridgeChiProfileW gamma growth degree j =
        (1 - mainAlpha ^ 2) * q ^ j := by
    rw [mixedBridgeChiProfileW_eq_geom]
  refine ⟨hgeom.summable.mul_left (1 - mainAlpha ^ 2) |>.congr ?_, ?_⟩
  · intro j
    exact (hdepth j).symm
  · calc
      (∑' j : ℕ, mixedBridgeChiProfileW gamma growth degree j) =
          (1 - mainAlpha ^ 2) * ∑' j : ℕ, q ^ j := by
            rw [show (fun j : ℕ => mixedBridgeChiProfileW gamma growth degree j) =
              fun j => (1 - mainAlpha ^ 2) * q ^ j from
              funext (fun j => hdepth j)]
            rw [tsum_mul_left]
      _ = (1 - mainAlpha ^ 2) * mainGeo q := by
        rw [(mainGeo_eq_depth_tsum_of_norm_lt_one q hqnorm).symm]
      _ = mainW gamma growth degree := by
        dsimp [q, mainGeo, mainW]
        rw [div_eq_mul_inv]

private theorem mixedBridgeChiProfileRare_hasSum
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    Summable (fun j : ℕ =>
      (1 - mainAlpha ^ 2) *
        (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j) ∧
      (∑' j : ℕ, (1 - mainAlpha ^ 2) *
        (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j) =
        (1 - mainAlpha ^ 2) /
          (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) := by
  let q : ℝ := mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have hq1 : q < 1 := by
    dsimp [q]
    apply main_weak_ratio_lt_one gamma (4 * gamma + 1 / 64) hg
    nlinarith [hg0]
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact hq1
  have hgeom := hasSum_geometric_of_norm_lt_one hqnorm
  refine ⟨hgeom.summable.mul_left (1 - mainAlpha ^ 2), ?_⟩
  calc
    (∑' j : ℕ, (1 - mainAlpha ^ 2) * q ^ j) =
        (1 - mainAlpha ^ 2) * ∑' j : ℕ, q ^ j := by rw [tsum_mul_left]
    _ = (1 - mainAlpha ^ 2) * mainGeo q := by
      rw [(mainGeo_eq_depth_tsum_of_norm_lt_one q hqnorm).symm]
    _ = (1 - mainAlpha ^ 2) /
        (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) := by
      dsimp [q, mainGeo]
      rw [div_eq_mul_inv]
      rfl

/-- The exact `mainChi` coefficient is the sum of its local weighted rows. -/
theorem mixed_bridge_local_chi_profile_tsum
    (v gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    Summable (fun j : ℕ => mixedBridgeChiProfileDepth v gamma j) ∧
      (∑' j : ℕ, mixedBridgeChiProfileDepth v gamma j) = mainChi v gamma := by
  classical
  let modal : ℕ → ℝ := fun j =>
    ∑ i : Fin 3, mainXiCoefficients v i *
      ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma *
          mixedBridgeChiProfileRawW gamma 10 (i.val + 2) j +
        52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
          mixedBridgeChiProfileW gamma 8 (i.val + 2) j)
  let kf : ℕ → ℝ := fun j =>
    2 * mainKf v *
      ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
          mixedBridgeChiProfileRawW gamma 8 2 j +
        52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
          mixedBridgeChiProfileW gamma 6 2 j)
  let base : ℕ → ℝ := fun j =>
    2 * v * mainBetaOld ^ 2 * mixedBridgeChiProfileW gamma 4 0 j
  let rare : ℕ → ℝ := fun j =>
    2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
      ((1 - mainAlpha ^ 2) *
        (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j)
  have hraw (growth : ℝ) (degree : ℕ) (hgrowth : growth ≤ 10) :=
    mixedBridgeChiProfileRawW_hasSum gamma growth degree hg0 hg hgrowth
  have hplain (growth : ℝ) (degree : ℕ) (hgrowth : growth ≤ 10) :=
    mixedBridgeChiProfileW_hasSum gamma growth degree hg0 hg hgrowth
  have hmodalTerm (i : Fin 3) : Summable (fun j : ℕ =>
      mainXiCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma *
            mixedBridgeChiProfileRawW gamma 10 (i.val + 2) j +
          52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
            mixedBridgeChiProfileW gamma 8 (i.val + 2) j)) := by
    have hr := (hraw 10 (i.val + 2) (by norm_num)).1.mul_left
      (mainXiCoefficients v i * ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma))
    have hp := (hplain 8 (i.val + 2) (by norm_num)).1.mul_left
      (mainXiCoefficients v i * (52 * v * Real.sqrt 3 * mainBetaOld ^ 4))
    exact (hr.add hp).congr (by intro j; ring)
  have hmodal : Summable modal := by
    dsimp [modal]
    exact summable_sum (s := Finset.univ) (fun i _ => hmodalTerm i)
  have hkf : Summable kf := by
    dsimp [kf]
    have hr := (hraw 8 2 (by norm_num)).1.mul_left
      (2 * mainKf v * ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma))
    have hp := (hplain 6 2 (by norm_num)).1.mul_left
      (2 * mainKf v * (52 * v * Real.sqrt 3 * mainBetaOld ^ 3))
    exact (hr.add hp).congr (by intro j; ring)
  have hbase : Summable base := by
    dsimp [base]
    exact (hplain 4 0 (by norm_num)).1.mul_left (2 * v * mainBetaOld ^ 2)
  have hraresum := mixedBridgeChiProfileRare_hasSum gamma hg0 hg
  have hrare : Summable rare := by
    dsimp [rare]
    exact hraresum.1.mul_left (2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld)
  have hprofile : Summable (fun j : ℕ => mixedBridgeChiProfileDepth v gamma j) := by
    have heq : (fun j : ℕ => mixedBridgeChiProfileDepth v gamma j) =
        fun j => modal j + kf j + base j + rare j := by
      funext j
      rfl
    rw [heq]
    exact ((hmodal.add hkf).add hbase).add hrare
  have hmodalSum : (∑' j : ℕ, modal j) =
      ∑ i : Fin 3, mainXiCoefficients v i *
        ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma *
            mainRawW gamma 10 (i.val + 2) +
          52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
            mainW gamma 8 (i.val + 2)) := by
    dsimp [modal]
    rw [Summable.tsum_finsetSum (fun i _ => hmodalTerm i)]
    apply Finset.sum_congr rfl
    intro i hi
    have hr := (hraw 10 (i.val + 2) (by norm_num)).1.mul_left
      (mainXiCoefficients v i * ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma))
    have hp := (hplain 8 (i.val + 2) (by norm_num)).1.mul_left
      (mainXiCoefficients v i * (52 * v * Real.sqrt 3 * mainBetaOld ^ 4))
    calc
      _ = ∑' j : ℕ, (
          (mainXiCoefficients v i * ((26 / 25) * mainBetaOld ^ 3 *
              mainRawFactor gamma) * mixedBridgeChiProfileRawW gamma 10 (i.val + 2) j) +
            (mainXiCoefficients v i * (52 * v * Real.sqrt 3 * mainBetaOld ^ 4) *
              mixedBridgeChiProfileW gamma 8 (i.val + 2) j)) := by
          apply tsum_congr
          intro j
          ring
      _ = _ := by
          rw [hr.tsum_add hp, tsum_mul_left, tsum_mul_left,
            (hraw 10 (i.val + 2) (by norm_num)).2,
            (hplain 8 (i.val + 2) (by norm_num)).2]
          ring
  have hkfSum : (∑' j : ℕ, kf j) =
      2 * mainKf v *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma * mainRawW gamma 8 2 +
          52 * v * Real.sqrt 3 * mainBetaOld ^ 3 * mainW gamma 6 2) := by
    dsimp [kf]
    have hr := (hraw 8 2 (by norm_num)).1.mul_left
      (2 * mainKf v * ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma))
    have hp := (hplain 6 2 (by norm_num)).1.mul_left
      (2 * mainKf v * (52 * v * Real.sqrt 3 * mainBetaOld ^ 3))
    calc
      _ = ∑' j : ℕ, (
          (2 * mainKf v * ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma) *
              mixedBridgeChiProfileRawW gamma 8 2 j) +
            (2 * mainKf v * (52 * v * Real.sqrt 3 * mainBetaOld ^ 3) *
              mixedBridgeChiProfileW gamma 6 2 j)) := by
          apply tsum_congr
          intro j
          ring
      _ = _ := by
          rw [hr.tsum_add hp, tsum_mul_left, tsum_mul_left,
            (hraw 8 2 (by norm_num)).2, (hplain 6 2 (by norm_num)).2]
          ring
  have hbaseSum : (∑' j : ℕ, base j) =
      2 * v * mainBetaOld ^ 2 * mainW gamma 4 0 := by
    dsimp [base]
    rw [tsum_mul_left, (hplain 4 0 (by norm_num)).2]
  have hrareSum : (∑' j : ℕ, rare j) =
      2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
        ((1 - mainAlpha ^ 2) /
          (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64))) := by
    dsimp [rare]
    rw [tsum_mul_left, hraresum.2]
  have hsum : (∑' j : ℕ, mixedBridgeChiProfileDepth v gamma j) =
      mainChi v gamma := by
    calc
      _ = (∑' j : ℕ, modal j) + (∑' j : ℕ, kf j) +
          (∑' j : ℕ, base j) + (∑' j : ℕ, rare j) := by
            rw [show (fun j : ℕ => mixedBridgeChiProfileDepth v gamma j) =
              fun j => modal j + kf j + base j + rare j from funext (fun j => rfl)]
            rw [((hmodal.add hkf).add hbase).tsum_add hrare,
              (hmodal.add hkf).tsum_add hbase, hmodal.tsum_add hkf]
      _ = mainChi v gamma := by
        rw [hmodalSum, hkfSum, hbaseSum, hrareSum]
        unfold mainChi
        ring
  exact ⟨hprofile, hsum⟩

end
end ASDExplicitGamma.Inverse
