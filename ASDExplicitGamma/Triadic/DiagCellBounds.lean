module

public import ASDExplicitGamma.Triadic.PlanarNeumannBridge

/-! Sharp mean-zero cell bounds needed by the DIAG residual estimate.
The cell residual has mean zero; it need not have zero boundary trace. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

theorem diag_meanZero_positiveHaar_sq (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) (hmean : cubeAverage Q u.toFun = 0) :
    positiveHaarNorm Q u.toFun ^ 2 ≤
      cubeScaleFactor Q ^ 2 * (2 / Real.pi) ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.grad x i) ^ 2 := by
  let q : ℝ := Real.sqrt 3
  let K : ℝ := vectorWeakHaarEnergy Q
    (fun x i => u.grad x i)
  let C : ℝ := cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K
  have hq1 : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hq2 : q ^ 2 = 3 := by
    dsimp [q]
    exact Real.sq_sqrt (by norm_num)
  have hratio : q ^ 2 / 9 = 1 / 3 := by rw [hq2]; norm_num
  have hK : 0 ≤ K := by
    dsimp [K]
    exact vectorWeakHaarEnergy_nonneg Q (fun x i => u.grad x i)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : MemLp u.toFun 2 (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hG : ∀ i, MemLp (fun x => u.grad x i) 2
      (normalizedCubeMeasure Q) := u.grad_memL2_normalizedCubeMeasure
  have hroot : energy Q u.toFun ≤
      cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K := by
    have h := h1_fluctuation_L2_bridge_sq Q u
    rw [hmean] at h
    have hn : vectorWeakHaarNorm Q (fun x i => u.grad x i) ^ 2 = K := by
      rw [vectorWeakHaarNorm]
      exact Real.sq_sqrt hK
    simpa only [sub_zero, hn] using h
  have hterm : ∀ j : ℕ, q ^ j *
      energy Q (fun x => u.toFun x -
        cubeProjection Q j u.toFun x) ≤ C * (1 / 3 : ℝ) ^ j := by
    intro j
    have hres := h1_residual_weak_bound Q j u
    have hbound : 0 ≤ energy Q (fun x => u.toFun x -
        cubeProjection Q j u.toFun x) := energy_nonneg Q _
    calc
      q ^ j * energy Q (fun x => u.toFun x -
          cubeProjection Q j u.toFun x)
          ≤ q ^ j * (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2 *
              q ^ j * K) := by
                exact mul_le_mul_of_nonneg_left (by simpa [K] using hres)
                  (pow_nonneg hq0.le _)
      _ = C * (1 / 3 : ℝ) ^ j := by
            have hqpow : q ^ j * q ^ j = 3 ^ j := by
              rw [← mul_pow, ← pow_two, hq2]
            have h9 : (9 : ℝ) ^ j = (3 ^ j) ^ 2 := by
              rw [← pow_mul, mul_comm j 2, pow_mul]
              norm_num
            dsimp [C]
            calc
              q ^ j * (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2 * q ^ j * K) =
                  (cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K) *
                    ((q ^ j * q ^ j) / 9 ^ j) := by ring
              _ = (cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K) *
                    ((3 ^ j) / (3 ^ j) ^ 2) := by rw [hqpow, h9]
              _ = (cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K) *
                    (1 / 3 : ℝ) ^ j := by
                      congr 1
                      have h3j : (3 : ℝ) ^ j ≠ 0 :=
                        pow_ne_zero j (by norm_num)
                      rw [div_pow, one_pow]
                      field_simp [h3j]
  have hgeom : Summable (fun j : ℕ => C * (1 / 3 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hresSummable : Summable (fun j : ℕ => q ^ j *
      energy Q (fun x => u.toFun x -
        cubeProjection Q j u.toFun x)) := by
    apply hgeom.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ q ^ j *
        energy Q (fun x => u.toFun x -
          cubeProjection Q j u.toFun x) :=
      mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
    rw [abs_of_nonneg hnonneg]
    exact hterm j
  have hgeomSum :
      (∑' j : ℕ, q ^ j * energy Q (fun x => u.toFun x -
        cubeProjection Q j u.toFun x)) ≤ C * (3 / 2 : ℝ) := by
    calc
      _ ≤ ∑' j : ℕ, C * (1 / 3 : ℝ) ^ j := hresSummable.tsum_le_tsum hterm hgeom
      _ = C * ∑' j : ℕ, (1 / 3 : ℝ) ^ j := by rw [tsum_mul_left]
      _ = C * (3 / 2 : ℝ) := by
            rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            norm_num
  have habel := primalEnergy_eq_abel Q hq1 hf hresSummable
  have hCcoef : planarC0 ^ 2 + (q - 1) * planarC0 ^ 2 * (3 / 2 : ℝ) =
      (2 / Real.pi) ^ 2 := by
    have hidentity := planarC0_exact_identity
    dsimp only [q]
    rw [div_pow]
    norm_num only [OfNat.ofNat] at hidentity ⊢
    nlinarith only [hidentity]
  have henergy : primalEnergy Q q u.toFun ≤
      cubeScaleFactor Q ^ 2 * (2 / Real.pi) ^ 2 * K := by
    rw [habel]
    have hqcoef : 0 ≤ q - 1 := by linarith
    calc
      energy Q u.toFun +
          (q - 1) * ∑' j : ℕ, q ^ j * energy Q
            (fun x => u.toFun x -
              cubeProjection Q j u.toFun x)
          ≤ cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K +
              (q - 1) * (C * (3 / 2 : ℝ)) :=
            add_le_add hroot (mul_le_mul_of_nonneg_left hgeomSum hqcoef)
      _ = cubeScaleFactor Q ^ 2 * (2 / Real.pi) ^ 2 * K := by
            dsimp [C]
            rw [← hCcoef]
            ring_nf
  have hKnorm : vectorWeakHaarNorm Q
      (fun x i => u.grad x i) ^ 2 = K := by
    rw [vectorWeakHaarNorm]
    exact Real.sq_sqrt hK
  calc
    positiveHaarNorm Q u.toFun ^ 2 =
        primalEnergy Q q u.toFun := by
          rw [positiveHaarNorm]
          exact Real.sq_sqrt (primalEnergy_nonneg Q q (Real.sqrt_nonneg _) _)
    _ ≤ cubeScaleFactor Q ^ 2 * (2 / Real.pi) ^ 2 * K := henergy
    _ = cubeScaleFactor Q ^ 2 * (2 / Real.pi) ^ 2 *
          vectorWeakHaarNorm Q (fun x i => u.grad x i) ^ 2 := by
            rw [hKnorm]

/-- Source cell residual with its actual H¹ witness. -/
def diagCellFluctuation (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    H1Function (openCubeSet Q) := u - h1ConstantOnCube Q (cubeAverage Q u.toFun)

theorem diagCellFluctuation_mean (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    cubeAverage Q (diagCellFluctuation Q u).toFun = 0 := by
  simp only [diagCellFluctuation, H1Function.sub_toFun, h1ConstantOnCube_toFun]
  rw [cubeAverage_sub_const_of_memLp_two Q u.memL2_normalizedCubeMeasure]
  ring

end

end ASDExplicitGamma.Triadic
