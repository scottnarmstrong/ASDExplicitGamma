module

public import ASDExplicitGamma.Inverse.MixedBridgeLocalBudget
public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.SourceInterfaceTransport
public import ASDExplicitGamma.Inverse.SourceSlopeSharp
public import ASDExplicitGamma.Inverse.MixedBridgeChiProfile
public import ASDExplicitGamma.Native.ParentBoundaryMeanProtectedExpectation
public import ASDExplicitGamma.Native.ParentBoundaryMeanGeometry
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryRawProfile
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandCoefficient
public import ASDExplicitGamma.Main.EnvelopeSigns
public import ASDExplicitGamma.Main.EnvelopeRatios
public import ASDExplicitGamma.Main.EnvelopeHProfileArithmetic
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport

/-! A depthwise actual-generator comparison for the translated local OLD slope. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Native
  ASDExplicitGamma.Model ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- The weighted geometric coefficient at a fixed source depth. -/
def mixedBridgeChiDepthW (gamma growth : ℝ) (degree j : ℕ) : ℝ :=
  (1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
    (3 : ℝ) ^ ((growth * gamma - degree) * (j : ℝ))

/-- The affine raw-profile coefficient at a fixed source depth. -/
def mixedBridgeChiDepthRawW (gamma growth : ℝ) (degree j : ℕ) : ℝ :=
  mixedBridgeChiDepthW gamma growth degree j *
    (mainRawA gamma + mainRawS gamma * (j : ℝ))

/-- The exact per-depth coefficient row in the source definition of mainChi. -/
def mixedBridgeLocalChiDepth (v gamma : ℝ) (j : ℕ) : ℝ :=
  (∑ i : Fin 3, mainXiCoefficients v i *
    ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma *
        mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j +
      52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
        mixedBridgeChiDepthW gamma 8 (i.val + 2) j)) +
  2 * mainKf v *
    ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
        mixedBridgeChiDepthRawW gamma 8 2 j +
      52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
        mixedBridgeChiDepthW gamma 6 2 j) +
  2 * v * mainBetaOld ^ 2 * mixedBridgeChiDepthW gamma 4 0 j +
  2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
    ((1 - mainAlpha ^ 2) *
      (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j)

private def mixedBridgeProtectedRateBound
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) : ℝ :=
  let sigma : ℝ := Annealed.sigmaBar M m
  let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let rho := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (m + 1)).val
  let kappa := lemmaVH2kn rho rho
  let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
    (pureFluxCovarianceB 0 (5 + j))
  let E := (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
  let F := parentBoundaryBandTraceCap M 1 (5 + j)
  2 * v * E * (3683 / 2500 : ℝ) +
    2 * v * kappa * E * ((3683 / 2500 : ℝ) * F) +
    v * mu * E ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F)

private theorem mixed_bridge_chi_raw_cap_profile
    (M : ABKModel 2) (j : ℕ) :
    parentBoundaryBandTraceCap M 1 (5 + j) =
      mainRawFactor M.gamma *
        (3 : ℝ) ^ (4 * M.gamma * (j : ℝ)) *
          (mainRawA M.gamma + mainRawS M.gamma * (j : ℝ)) := by
  rw [parent_boundary_common_raw_profile_eq M 1 5 j]
  unfold parentBoundaryCommonRawFactor parentBoundaryCommonRawBase
    mainRawFactor mainRawA mainRawS
  push_cast
  ring_nf

private theorem mixed_bridge_chi_kappa_profile
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) :
    let sigma : ℝ := Annealed.sigmaBar M m
    let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
    let q : ℤ := m - ((5 + j : ℕ) : ℤ)
    let rho := cubeScaleFactor (originCube 2 q) /
      (q3ModelLength (m + 1)).val
    v * lemmaVH2kn rho rho = mainKf v * (1 / 3 : ℝ) ^ (2 * j) := by
  let sigma : ℝ := Annealed.sigmaBar M m
  let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let rho := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (m + 1)).val
  have hqs : q + ((6 + j : ℕ) : ℤ) = m + 1 := by
    dsimp [q]
    omega
  have hrho := pureFlux_bank_source_rho q (6 + j) (by omega)
  rw [hqs] at hrho
  have hrho' : rho = (1 / 3 : ℝ) ^ (6 + j) := by
    calc
      rho = pureFluxCovarianceRho 0 (6 + j - 1) := by simpa [rho] using hrho
      _ = (1 / 3 : ℝ) ^ (6 + j) := by
        unfold pureFluxCovarianceRho
        congr 1
        omega
  have hk := parent_boundary_mean_kn_shape rho
  rw [hrho'] at hk
  have hA2 : mainA2 v = v * (1 / 3 : ℝ) ^ 12 := by
    unfold mainA2
    norm_num [zpow_neg]
  have hpow : ((1 / 3 : ℝ) ^ (6 + j)) ^ 2 =
      (1 / 3 : ℝ) ^ 12 * (1 / 3 : ℝ) ^ (2 * j) := by
    rw [← pow_mul, show (6 + j) * 2 = 12 + 2 * j by omega, pow_add]
  change v * lemmaVH2kn rho rho = mainKf v * (1 / 3 : ℝ) ^ (2 * j)
  rw [hrho']
  unfold mainKf
  rw [hA2, hk, hpow]
  ring

private theorem mixed_bridge_sqrt_source_mode
    (c x q : ℝ) (n : ℕ) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    Real.sqrt (c * (x ^ 2 * q ^ (2 * n))) =
      Real.sqrt c * |x| * q ^ n := by
  have hpow : q ^ (2 * n) = (q ^ n) ^ 2 := by
    calc
      q ^ (2 * n) = q ^ (n * 2) := by rw [Nat.mul_comm]
      _ = (q ^ n) ^ 2 := pow_mul q n 2
  calc
    Real.sqrt (c * (x ^ 2 * q ^ (2 * n))) =
        Real.sqrt ((c * (q ^ n) ^ 2) * x ^ 2) := by
          rw [hpow]
          congr 1; ring
    _ = Real.sqrt (c * (q ^ n) ^ 2) * |x| := by
          rw [Real.sqrt_mul (mul_nonneg hc (sq_nonneg (q ^ n))),
            Real.sqrt_sq_eq_abs]
    _ = Real.sqrt c * q ^ n * |x| := by
          rw [Real.sqrt_mul hc, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (pow_nonneg hq n)]
    _ = Real.sqrt c * |x| * q ^ n := by ring

private theorem mixed_bridge_chi_covariance_modal
    {x v : ℝ} (hv : v = x ^ 2) (j : ℕ) :
    (232 / 125 : ℝ) * (|x| *
      ((Real.sqrt (39 / 5 : ℝ) + (36 / 25 : ℝ) * Real.sqrt (156 / 5 : ℝ)) *
          (1 / 3 : ℝ) ^ (6 + j) +
        (57 / 200 : ℝ) * Real.sqrt (46488 / 25 : ℝ) *
          (1 / 3 : ℝ) ^ (12 + 2 * j))) ^ 2 =
      ∑ i : Fin 3, mainXiCoefficients v i *
        (1 / 3 : ℝ) ^ (j * (i.val + 2)) := by
  have hA2 : mainA2 v = v * (1 / 3 : ℝ) ^ 12 := by
    unfold mainA2
    norm_num [zpow_neg]
  have hA4 : mainA4 v = v * (1 / 3 : ℝ) ^ 24 := by
    unfold mainA4
    norm_num [zpow_neg]
  have hPa0 : mainPa v 0 =
      Real.sqrt (39 / 5 : ℝ) * |x| * (1 / 3 : ℝ) ^ 6 := by
    change Real.sqrt ((39 / 5 : ℝ) * mainA2 v) = _
    rw [hA2, hv]
    exact mixed_bridge_sqrt_source_mode (39 / 5) x (1 / 3) 6
      (by norm_num) (by norm_num)
  have hPa1 : mainPa v 1 =
      (36 / 25 : ℝ) * Real.sqrt (156 / 5 : ℝ) * |x| *
        (1 / 3 : ℝ) ^ 6 := by
    change (36 / 25 : ℝ) *
      Real.sqrt ((156 / 5 : ℝ) * mainA2 v) = _
    rw [hA2, hv]
    rw [mixed_bridge_sqrt_source_mode (156 / 5) x (1 / 3) 6
      (by norm_num) (by norm_num)]
    ring
  have hPa2 : mainPa v 2 =
      (57 / 200 : ℝ) * Real.sqrt (46488 / 25 : ℝ) * |x| *
        (1 / 3 : ℝ) ^ 12 := by
    change (57 / 200 : ℝ) *
      Real.sqrt ((46488 / 25 : ℝ) * mainA4 v) = _
    rw [hA4, hv]
    rw [mixed_bridge_sqrt_source_mode (46488 / 25) x (1 / 3) 12
      (by norm_num) (by norm_num)]
    ring_nf
  have hmod : |x| *
      ((Real.sqrt (39 / 5 : ℝ) + (36 / 25 : ℝ) * Real.sqrt (156 / 5 : ℝ)) *
          (1 / 3 : ℝ) ^ (6 + j) +
        (57 / 200 : ℝ) * Real.sqrt (46488 / 25 : ℝ) *
          (1 / 3 : ℝ) ^ (12 + 2 * j)) =
      (mainPa v 0 + mainPa v 1) * (1 / 3 : ℝ) ^ j +
        mainPa v 2 * (1 / 3 : ℝ) ^ (2 * j) := by
    rw [pow_add, pow_add, hPa0, hPa1, hPa2]
    ring
  have hxi :
      ∑ i : Fin 3, mainXiCoefficients v i *
          (1 / 3 : ℝ) ^ (j * (i.val + 2)) =
        (232 / 125 : ℝ) *
          ((mainPa v 0 + mainPa v 1) * (1 / 3 : ℝ) ^ j +
            mainPa v 2 * (1 / 3 : ℝ) ^ (2 * j)) ^ 2 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      Fin.val_succ, mainXiCoefficients, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue]
    ring
  rw [hmod, hxi]

private theorem mixed_bridge_chi_modal_profile
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) :
    let sigma : ℝ := Annealed.sigmaBar M m
    let x := q3ModelAmplitude M h (m + 1) / sigma
    let v := x ^ 2
    let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
      (pureFluxCovarianceB 0 (5 + j))
    v * mu ≤ ∑ i : Fin 3, mainXiCoefficients v i *
      (1 / 3 : ℝ) ^ (j * (i.val + 2)) := by
  dsimp only
  let sigma : ℝ := Annealed.sigmaBar M m
  let x := q3ModelAmplitude M h (m + 1) / sigma
  let v := x ^ 2
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
    (pureFluxCovarianceB 0 (5 + j))
  have hqs : q + ((6 + j : ℕ) : ℤ) = m + 1 := by
    dsimp [q]
    omega
  have hrow := parent_boundary_mean_mu_row q (6 + j) (by omega)
    (q3ModelAmplitude M h (m + 1)) sigma
  rw [hqs] at hrow
  have hrowCoeff := parent_boundary_mean_own_row_scale q (6 + j)
    (by omega) x
  rw [hqs] at hrowCoeff
  have hratio :
      (q3ModelAmplitude M h (m + 1)) ^ 2 / sigma ^ 2 = v := by
    dsimp [v, x]
    rw [div_pow]
  rw [hratio, hrowCoeff] at hrow
  have hrho : pureFluxCovarianceRho 0 (5 + j) =
      (1 / 3 : ℝ) ^ (6 + j) := by
    unfold pureFluxCovarianceRho
    congr 1
    omega
  have hsmall : (1 / 3 : ℝ) ^ (6 + j) ≤ (1 / 243 : ℝ) := by
    calc
      _ ≤ (1 / 3 : ℝ) ^ 5 := by
        apply pow_le_pow_of_le_one
        · norm_num
        · norm_num
        · omega
      _ = 1 / 243 := by norm_num
  have hdelta : pureFluxCovarianceDelta 0 (5 + j) =
      (1 / 3 : ℝ) ^ (6 + j) := by
    unfold pureFluxCovarianceDelta
    rw [hrho, min_eq_right hsmall]
  have hA : pureFluxCovarianceA 0 (5 + j) =
      (Real.sqrt (39 / 5 : ℝ) +
        (36 / 25 : ℝ) * Real.sqrt (156 / 5 : ℝ)) *
          (1 / 3 : ℝ) ^ (6 + j) +
        (57 / 200 : ℝ) * Real.sqrt (46488 / 25 : ℝ) *
          (1 / 3 : ℝ) ^ (12 + 2 * j) := by
    unfold pureFluxCovarianceA pureFluxCovarianceAr pureFluxCovarianceBA
      pureFluxCovarianceCA
    rw [hrho, hdelta]
    norm_num only [show (78 / 5 : ℝ) / 2 = 39 / 5 by norm_num,
      show (2 : ℝ) * (78 / 5) = 156 / 5 by norm_num,
      show (2 : ℝ) * ((3432 / 5 : ℝ) + (78 / 5) ^ 2) = 46488 / 25 by norm_num]
    ring
  have hmodal := mixed_bridge_chi_covariance_modal
    (x := x) (v := v) rfl j
  calc
    v * mu ≤ (232 / 125 : ℝ) * (|x| *
        ((Real.sqrt (39 / 5 : ℝ) +
          (36 / 25 : ℝ) * Real.sqrt (156 / 5 : ℝ)) *
            (1 / 3 : ℝ) ^ (6 + j) +
          (57 / 200 : ℝ) * Real.sqrt (46488 / 25 : ℝ) *
            (1 / 3 : ℝ) ^ (12 + 2 * j))) ^ 2 := by
      simpa [mu, hA, mul_assoc, add_assoc] using hrow
    _ = ∑ i : Fin 3, mainXiCoefficients v i *
        (1 / 3 : ℝ) ^ (j * (i.val + 2)) := hmodal

private theorem mixed_bridge_chi_rpow_depth_add
    (a b : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (a * (j : ℝ)) * (3 : ℝ) ^ (b * (j : ℝ)) =
      (3 : ℝ) ^ ((a + b) * (j : ℝ)) := by
  rw [show (a + b) * (j : ℝ) = a * (j : ℝ) + b * (j : ℝ) by ring]
  exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm

private theorem mixed_bridge_chi_one_third_nat_rpow (n : ℕ) :
    (1 / 3 : ℝ) ^ n = (3 : ℝ) ^ (-(n : ℝ)) := by
  have hrecip : (1 / 3 : ℝ) = (3 : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hrecip, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

private theorem mixed_bridge_chi_rpow_sub_degree
    (a : ℝ) (d j : ℕ) :
    (3 : ℝ) ^ (a * (j : ℝ)) * (1 / 3 : ℝ) ^ (d * j) =
      (3 : ℝ) ^ ((a - d) * (j : ℝ)) := by
  rw [mixed_bridge_chi_one_third_nat_rpow]
  have hcast : -((d * j : ℕ) : ℝ) = -(d : ℝ) * (j : ℝ) := by
    push_cast
    ring
  rw [hcast,
    show (a - (d : ℝ)) * (j : ℝ) =
      a * (j : ℝ) + (-(d : ℝ)) * (j : ℝ) by ring]
  exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm

private theorem mixed_bridge_local_weight_eq_chi
    (M : ABKModel 2) (j : ℕ) :
    mixedBridgeLocalWeight M j =
      (1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
        ((3683 / 2500 : ℝ) *
          (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by
  have hα : Scalar.inverseHistoryDiscount = mainAlpha := by
    have hh := Scalar.inverse_history_discount_power 1
    have he : (-1 / 4 : ℝ) = -(4 : ℝ)⁻¹ := by norm_num
    simpa [mainAlpha, he] using hh
  unfold mixedBridgeLocalWeight
  rw [hα]
  unfold mixedBridgeOldInverseBaseline
  ring

private theorem mixed_bridge_chi_depth_w_nonneg
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (growth : ℝ) (degree j : ℕ) :
    0 ≤ mixedBridgeChiDepthW gamma growth degree j := by
  have hratio := main_weak_ratio_lt_one gamma 0 hg (by linarith)
  have hαsq : mainAlpha ^ 2 < 1 := by
    simpa only [Real.rpow_zero, mul_one] using hratio
  have hα0 : 0 ≤ mainAlpha := by unfold mainAlpha; positivity
  unfold mixedBridgeChiDepthW
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hαsq.le) (pow_nonneg hα0 _))
    (Real.rpow_nonneg (by norm_num) _)

private theorem mixed_bridge_chi_depth_raw_w_nonneg
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (growth : ℝ) (degree j : ℕ) :
    0 ≤ mixedBridgeChiDepthRawW gamma growth degree j := by
  have hW := mixed_bridge_chi_depth_w_nonneg hg0 hg growth degree j
  have hA := mainRawA_nonneg hg0
  have hS := mainRawS_nonneg hg0
  unfold mixedBridgeChiDepthRawW
  exact mul_nonneg hW (add_nonneg hA (mul_nonneg hS (Nat.cast_nonneg j)))

private theorem mixed_bridge_local_weight_nonneg_chi
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (j : ℕ) :
    0 ≤ mixedBridgeLocalWeight M j := by
  rw [mixed_bridge_local_weight_eq_chi]
  have hα0 : 0 ≤ mainAlpha := by unfold mainAlpha; positivity
  have hratio := main_weak_ratio_lt_one M.gamma 0 hγ
    (by linarith [M.shellPrefix.gamma_pos.le])
  have hαsq : mainAlpha ^ 2 < 1 := by
    simpa only [Real.rpow_zero, mul_one] using hratio
  positivity

private theorem mixed_bridge_chi_depth_row_pad
    (v gamma weight b₀ kappa mu E F : ℝ) (j : ℕ)
    (hv : 0 ≤ v) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hbetaEq : b₀ = mainBetaOld)
    (hcenter : weight * (2 * v * E * b₀) =
      2 * v * b₀ ^ 2 * mixedBridgeChiDepthW gamma 4 0 j)
    (hmixed : weight * (2 * v * kappa * E * (b₀ * F)) =
      2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
        mixedBridgeChiDepthRawW gamma 8 2 j)
    (hmodal : weight * (v * mu * E ^ 2 * (b₀ ^ 2 * F)) ≤
      b₀ ^ 3 * mainRawFactor gamma *
        ∑ i : Fin 3, mainXiCoefficients v i *
          mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j) :
    weight * (2 * v * E * b₀ + 2 * v * kappa * E * (b₀ * F) +
      v * mu * E ^ 2 * (b₀ ^ 2 * F)) ≤
      mixedBridgeLocalChiDepth v gamma j := by
  have hAlpha0 : 0 ≤ mainAlpha := by unfold mainAlpha; positivity
  have hAlphaSqLt : mainAlpha ^ 2 < 1 := by
    have hh := main_weak_ratio_lt_one gamma 0 hg (by linarith)
    simpa only [Real.rpow_zero, mul_one] using hh
  have hAlphaPref : 0 ≤ 1 - mainAlpha ^ 2 := sub_nonneg.mpr hAlphaSqLt.le
  have hRawA : 0 ≤ mainRawA gamma := mainRawA_nonneg hg0
  have hRawS : 0 ≤ mainRawS gamma := mainRawS_nonneg hg0
  have hRawFactor : 0 ≤ mainRawFactor gamma := by unfold mainRawFactor; positivity
  have hBeta : 0 ≤ mainBetaOld := by norm_num [mainBetaOld]
  have hKf : 0 ≤ mainKf v := mainKf_nonneg hv
  have hXi (i : Fin 3) : 0 ≤ mainXiCoefficients v i := mainXiCoefficients_nonneg v i
  have hmodalPad :
      b₀ ^ 3 * mainRawFactor gamma *
          ∑ i : Fin 3, mainXiCoefficients v i *
            mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j ≤
        ∑ i : Fin 3, mainXiCoefficients v i *
          ((26 / 25 : ℝ) * mainBetaOld ^ 3 * mainRawFactor gamma *
              mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j +
            52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
              mixedBridgeChiDepthW gamma 8 (i.val + 2) j) := by
    have hrawW (i : Fin 3) :
        0 ≤ mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j :=
      mixed_bridge_chi_depth_raw_w_nonneg hg0 hg 10 (i.val + 2) j
    have hplainW (i : Fin 3) :
        0 ≤ mixedBridgeChiDepthW gamma 8 (i.val + 2) j :=
      mixed_bridge_chi_depth_w_nonneg hg0 hg 8 (i.val + 2) j
    calc
      _ = ∑ i : Fin 3, mainXiCoefficients v i *
          (mainBetaOld ^ 3 * mainRawFactor gamma *
            mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j) := by
          rw [hbetaEq, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hx := hXi i
          have hy := hrawW i
          have hz := hplainW i
          have hpad :
              mainBetaOld ^ 3 * mainRawFactor gamma *
                  mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j ≤
                (26 / 25 : ℝ) * mainBetaOld ^ 3 * mainRawFactor gamma *
                    mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j +
                  52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
                    mixedBridgeChiDepthW gamma 8 (i.val + 2) j := by
            have hgap : 0 ≤ (1 / 25 : ℝ) * mainBetaOld ^ 3 * mainRawFactor gamma *
                mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j := by positivity
            have hslack : 0 ≤ 52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
                mixedBridgeChiDepthW gamma 8 (i.val + 2) j := by positivity
            nlinarith [hgap, hslack]
          exact mul_le_mul_of_nonneg_left hpad hx
  have hkfPad :
      2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
          mixedBridgeChiDepthRawW gamma 8 2 j ≤
        2 * mainKf v *
          ((26 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma *
              mixedBridgeChiDepthRawW gamma 8 2 j +
            52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
              mixedBridgeChiDepthW gamma 6 2 j) := by
    have hrawW := mixed_bridge_chi_depth_raw_w_nonneg hg0 hg 8 2 j
    have hplainW := mixed_bridge_chi_depth_w_nonneg hg0 hg 6 2 j
    have hpad : mainBetaOld ^ 2 * mainRawFactor gamma *
        mixedBridgeChiDepthRawW gamma 8 2 j ≤
      (26 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma *
          mixedBridgeChiDepthRawW gamma 8 2 j +
        52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
          mixedBridgeChiDepthW gamma 6 2 j := by
      have hgap : 0 ≤ (1 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma *
          mixedBridgeChiDepthRawW gamma 8 2 j := by positivity
      have hslack : 0 ≤ 52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
          mixedBridgeChiDepthW gamma 6 2 j := by positivity
      nlinarith [hgap, hslack]
    rw [hbetaEq]
    have hcoef : 0 ≤ (2 : ℝ) * mainKf v := by positivity
    calc
      _ = (2 * mainKf v) *
          (mainBetaOld ^ 2 * mainRawFactor gamma *
            mixedBridgeChiDepthRawW gamma 8 2 j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpad hcoef
  have hcenterPad :
      2 * v * b₀ ^ 2 * mixedBridgeChiDepthW gamma 4 0 j ≤
        2 * v * mainBetaOld ^ 2 * mixedBridgeChiDepthW gamma 4 0 j := by
    rw [hbetaEq]
  have hrare0 : 0 ≤ 2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
      ((1 - mainAlpha ^ 2) *
        (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j) := by
    have heps : 0 ≤ mainEpsOld := by norm_num [mainEpsOld]
    have hcoef : 0 ≤ 2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld := by positivity
    have hpow : 0 ≤ (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j :=
      pow_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)) _
    exact mul_nonneg hcoef (mul_nonneg hAlphaPref hpow)
  have hsource :
      weight * (2 * v * E * b₀ + 2 * v * kappa * E * (b₀ * F) +
        v * mu * E ^ 2 * (b₀ ^ 2 * F)) ≤
        2 * v * b₀ ^ 2 * mixedBridgeChiDepthW gamma 4 0 j +
          2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
            mixedBridgeChiDepthRawW gamma 8 2 j +
          b₀ ^ 3 * mainRawFactor gamma *
            ∑ i : Fin 3, mainXiCoefficients v i *
              mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j := by
    calc
      _ = weight * (2 * v * E * b₀) +
          weight * (2 * v * kappa * E * (b₀ * F)) +
          weight * (v * mu * E ^ 2 * (b₀ ^ 2 * F)) := by ring
      _ ≤ _ := add_le_add (add_le_add (le_of_eq hcenter) (le_of_eq hmixed)) hmodal
  have hprofile :
      2 * v * b₀ ^ 2 * mixedBridgeChiDepthW gamma 4 0 j +
          2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
            mixedBridgeChiDepthRawW gamma 8 2 j +
          b₀ ^ 3 * mainRawFactor gamma *
            ∑ i : Fin 3, mainXiCoefficients v i *
              mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j ≤
        mixedBridgeLocalChiDepth v gamma j := by
    unfold mixedBridgeLocalChiDepth
    have hslack : 0 ≤ 2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
        ((1 - mainAlpha ^ 2) *
          (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j) := hrare0
    calc
      _ =
          (b₀ ^ 3 * mainRawFactor gamma *
              ∑ i : Fin 3, mainXiCoefficients v i *
                mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j +
            2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
              mixedBridgeChiDepthRawW gamma 8 2 j +
            2 * v * b₀ ^ 2 * mixedBridgeChiDepthW gamma 4 0 j) := by ring
      _ ≤
          (∑ i : Fin 3, mainXiCoefficients v i *
              ((26 / 25 : ℝ) * mainBetaOld ^ 3 * mainRawFactor gamma *
                  mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j +
                52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
                  mixedBridgeChiDepthW gamma 8 (i.val + 2) j)) +
            2 * mainKf v *
              ((26 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma *
                  mixedBridgeChiDepthRawW gamma 8 2 j +
                52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
                  mixedBridgeChiDepthW gamma 6 2 j) +
            2 * v * mainBetaOld ^ 2 * mixedBridgeChiDepthW gamma 4 0 j := by
          exact add_le_add (add_le_add hmodalPad hkfPad) hcenterPad
      _ ≤ _ := by
        let A : ℝ :=
          (∑ i : Fin 3, mainXiCoefficients v i *
            ((26 / 25 : ℝ) * mainBetaOld ^ 3 * mainRawFactor gamma *
                mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j +
              52 * v * Real.sqrt 3 * mainBetaOld ^ 4 *
                mixedBridgeChiDepthW gamma 8 (i.val + 2) j)) +
          2 * mainKf v *
            ((26 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma *
                mixedBridgeChiDepthRawW gamma 8 2 j +
              52 * v * Real.sqrt 3 * mainBetaOld ^ 3 *
                mixedBridgeChiDepthW gamma 6 2 j) +
          2 * v * mainBetaOld ^ 2 * mixedBridgeChiDepthW gamma 4 0 j
        change A ≤ A +
          2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld *
            ((1 - mainAlpha ^ 2) *
              (mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64)) ^ j)
        exact le_add_of_nonneg_right hslack
  exact hsource.trans hprofile

private theorem mixed_bridge_chi_depth_source_bound
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (j : ℕ) :
    mixedBridgeLocalWeight M j *
        mixedBridgeProtectedRateBound M h m j ≤
      mixedBridgeLocalChiDepth
        ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma j := by
  let gamma := M.gamma
  let sigma : ℝ := Annealed.sigmaBar M m
  let x := q3ModelAmplitude M h (m + 1) / sigma
  let v := x ^ 2
  let b₀ : ℝ := 3683 / 2500
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let rho := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (m + 1)).val
  let kappa := lemmaVH2kn rho rho
  let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
    (pureFluxCovarianceB 0 (5 + j))
  let E := (3 : ℝ) ^ (2 * gamma * (j : ℝ))
  let F := parentBoundaryBandTraceCap M 1 (5 + j)
  have hg0 : 0 ≤ gamma := M.shellPrefix.gamma_pos.le
  have hg : gamma ≤ gammaZero := hγ
  have hv : 0 ≤ v := by dsimp [v, x]; positivity
  have hW : mixedBridgeLocalWeight M j =
      (1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
        (b₀ * (3 : ℝ) ^ (2 * gamma * (j : ℝ))) := by
    rw [mixed_bridge_local_weight_eq_chi]
  have hE2 : E ^ 2 = (3 : ℝ) ^ (4 * gamma * (j : ℝ)) := by
    dsimp [E]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hF : F = mainRawFactor gamma *
      (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
        (mainRawA gamma + mainRawS gamma * (j : ℝ)) := by
    simpa [gamma] using mixed_bridge_chi_raw_cap_profile M j
  have hκ : v * kappa = mainKf v * (1 / 3 : ℝ) ^ (2 * j) := by
    simpa [sigma, v, x, q, rho, kappa, gamma] using
      mixed_bridge_chi_kappa_profile M h m j
  have hμ : v * mu ≤ ∑ i : Fin 3, mainXiCoefficients v i *
      (1 / 3 : ℝ) ^ (j * (i.val + 2)) := by
    simpa [sigma, v, x, q, mu] using
      mixed_bridge_chi_modal_profile M h m j
  have hlocal0 : 0 ≤ mixedBridgeLocalWeight M j :=
    mixed_bridge_local_weight_nonneg_chi M hγ j
  have hE0 : 0 ≤ E := by positivity
  have hF0 : 0 ≤ F := parent_boundary_band_trace_cap_nonneg M 1 (5 + j)
  have hκ0 : 0 ≤ kappa := by
    change 0 ≤ lemmaVH2kn rho rho
    rw [parent_boundary_mean_kn_shape]
    have hqs : q + ((6 + j : ℕ) : ℤ) = m + 1 := by
      dsimp [q]
      omega
    have hrho := pureFlux_bank_source_rho q (6 + j) (by omega)
    rw [hqs] at hrho
    have hrho0 : 0 ≤ rho := by
      calc
        rho = pureFluxCovarianceRho 0 (5 + j) := by simpa [rho] using hrho
        _ ≥ 0 := by
          unfold pureFluxCovarianceRho
          positivity
    positivity
  have hμ0 : 0 ≤ mu := (pureFlux_covariance_mu_lower _ _).1
  have hAlpha0 : 0 ≤ mainAlpha := by unfold mainAlpha; positivity
  have hAlphaSqLt : mainAlpha ^ 2 < 1 := by
    have hh := main_weak_ratio_lt_one gamma 0 hg (by linarith [hg0])
    simpa only [Real.rpow_zero, mul_one] using hh
  have hAlphaPref : 0 ≤ 1 - mainAlpha ^ 2 := (sub_nonneg.mpr hAlphaSqLt.le)
  have hRawA : 0 ≤ mainRawA gamma := mainRawA_nonneg hg0
  have hRawS : 0 ≤ mainRawS gamma := mainRawS_nonneg hg0
  have hRawFactor : 0 ≤ mainRawFactor gamma := by unfold mainRawFactor; positivity
  have hBeta : 0 ≤ mainBetaOld := by norm_num [mainBetaOld]
  have hKf : 0 ≤ mainKf v := mainKf_nonneg hv
  have hXi (i : Fin 3) : 0 ≤ mainXiCoefficients v i := mainXiCoefficients_nonneg v i
  have hcenter :
      mixedBridgeLocalWeight M j * (2 * v * E * b₀) =
        2 * v * b₀ ^ 2 * mixedBridgeChiDepthW gamma 4 0 j := by
    calc
      _ = 2 * v * b₀ ^ 2 * (1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
          ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
            (3 : ℝ) ^ (2 * gamma * (j : ℝ))) := by
          rw [hW]
          dsimp [E]
          ring
      _ = _ := by
          unfold mixedBridgeChiDepthW
          rw [mixed_bridge_chi_rpow_depth_add _ _ j]
          dsimp [b₀]
          ring_nf
  have hmixed :
      mixedBridgeLocalWeight M j *
        (2 * v * kappa * E * (b₀ * F)) =
        2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
          mixedBridgeChiDepthRawW gamma 8 2 j := by
    have h2k : 2 * v * kappa = 2 * (v * kappa) := by ring
    have hpow :
        (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
          (1 / 3 : ℝ) ^ (2 * j) *
          (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
          (3 : ℝ) ^ (4 * gamma * (j : ℝ)) =
          (3 : ℝ) ^ ((8 * gamma - 2) * (j : ℝ)) := by
      calc
        _ = (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
            (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
            (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
            (1 / 3 : ℝ) ^ (2 * j) := by ring
        _ = (3 : ℝ) ^ ((2 * gamma + 2 * gamma) * (j : ℝ)) *
            (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
            (1 / 3 : ℝ) ^ (2 * j) := by
              rw [mixed_bridge_chi_rpow_depth_add _ _ j]
        _ = (3 : ℝ) ^ ((2 * gamma + 2 * gamma + 4 * gamma) * (j : ℝ)) *
            (1 / 3 : ℝ) ^ (2 * j) := by
              rw [mixed_bridge_chi_rpow_depth_add _ _ j]
        _ = (3 : ℝ) ^ (8 * gamma * (j : ℝ)) *
            (1 / 3 : ℝ) ^ (2 * j) := by congr 1; ring_nf
        _ = (3 : ℝ) ^ ((8 * gamma - 2) * (j : ℝ)) :=
          mixed_bridge_chi_rpow_sub_degree (8 * gamma) 2 j
    rw [hW, hF, h2k, hκ]
    unfold mixedBridgeChiDepthRawW mixedBridgeChiDepthW
    dsimp [E, b₀]
    calc
      _ = 2 * mainKf v * b₀ ^ 2 * mainRawFactor gamma *
          ((1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
            ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
              (1 / 3 : ℝ) ^ (2 * j) *
              (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
              (3 : ℝ) ^ (4 * gamma * (j : ℝ))) *
            (mainRawA gamma + mainRawS gamma * (j : ℝ))) := by ring
      _ = _ := by rw [hpow]
  have hmodal :
      mixedBridgeLocalWeight M j *
        (v * mu * E ^ 2 * (b₀ ^ 2 * F)) ≤
        b₀ ^ 3 * mainRawFactor gamma *
          ∑ i : Fin 3, mainXiCoefficients v i *
            mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j := by
    have hcoeff0 : 0 ≤ mixedBridgeLocalWeight M j * E ^ 2 *
        (b₀ ^ 2 * F) := by positivity
    have hmodalBound := mul_le_mul_of_nonneg_left hμ hcoeff0
    have hpow (i : Fin 3) :
        (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
          (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
          (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
          (1 / 3 : ℝ) ^ (j * (i.val + 2)) =
          (3 : ℝ) ^ ((10 * gamma - ((i.val + 2 : ℕ) : ℝ)) * (j : ℝ)) := by
      calc
        _ = (3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
            (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
            (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
            (1 / 3 : ℝ) ^ ((i.val + 2) * j) := by
              rw [Nat.mul_comm j (i.val + 2)]
        _ = (3 : ℝ) ^ (10 * gamma * (j : ℝ)) *
            (1 / 3 : ℝ) ^ ((i.val + 2) * j) := by
              rw [mixed_bridge_chi_rpow_depth_add _ _ j,
                mixed_bridge_chi_rpow_depth_add _ _ j]
              congr 1; ring_nf
        _ = (3 : ℝ) ^ ((10 * gamma - ((i.val + 2 : ℕ) : ℝ)) * (j : ℝ)) :=
          mixed_bridge_chi_rpow_sub_degree (10 * gamma) (i.val + 2) j
    calc
      _ = (mixedBridgeLocalWeight M j * E ^ 2 * (b₀ ^ 2 * F)) *
          (v * mu) := by ring
      _ ≤ (mixedBridgeLocalWeight M j * E ^ 2 * (b₀ ^ 2 * F)) *
          (∑ i : Fin 3, mainXiCoefficients v i *
            (1 / 3 : ℝ) ^ (j * (i.val + 2))) := hmodalBound
      _ = b₀ ^ 3 * mainRawFactor gamma *
          ∑ i : Fin 3, mainXiCoefficients v i *
            mixedBridgeChiDepthRawW gamma 10 (i.val + 2) j := by
          rw [hW, hF, hE2]
          unfold mixedBridgeChiDepthRawW mixedBridgeChiDepthW
          conv_lhs => rw [Finset.mul_sum]
          conv_rhs => rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          calc
            _ = b₀ ^ 3 * mainRawFactor gamma *
                (mainXiCoefficients v i *
                  ((1 - mainAlpha ^ 2) * mainAlpha ^ (2 * j) *
                    ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) *
                      (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
                      (3 : ℝ) ^ (4 * gamma * (j : ℝ)) *
                      (1 / 3 : ℝ) ^ (j * (i.val + 2))) *
                    (mainRawA gamma + mainRawS gamma * (j : ℝ)))) := by ring
            _ = _ := by rw [hpow i]
  have hbetaEq : b₀ = mainBetaOld := by
    norm_num [b₀, mainBetaOld]
  unfold mixedBridgeProtectedRateBound
  dsimp only [sigma, v, x, gamma, q, rho, kappa, mu, E, F]
  rw [show (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2 = v by rfl]
  simpa only [gamma] using
    mixed_bridge_chi_depth_row_pad v gamma
      (mixedBridgeLocalWeight M j) b₀ kappa mu E F j
      hv hg0 hg hbetaEq hcenter hmixed hmodal

/-- The exact shifted local OLD slope is bounded by the explicit `mainChi`
coefficient used by the depth-five `mainEnvelopeXi` profile. -/
theorem mixed_bridge_local_slope_main_chi
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    mixedBridgeLocalSlope M h m ≤
      mainChi
        ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2)
        M.gamma := by
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  have hprofile := mixed_bridge_local_chi_profile_tsum
    v M.gamma M.shellPrefix.gamma_pos.le hγ
  have hpoint (j : ℕ) :
      mixedBridgeLocalWeight M j *
          inSourceMeanSlopeActual M h m (5 + j) ≤
        mixedBridgeChiProfileDepth v M.gamma j := by
    have hsource := inSourceMeanSlopeActual_le_protectedRow
      M h hM hγ N hpast m hm j
    have hsource' : inSourceMeanSlopeActual M h m (5 + j) ≤
        mixedBridgeProtectedRateBound M h m j := by
      exact hsource
    calc
      _ ≤ mixedBridgeLocalWeight M j *
          mixedBridgeProtectedRateBound M h m j :=
        mul_le_mul_of_nonneg_left
          hsource'
          (mixed_bridge_local_weight_nonneg_chi M hγ j)
      _ ≤ mixedBridgeLocalChiDepth v M.gamma j := by
        simpa only [v] using mixed_bridge_chi_depth_source_bound M h hγ m j
      _ = mixedBridgeChiProfileDepth v M.gamma j := by
        rfl
  have hterm0 (j : ℕ) :
      0 ≤ mixedBridgeLocalWeight M j *
        inSourceMeanSlopeActual M h m (5 + j) :=
    mul_nonneg (mixed_bridge_local_weight_nonneg_chi M hγ j)
      (le_max_left _ _)
  have hsummable := Summable.of_nonneg_of_le hterm0 hpoint hprofile.1
  have hsum := hsummable.tsum_le_tsum hpoint hprofile.1
  change (∑' j : ℕ, mixedBridgeLocalWeight M j *
    inSourceMeanSlopeActual M h m (5 + j)) ≤ mainChi v M.gamma
  calc
    _ ≤ ∑' j : ℕ, mixedBridgeChiProfileDepth v M.gamma j := hsum
    _ = mainChi v M.gamma := hprofile.2

end
end ASDExplicitGamma.Inverse
