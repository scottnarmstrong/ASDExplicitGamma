module

public import ASDExplicitGamma.Main.EnvelopeHFixedFrameGenerator

/-! Sharper source-depth caps for the fixed-frame p=20 control. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Algsuperdiff.Section3 MeasureTheory

private theorem main_three_rpow_one_sixteenth_le_four_thirds :
    (3 : ℝ) ^ (1 / 16 : ℝ) ≤ 4 / 3 := by
  have hroot : ((3 : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ) = 3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hpower : ((3 : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ) ≤
      (4 / 3 : ℝ) ^ (16 : ℕ) := by
    rw [hroot]
    norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num)
    (by norm_num : (16 : ℕ) ≠ 0)).1 hpower

private theorem main_rawShell_fixed_old_frame_p20_discount_caps
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    (3 / 4 : ℝ) ≤ mainAlpha ∧ mainAlpha ≤ 1 ∧
      0 ≤ mainAlpha * (3 : ℝ) ^ (2 * gamma) ∧
      mainAlpha * (3 : ℝ) ^ (2 * gamma) ≤ 81 / 100 ∧
      0 ≤ mainAlpha * (3 : ℝ) ^ (8 * gamma) ∧
      mainAlpha * (3 : ℝ) ^ (8 * gamma) ≤ 81 / 100 ∧
      (3 : ℝ) ^ (12 * gamma) ≤ 4 / 3 ∧
      (3 : ℝ) ^ (48 * gamma) ≤ 4 / 3 ∧
      mainRawA gamma ≤ 4000 ∧ mainRawS gamma ≤ 12 := by
  have hg' : gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have hAlpha0 : 0 ≤ mainAlpha := by
    dsimp [mainAlpha]
    positivity
  have hAlpha1 : mainAlpha ≤ 1 := by
    dsimp [mainAlpha]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hAlpha4 : mainAlpha ^ 4 = (1 / 3 : ℝ) := by
    dsimp [mainAlpha]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [Real.rpow_neg_one]
  have hAlphaLow : (3 / 4 : ℝ) ≤ mainAlpha := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hAlpha0 (by norm_num : (4 : ℕ) ≠ 0)).1
    rw [hAlpha4]
    norm_num
  let r0 : ℝ := mainAlpha * (3 : ℝ) ^ (2 * gamma)
  let r1 : ℝ := mainAlpha * (3 : ℝ) ^ (8 * gamma)
  have hr0 : 0 ≤ r0 := by dsimp [r0]; positivity
  have hr1 : 0 ≤ r1 := by dsimp [r1]; positivity
  have hr1eq : r1 = (3 : ℝ) ^ (8 * gamma - 1 / 4) := by
    dsimp [r1, mainAlpha]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hr1pow : r1 ^ 5 = (3 : ℝ) ^ ((8 * gamma - 1 / 4) * 5) := by
    rw [hr1eq, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
  have hexp5 : (8 * gamma - 1 / 4) * 5 ≤ -1 := by
    norm_num at hg'
    nlinarith
  have hr1powle : r1 ^ 5 ≤ (1 / 3 : ℝ) := by
    calc
      _ = (3 : ℝ) ^ ((8 * gamma - 1 / 4) * 5) := hr1pow
      _ ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp5
      _ = 1 / 3 := by norm_num [Real.rpow_neg_one]
  have hr1le : r1 ≤ 81 / 100 := by
    apply (pow_le_pow_iff_left₀ hr1 (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).1
    calc
      _ ≤ 1 / 3 := hr1powle
      _ ≤ (81 / 100 : ℝ) ^ 5 := by norm_num
  have hr0le : r0 ≤ r1 := by
    dsimp [r0, r1]
    apply mul_le_mul_of_nonneg_left _ hAlpha0
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hg0])
  have h12 : 12 * gamma ≤ 1 / 16 := by norm_num at hg'; nlinarith
  have h48 : 48 * gamma ≤ 1 / 16 := by norm_num at hg'; nlinarith
  have hpow12 : (3 : ℝ) ^ (12 * gamma) ≤ 4 / 3 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) h12).trans
      main_three_rpow_one_sixteenth_le_four_thirds
  have hpow48 : (3 : ℝ) ^ (48 * gamma) ≤ 4 / 3 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) h48).trans
      main_three_rpow_one_sixteenth_le_four_thirds
  have hRawA : mainRawA gamma ≤ 4000 := by
    dsimp [mainRawA]
    nlinarith [hg']
  have hRawS : mainRawS gamma ≤ 12 := by
    dsimp [mainRawS]
    nlinarith [hg']
  exact ⟨hAlphaLow, hAlpha1, hr0, hr0le.trans hr1le,
    hr1, hr1le, hpow12, hpow48, hRawA, hRawS⟩

/-- The exact six-generation source mesh gives small coefficients in the
fixed-frame generator, sharper than the coarse caps used for summability. -/
private theorem main_rawShell_fixed_old_frame_p20_refined_caps
    (q : ℤ) (s : ℕ) (hs : 6 ≤ s) :
    let ρ := cubeScaleFactor (originCube 2 q) /
      (q3ModelLength (q + (s : ℤ))).1
    let δ := diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1
    let κ := rawTraceRemainderKappaF ρ δ
    let κB := rawTraceRemainderB ρ δ
    let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1))
    let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1))
    let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
    A ≤ 13 / 500 ∧ B ≤ 21 / 1000 ∧ κ ≤ 1 / 10000 ∧
      0 ≤ κB ∧ κB ≤ 21 / 1000 ∧ μR ≤ 1 / 200 := by
  dsimp only
  let ρ := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (q + (s : ℤ))).1
  let δ := diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
    (q3ModelLength (q + (s : ℤ))).1
  let κ := rawTraceRemainderKappaF ρ δ
  let κB := rawTraceRemainderB ρ δ
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
  have hscale := main_rawShell_fixed_old_frame_p20_source_scales q s hs
  have hρeq : ρ = (1 / 3 : ℝ) ^ s := by
    change cubeScaleFactor (originCube 2 q) /
        (q3ModelLength (q + (s : ℤ))).1 = (1 / 3 : ℝ) ^ s
    rw [hscale.1]
    unfold pureFluxCovarianceRho
    congr 1
    omega
  have hδeq : δ = pureFluxCovarianceDelta 0 (s - 1) := by
    change diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1 = _
    exact hscale.2
  have hδnonneg : 0 ≤ δ := by
    change 0 ≤ diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1
    rw [hscale.2]
    exact (pureFlux_covariance_delta_bounds 0 (s - 1)).1
  have hρnonneg : 0 ≤ ρ := by rw [hρeq]; positivity
  have hρle : ρ ≤ 1 / 729 := by
    rw [hρeq]
    calc
      _ ≤ (1 / 3 : ℝ) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
      _ = 1 / 729 := by norm_num
  have hρbankeq : pureFluxCovarianceRho 0 (s - 1) = (1 / 3 : ℝ) ^ s := by
    calc
      _ = ρ := hscale.1.symm
      _ = (1 / 3 : ℝ) ^ s := hρeq
  have hρbank : 0 ≤ pureFluxCovarianceRho 0 (s - 1) := by
    rw [hρbankeq]
    positivity
  have hρbankle : pureFluxCovarianceRho 0 (s - 1) ≤ 1 / 729 := by
    rw [hρbankeq]
    calc
      _ ≤ (1 / 3 : ℝ) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
      _ = 1 / 729 := by norm_num
  have hδbankeq : pureFluxCovarianceDelta 0 (s - 1) = δ := hscale.2.symm
  have hδbank : 0 ≤ pureFluxCovarianceDelta 0 (s - 1) := by
    exact (pureFlux_covariance_delta_bounds 0 (s - 1)).1
  have hδbankle : pureFluxCovarianceDelta 0 (s - 1) ≤ 1 / 729 :=
    (pureFlux_covariance_delta_bounds 0 (s - 1)).2.trans hρbankle
  have hδle : δ ≤ 1 / 729 := by
    change diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1 ≤ 1 / 729
    rw [hscale.2]
    exact hδbankle
  have hsqrtA0 : Real.sqrt (78 / 10 : ℝ) ≤ 14 / 5 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtA1 : Real.sqrt (156 / 5 : ℝ) ≤ 28 / 5 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtA2 : Real.sqrt (46488 / 25 : ℝ) ≤ 44 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtB1 : Real.sqrt (78 / 5 : ℝ) ≤ 4 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtB2 : Real.sqrt (23244 / 25 : ℝ) ≤ 31 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hρsq : (pureFluxCovarianceRho 0 (s - 1)) ^ 2 ≤ (1 / 729 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hρbank hρbankle 2
  have hδsq : (pureFluxCovarianceDelta 0 (s - 1)) ^ 2 ≤ (1 / 729 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hδbank hδbankle 2
  have hA : 0 ≤ A ∧ A ≤ 13 / 500 := by
    constructor
    · dsimp [A]; unfold rawTraceRemainderA; positivity
    · dsimp [A]
      unfold rawTraceRemainderA
      calc
        _ ≤ 1.860 * (14 / 5) * (1 / 729) +
            2.36412 * (28 / 5) * (1 / 729) +
            0.52288 * 44 * (1 / 729 : ℝ) ^ 2 := by
              gcongr
        _ ≤ 13 / 500 := by norm_num
  have hB : 0 ≤ B ∧ B ≤ 21 / 1000 := by
    constructor
    · dsimp [B]; unfold rawTraceRemainderB; positivity
    · dsimp [B]
      unfold rawTraceRemainderB
      calc
        _ ≤ 1.860 * (14 / 5) * (1 / 729) +
            2.36412 * 4 * (1 / 729) +
            0.52288 * 31 * (1 / 729 : ℝ) ^ 2 := by
              gcongr
        _ ≤ 21 / 1000 := by norm_num
  have hsqrt2 : 1 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 3 / 2 := by
    constructor
    · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrt2lower : (7 / 5 : ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hκ : 0 ≤ κ ∧ κ ≤ 1 / 10000 := by
    constructor
    · change 0 ≤ rawTraceRemainderKappaF ρ δ
      unfold rawTraceRemainderKappaF
      positivity
    · change rawTraceRemainderKappaF ρ δ ≤ 1 / 10000
      unfold rawTraceRemainderKappaF
      have hρδ : ρ * δ ≤ (1 / 729 : ℝ) ^ 2 := by
        calc
          ρ * δ ≤ (1 / 729 : ℝ) * δ :=
            mul_le_mul_of_nonneg_right hρle hδnonneg
          _ ≤ (1 / 729 : ℝ) * (1 / 729 : ℝ) :=
            mul_le_mul_of_nonneg_left hδle (by norm_num)
          _ = (1 / 729 : ℝ) ^ 2 := by ring
      have hcoef : (78 / 5 : ℝ) / Real.sqrt 2 ≤ 78 / 7 := by
        apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 2)).2
        nlinarith [hsqrt2lower]
      have hρsqActual : ρ ^ 2 ≤ (1 / 729 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hρnonneg hρle 2
      have hδsqActual : δ ^ 2 ≤ (1 / 729 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hδnonneg hδle 2
      have hterm1 : 1.860 * ((78 / 5 : ℝ) / 4) * ρ ^ 2 ≤
          1.860 * ((78 / 5 : ℝ) / 4) * (1 / 729 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hρsqActual (by positivity)
      have hcoef2 : 2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) ≤
          2.36412 * (78 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_left hcoef (by norm_num)
      have hterm2 : 2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * (ρ * δ) ≤
          2.36412 * (78 / 7 : ℝ) * (1 / 729 : ℝ) ^ 2 := by
        calc
          _ ≤ 2.36412 * (78 / 7 : ℝ) * (ρ * δ) :=
            mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg hρnonneg hδnonneg)
          _ ≤ _ := mul_le_mul_of_nonneg_left hρδ (by positivity)
      have hcoef3 : 0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) ≤
          0.52288 * (3 / 2 : ℝ) * (78 / 5 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt2.2 (by norm_num)) (by norm_num)
      have hterm3 : 0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) * δ ^ 2 ≤
          0.52288 * (3 / 2 : ℝ) * (78 / 5 : ℝ) * (1 / 729 : ℝ) ^ 2 :=
        mul_le_mul hcoef3 hδsqActual (by positivity) (by positivity)
      calc
        _ = 1.860 * ((78 / 5 : ℝ) / 4) * ρ ^ 2 +
            2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * (ρ * δ) +
            0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) * δ ^ 2 := by ring
        _ ≤ 1.860 * ((78 / 5 : ℝ) / 4) * (1 / 729 : ℝ) ^ 2 +
            2.36412 * (78 / 7 : ℝ) * (1 / 729 : ℝ) ^ 2 +
            0.52288 * (3 / 2 : ℝ) * (78 / 5 : ℝ) * (1 / 729 : ℝ) ^ 2 :=
              add_le_add (add_le_add hterm1 hterm2) hterm3
        _ ≤ 1 / 10000 := by norm_num
  have hκB : 0 ≤ κB ∧ κB ≤ 21 / 1000 := by
    constructor
    · dsimp [κB, ρ, δ]; unfold rawTraceRemainderB; positivity
    · have hEq : κB = B := by
        change rawTraceRemainderB ρ δ =
          rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
            (pureFluxCovarianceDelta 0 (s - 1))
        rw [hρeq, hδeq, hρbankeq, hδbankeq]
      simpa only [hEq] using hB.2
  have hH0 : 0 ≤ rawTraceRemainderH0 ∧ rawTraceRemainderH0 ≤ 12 / 5 := by
    norm_num [rawTraceRemainderH0]
  have hsqrtH0 : Real.sqrt rawTraceRemainderH0 ≤ 8 / 5 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num [rawTraceRemainderH0]⟩
  have hD0 : 0 ≤ rawTraceRemainderD0 ∧ rawTraceRemainderD0 ≤ 4 := by
    constructor
    · unfold rawTraceRemainderD0
      exact add_nonneg (by norm_num [rawTraceRemainderH0]) (Real.sqrt_nonneg _)
    · unfold rawTraceRemainderD0
      nlinarith [hsqrtH0]
  have hμR : 0 ≤ μR ∧ μR ≤ 1 / 200 := by
    constructor
    · dsimp [μR]
      unfold rawTraceRemainderMu
      have hA0 := hA.1
      have hB0 := hB.1
      have hH00 := hH0.1
      have hD00 := hD0.1
      positivity
    · dsimp [μR]
      unfold rawTraceRemainderMu
      have hrad : rawTraceRemainderH0 ^ 2 * A ^ 4 +
          4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2 ≤ (1 / 200 : ℝ) ^ 2 := by
        have hA2 : A ^ 2 ≤ (13 / 500 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hA.1 hA.2 2
        have hA4 : A ^ 4 ≤ (13 / 500 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hA.1 hA.2 4
        have hB2 : B ^ 2 ≤ (21 / 1000 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hB.1 hB.2 2
        have hH02 : rawTraceRemainderH0 ^ 2 ≤ (12 / 5 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hH0.1 hH0.2 2
        have hD02 : rawTraceRemainderD0 ^ 2 ≤ (4 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hD0.1 hD0.2 2
        have hfirst : rawTraceRemainderH0 ^ 2 * A ^ 4 ≤
            (12 / 5 : ℝ) ^ 2 * (13 / 500 : ℝ) ^ 4 :=
          mul_le_mul hH02 hA4 (by positivity) (by positivity)
        have hDA : rawTraceRemainderD0 ^ 2 * A ^ 2 ≤
            (4 : ℝ) ^ 2 * (13 / 500 : ℝ) ^ 2 :=
          mul_le_mul hD02 hA2 (by positivity) (by positivity)
        have hsecond : 4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2 ≤
            4 * (4 : ℝ) ^ 2 * (13 / 500 : ℝ) ^ 2 * (21 / 1000 : ℝ) ^ 2 := by
          have hmul := mul_le_mul hDA hB2 (by positivity) (by positivity)
          nlinarith [hmul]
        calc
          _ ≤ (12 / 5 : ℝ) ^ 2 * (13 / 500 : ℝ) ^ 4 +
              4 * (4 : ℝ) ^ 2 * (13 / 500 : ℝ) ^ 2 * (21 / 1000 : ℝ) ^ 2 :=
            add_le_add hfirst hsecond
          _ ≤ (1 / 200 : ℝ) ^ 2 := by norm_num
      have hroot : Real.sqrt (rawTraceRemainderH0 ^ 2 * A ^ 4 +
          4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2) ≤ 1 / 200 :=
        (Real.sqrt_le_iff).2 ⟨by positivity, hrad⟩
      have hbase : rawTraceRemainderH0 * A ^ 2 ≤
          (12 / 5 : ℝ) * (13 / 500 : ℝ) ^ 2 := by
        have hA2 : A ^ 2 ≤ (13 / 500 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hA.1 hA.2 2
        calc
          _ ≤ (12 / 5 : ℝ) * A ^ 2 := by
            exact mul_le_mul_of_nonneg_right hH0.2 (by positivity)
          _ ≤ (12 / 5 : ℝ) * (13 / 500 : ℝ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hA2 (by norm_num)
      nlinarith
  rcases hA with ⟨_, hA⟩
  rcases hB with ⟨_, hB⟩
  rcases hκ with ⟨_, hκ⟩
  rcases hκB with ⟨hκB0, hκB⟩
  rcases hμR with ⟨_, hμR⟩
  exact ⟨hA, hB, hκ, hκB0, hκB, hμR⟩

/-- The actual fixed-frame control has a small coefficient once the exact
source mesh is retained, before replacing it by the coarse summability cap. -/
theorem main_rawShell_fixed_old_frame_p20_control_linear_clock_bound
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) :
    mainRawShellOldFrameP20Control M h m j ≤
      ((q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2) *
        (120 * rawTraceOldFrameP20LocalClock M.gamma (6 + j) +
          (67 / 1000 : ℝ) *
            rawTraceOldFrameP20LocalClock M.gamma (6 + j) ^ 2 *
              rawTraceOldFrameP20FullResponseCap M.gamma (6 + j)) := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  let J := q + (s : ℤ)
  let ρ := cubeScaleFactor (originCube 2 q) / (q3ModelLength J).1
  let δ := diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
    (q3ModelLength J).1
  let κ := rawTraceRemainderKappaF ρ δ
  let κB := rawTraceRemainderB ρ δ
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
  let v := (q3ModelAmplitude M h J) ^ 2 /
    (Annealed.sigmaBar M m : ℝ) ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
  have hs : 6 ≤ s := by dsimp [s]; omega
  have hcaps := main_rawShell_fixed_old_frame_p20_refined_caps q s hs
  rcases hcaps with ⟨hA, hB, hκ, hκB0, hκB, hμR⟩
  have hβ : (3683 / 2500 : ℝ) ≤ 3 / 2 := by norm_num
  have hgamma_pos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hCge : 1 ≤ C := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    apply Real.one_le_rpow (by norm_num)
    have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show 1 ≤ s by omega)
    positivity
  have hfCapge : 1 ≤ fCap := by
    dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
    have hpow : 1 ≤ (3 : ℝ) ^
        (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ)) := by
      apply Real.one_le_rpow (by norm_num)
      positivity
    have hfac : 1 ≤ 4 * ((2018618 : ℝ) / 1000000 + M.gamma *
        ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) := by
      have : (0 : ℝ) ≤ M.gamma *
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216) := by positivity
      nlinarith [this]
    have hfac0 : 0 ≤ 4 * ((2018618 : ℝ) / 1000000 + M.gamma *
        ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) := le_trans (by norm_num) hfac
    calc
      1 = 1 * 1 := by ring
      _ ≤ (4 * ((2018618 : ℝ) / 1000000 + M.gamma *
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216))) *
          (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ)) :=
        mul_le_mul hfac hpow (by norm_num) hfac0
  have hC0 : 0 ≤ C := le_trans (by norm_num) hCge
  have hfCap0 : 0 ≤ fCap := le_trans (by norm_num) hfCapge
  have hJ : q + (s : ℤ) = m + 1 := by
    dsimp [q, s]
    omega
  rw [← hJ]
  change v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
      2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
      (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap) ≤
    v * (120 * C + (67 / 1000 : ℝ) * C ^ 2 * fCap)
  have hterm1 : (78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) ≤ 120 * C := by
    have hκ' : 78 + 76 * κ ≤ 79 := by nlinarith [hκ]
    calc
      _ ≤ 79 * (C * (3683 / 2500 : ℝ)) :=
        mul_le_mul_of_nonneg_right hκ' (mul_nonneg hC0 (by norm_num))
      _ ≤ 79 * (C * (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ hC0) (by norm_num)
      _ ≤ 120 * C := by nlinarith [hC0]
  have hterm2 : 2 * κ * (C * (3683 / 2500 : ℝ)) * fCap ≤
      (1 / 1000 : ℝ) * C ^ 2 * fCap := by
    have hκ' : 2 * κ ≤ 1 / 2500 := by nlinarith [hκ]
    have hCsq : C ≤ C ^ 2 := by nlinarith [hCge]
    have hCmul : C * fCap ≤ C ^ 2 * fCap :=
      mul_le_mul_of_nonneg_right hCsq hfCap0
    calc
      _ ≤ (1 / 2500 : ℝ) * (C * (3683 / 2500 : ℝ)) * fCap := by
        gcongr
      _ ≤ (1 / 2500 : ℝ) * (C * (3 / 2 : ℝ)) * fCap := by
        gcongr
      _ ≤ (1 / 1000 : ℝ) * C ^ 2 * fCap := by
        calc
          _ = (3 / 5000 : ℝ) * C * fCap := by ring
          _ = (3 / 5000 : ℝ) * (C * fCap) := by ring
          _ ≤ (3 / 5000 : ℝ) * (C ^ 2 * fCap) :=
            mul_le_mul_of_nonneg_left hCmul (by norm_num)
          _ = (3 / 5000 : ℝ) * C ^ 2 * fCap := by ring
          _ ≤ (1 / 1000 : ℝ) * C ^ 2 * fCap := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by norm_num : (3 / 5000 : ℝ) ≤ 1 / 1000)
                (sq_nonneg C)) hfCap0
  have hterm3 : (μR + 38 * (κB ^ 2 + κ)) *
      (C * (3683 / 2500 : ℝ)) ^ 2 * fCap ≤
        (66 / 1000 : ℝ) * C ^ 2 * fCap := by
    have hinner : μR + 38 * (κB ^ 2 + κ) ≤ 29 / 1000 := by
      have hκBsq : κB ^ 2 ≤ (21 / 1000 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hκB0 hκB 2
      nlinarith [hκBsq, hκ]
    have hCβ : C * (3683 / 2500 : ℝ) ≤ C * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hβ hC0
    have hCβ0 : 0 ≤ C * (3683 / 2500 : ℝ) := by positivity
    have hCβ'0 : 0 ≤ C * (3 / 2 : ℝ) := by positivity
    have hsquare : (C * (3683 / 2500 : ℝ)) ^ 2 ≤
        (C * (3 / 2 : ℝ)) ^ 2 := (sq_le_sq₀ hCβ0 hCβ'0).mpr hCβ
    calc
      _ ≤ (29 / 1000 : ℝ) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap := by
        gcongr
      _ ≤ (29 / 1000 : ℝ) * (C * (3 / 2 : ℝ)) ^ 2 * fCap := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hfCap0
      _ = (29 / 1000 : ℝ) * (C ^ 2 * (3 / 2 : ℝ) ^ 2) * fCap := by ring
      _ ≤ (66 / 1000 : ℝ) * C ^ 2 * fCap := by
        have hconst : (29 / 1000 : ℝ) * (3 / 2 : ℝ) ^ 2 ≤ 66 / 1000 := by norm_num
        calc
          _ = ((29 / 1000 : ℝ) * (3 / 2 : ℝ) ^ 2) * C ^ 2 * fCap := by ring
          _ ≤ (66 / 1000 : ℝ) * C ^ 2 * fCap :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst (sq_nonneg C)) hfCap0
  have hinside :
      (78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
        2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
        (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap ≤
          120 * C + (67 / 1000 : ℝ) * C ^ 2 * fCap := by
    linarith [hterm1, hterm2, hterm3]
  exact mul_le_mul_of_nonneg_left hinside (by
    dsimp [v]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The inverse-history-discounted fixed-OLD-frame generator control is at
most `10000 * gamma`. -/
theorem main_rawShell_fixed_old_frame_p20_control_discounted_linear_gamma_bound
    (M : ABKModel 2) (h : ℝ)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) :
    (1 - mainAlpha) * ∑' j : ℕ,
      mainAlpha ^ j * mainRawShellOldFrameP20Control M h m j ≤
        10000 * M.gamma := by
  let gamma : ℝ := M.gamma
  let r0 : ℝ := mainAlpha * (3 : ℝ) ^ (2 * gamma)
  let r1 : ℝ := mainAlpha * (3 : ℝ) ^ (8 * gamma)
  let a : ℝ := mainRawA gamma
  let b : ℝ := mainRawS gamma
  let baseCoeff : ℝ := 540 * gamma * (3 : ℝ) ^ (12 * gamma)
  let nonlinearCoeff : ℝ := (603 / 500 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma)
  let majorant : ℕ → ℝ := fun j =>
    baseCoeff * r0 ^ j + nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j
  have hgamma0 : 0 ≤ gamma := by
    dsimp [gamma]
    exact M.shellPrefix.gamma_pos.le
  have hcaps := main_rawShell_fixed_old_frame_p20_discount_caps gamma hgamma0
    (by simpa [gamma] using hgamma)
  rcases hcaps with ⟨hAlphaLow, hAlphaOne, hr0, hr0le, hr1, hr1le,
    hpow12, hpow48, ha, hb⟩
  have halpha0 : 0 ≤ mainAlpha := by linarith
  have hweight : 0 ≤ 1 - mainAlpha ∧ 1 - mainAlpha ≤ 1 / 4 := by
    constructor <;> linarith
  have hr0norm : ‖r0‖ < 1 := by
    rw [Real.norm_of_nonneg hr0]
    linarith
  have hr1norm : ‖r1‖ < 1 := by
    rw [Real.norm_of_nonneg hr1]
    linarith
  have hgeo0 := hasSum_geometric_of_norm_lt_one hr0norm
  have hgeo1 := hasSum_geometric_of_norm_lt_one hr1norm
  have hlinear1 := hasSum_coe_mul_geometric_of_norm_lt_one hr1norm
  have hpolySummable : Summable (fun j : ℕ =>
      (a + b * (j : ℝ)) * r1 ^ j) := by
    have hpoint (j : ℕ) :
        (a + b * (j : ℝ)) * r1 ^ j =
          a * r1 ^ j + b * ((j : ℝ) * r1 ^ j) := by ring
    have heq : (fun j : ℕ => (a + b * (j : ℝ)) * r1 ^ j) =
        fun j : ℕ => a * r1 ^ j + b * ((j : ℝ) * r1 ^ j) := by
      funext j
      exact hpoint j
    rw [heq]
    exact (hgeo1.summable.mul_left a).add (hlinear1.summable.mul_left b)
  have hbaseSummable : Summable (fun j : ℕ => baseCoeff * r0 ^ j) :=
    hgeo0.summable.mul_left baseCoeff
  have hnonlinearSummable : Summable (fun j : ℕ =>
      nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j) := by
    have hs := hpolySummable.mul_left nonlinearCoeff
    simpa only [mul_assoc] using hs
  have hmajorSummable : Summable majorant := by
    simpa only [majorant] using hbaseSummable.add hnonlinearSummable
  have hweightedSummable : Summable (fun j : ℕ =>
      mainAlpha ^ j * mainRawShellOldFrameP20Control M h m j) := by
    simpa [mainAlpha, Scalar.inverseHistoryDiscount] using
      main_rawShell_fixed_old_frame_p20_control_discounted_summable M h m hgamma
  have hpow12eq : (3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (10 * gamma) =
      (3 : ℝ) ^ (12 * gamma) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hpow48eq : (3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (46 * gamma) =
      (3 : ℝ) ^ (48 * gamma) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hpointwise (j : ℕ) :
      mainAlpha ^ j * mainRawShellOldFrameP20Control M h m j ≤ majorant j := by
    let q : ℤ := m - ((5 + j : ℕ) : ℤ)
    let s : ℕ := 6 + j
    let J : ℤ := q + (s : ℤ)
    have hJ : J = m + 1 := by dsimp [J, q, s]; omega
    have hqs : q + (s : ℤ) = m + 1 := hJ
    have hstate : nativeInductionState M h m := hpast m (le_rfl)
    have hvariance := main_rawShell_fixed_old_frame_p20_shell_variance_clock
      M h m q s hqs hstate
    have hV : (q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2 ≤
          (9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) := by
      simpa only [hqs, gamma] using hvariance
    have hlinear := main_rawShell_fixed_old_frame_p20_control_linear_clock_bound M h m j
    let C := rawTraceOldFrameP20LocalClock gamma (6 + j)
    let F := rawTraceOldFrameP20FullResponseCap gamma (6 + j)
    have hCformula : C = (3 : ℝ) ^ (10 * gamma) * ((3 : ℝ) ^ (2 * gamma)) ^ j := by
      dsimp [C, rawTraceOldFrameP20LocalClock]
      have hs : ((6 + j : ℕ) : ℝ) = 6 + (j : ℝ) := by push_cast; ring
      rw [hs]
      have hexp : 2 * gamma * (6 + (j : ℝ) - 1) =
          10 * gamma + (2 * gamma) * (j : ℝ) := by ring
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    have hcoef : (2018618 : ℝ) / 1000000 + gamma *
        (32474 * ((j + 7 : ℕ) : ℝ) + 11483216) = a + b * (j : ℝ) := by
      dsimp [a, b, gamma, mainRawA, mainRawS]
      push_cast
      ring
    have hprod : C ^ 2 * F =
        4 * (a + b * (j : ℝ)) * (3 : ℝ) ^ (46 * gamma) *
          ((3 : ℝ) ^ (8 * gamma)) ^ j := by
      calc
        _ = 4 * ((2018618 : ℝ) / 1000000 + M.gamma *
            (32474 * ((j + 7 : ℕ) : ℝ) + 11483216)) *
            (3 : ℝ) ^ (46 * M.gamma) * ((3 : ℝ) ^ (8 * M.gamma)) ^ j := by
          dsimp [C, F, gamma]
          exact main_rawShell_old_frame_p20_clock_response_product M.gamma j
        _ = 4 * (a + b * (j : ℝ)) * (3 : ℝ) ^ (46 * gamma) *
            ((3 : ℝ) ^ (8 * gamma)) ^ j := by
          rw [hcoef]
    have hcontrol : mainRawShellOldFrameP20Control M h m j ≤
        ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma)) *
          (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F) := by
      have hCpos : 0 ≤ C := by
        dsimp [C, rawTraceOldFrameP20LocalClock]
        positivity
      have hFpos : 0 ≤ F := by
        dsimp [F, rawTraceOldFrameP20FullResponseCap]
        positivity
      have hcoeff0 : 0 ≤ 120 * C + (67 / 1000 : ℝ) * C ^ 2 * F := by positivity
      calc
        _ ≤ ((q3ModelAmplitude M h (m + 1)) ^ 2 /
              (Annealed.sigmaBar M m : ℝ) ^ 2) *
              (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F) := by
          simpa only [C, F, gamma] using hlinear
        _ ≤ _ := mul_le_mul_of_nonneg_right hV hcoeff0
    calc
      _ ≤ mainAlpha ^ j * (((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma)) *
          (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F)) :=
        mul_le_mul_of_nonneg_left hcontrol (pow_nonneg halpha0 j)
      _ = majorant j := by
        change mainAlpha ^ j * (((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma)) *
            (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F)) =
          baseCoeff * r0 ^ j + nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j
        have hscaledProd : (67 / 1000 : ℝ) * C ^ 2 * F =
            (67 / 250 : ℝ) * (a + b * (j : ℝ)) *
              (3 : ℝ) ^ (46 * gamma) * ((3 : ℝ) ^ (8 * gamma)) ^ j := by
          rw [mul_assoc, hprod]
          ring
        have hbaseTerm :
            mainAlpha ^ j * ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
              (120 * ((3 : ℝ) ^ (10 * gamma) *
                ((3 : ℝ) ^ (2 * gamma)) ^ j))) =
              540 * gamma * (3 : ℝ) ^ (12 * gamma) *
                (mainAlpha * (3 : ℝ) ^ (2 * gamma)) ^ j := by
          calc
            _ = 540 * gamma * ((3 : ℝ) ^ (2 * gamma) *
                (3 : ℝ) ^ (10 * gamma)) *
                (mainAlpha ^ j * ((3 : ℝ) ^ (2 * gamma)) ^ j) := by
              ring
            _ = 540 * gamma * (3 : ℝ) ^ (12 * gamma) *
                (mainAlpha ^ j * ((3 : ℝ) ^ (2 * gamma)) ^ j) := by
              rw [hpow12eq]
            _ = _ := by rw [← mul_pow]
        have hnonlinearTerm :
            mainAlpha ^ j * ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
              ((67 / 250 : ℝ) * (a + b * (j : ℝ)) * (3 : ℝ) ^ (46 * gamma) *
                ((3 : ℝ) ^ (8 * gamma)) ^ j)) =
              (603 / 500 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma) *
                (a + b * (j : ℝ)) *
                  (mainAlpha * (3 : ℝ) ^ (8 * gamma)) ^ j := by
          calc
            _ = (603 / 500 : ℝ) * gamma *
                ((3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (46 * gamma)) *
                (a + b * (j : ℝ)) *
                  (mainAlpha ^ j * ((3 : ℝ) ^ (8 * gamma)) ^ j) := by
              ring
            _ = (603 / 500 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma) *
                (a + b * (j : ℝ)) *
                  (mainAlpha ^ j * ((3 : ℝ) ^ (8 * gamma)) ^ j) := by
              rw [hpow48eq]
            _ = _ := by rw [← mul_pow]
        rw [hscaledProd, hCformula]
        dsimp [baseCoeff, nonlinearCoeff, r0, r1]
        calc
          _ = mainAlpha ^ j * ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
                (120 * ((3 : ℝ) ^ (10 * gamma) *
                  ((3 : ℝ) ^ (2 * gamma)) ^ j))) +
              mainAlpha ^ j * ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
                ((67 / 250 : ℝ) * (a + b * (j : ℝ)) *
                  (3 : ℝ) ^ (46 * gamma) *
                    ((3 : ℝ) ^ (8 * gamma)) ^ j)) := by ring
          _ = _ := by rw [hbaseTerm, hnonlinearTerm]
  have hpolySum : ∑' j : ℕ, (a + b * (j : ℝ)) * r1 ^ j =
      a / (1 - r1) + b * (r1 / (1 - r1) ^ 2) := by
    calc
      _ = ∑' j : ℕ, (a * r1 ^ j + b * ((j : ℝ) * r1 ^ j)) := by
        apply tsum_congr
        intro j
        ring
      _ = (∑' j : ℕ, a * r1 ^ j) +
          (∑' j : ℕ, b * ((j : ℝ) * r1 ^ j)) :=
        ((hgeo1.summable.mul_left a).tsum_add
          (hlinear1.summable.mul_left b))
      _ = a / (1 - r1) + b * (r1 / (1 - r1) ^ 2) := by
        rw [tsum_mul_left, hgeo1.tsum_eq, tsum_mul_left, hlinear1.tsum_eq]
        ring
  have hsumMajorant : ∑' j : ℕ, majorant j =
      baseCoeff / (1 - r0) + nonlinearCoeff *
        (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) := by
    calc
      _ = (∑' j : ℕ, baseCoeff * r0 ^ j) +
          (∑' j : ℕ, nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j) := by
        dsimp [majorant]
        exact hbaseSummable.tsum_add hnonlinearSummable
      _ = baseCoeff / (1 - r0) + nonlinearCoeff *
          (∑' j : ℕ, (a + b * (j : ℝ)) * r1 ^ j) := by
        rw [tsum_mul_left, hgeo0.tsum_eq]
        congr 1
        calc
          _ = ∑' j : ℕ, nonlinearCoeff *
              ((a + b * (j : ℝ)) * r1 ^ j) := by
            apply tsum_congr
            intro j
            ring
          _ = nonlinearCoeff *
              (∑' j : ℕ, (a + b * (j : ℝ)) * r1 ^ j) := tsum_mul_left
      _ = _ := by rw [hpolySum]
  have hgap0 : (19 / 100 : ℝ) ≤ 1 - r0 := by linarith
  have hgap1 : (19 / 100 : ℝ) ≤ 1 - r1 := by linarith
  have hratio0 : (1 - mainAlpha) / (1 - r0) ≤ 4 / 3 := by
    apply (div_le_iff₀ (by linarith [hgap0])).2
    nlinarith [hweight.2, hgap0]
  have hbaseCoeff : baseCoeff ≤ 720 * gamma := by
    dsimp [baseCoeff]
    calc
      _ ≤ 540 * gamma * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow12 (by positivity)
      _ = 720 * gamma := by ring
  have hbase : (1 - mainAlpha) * (baseCoeff / (1 - r0)) ≤
      960 * gamma := by
    have hratio0nonneg : 0 ≤ (1 - mainAlpha) / (1 - r0) :=
      div_nonneg hweight.1 (by linarith [hgap0])
    have hbaseCoeff0 : 0 ≤ baseCoeff := by dsimp [baseCoeff]; positivity
    have hmul := mul_le_mul hratio0 hbaseCoeff hbaseCoeff0 (by positivity)
    have heq : (1 - mainAlpha) * (baseCoeff / (1 - r0)) =
        ((1 - mainAlpha) / (1 - r0)) * baseCoeff := by
      field_simp
    rw [heq]
    nlinarith [hmul]
  have hinv1 : 0 ≤ (1 - r1)⁻¹ := by positivity
  have hinv1le : (1 - r1)⁻¹ ≤ 100 / 19 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 19 / 100) hgap1
    simpa using h
  have hinv1sq : ((1 - r1)⁻¹) ^ 2 ≤ (100 / 19 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hinv1 hinv1le 2
  have ha0 : 0 ≤ a := by dsimp [a, mainRawA]; positivity
  have hb0 : 0 ≤ b := by dsimp [b, mainRawS]; positivity
  have hpoly0 : 0 ≤ a / (1 - r1) + b * (r1 / (1 - r1) ^ 2) := by
    positivity
  have htermA : a / (1 - r1) ≤ 4000 * (100 / 19 : ℝ) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul ha hinv1le (by positivity) (by positivity)
  have hbr : b * r1 ≤ 12 * (81 / 100 : ℝ) :=
    mul_le_mul hb hr1le (by positivity) (by positivity)
  have htermB : b * (r1 / (1 - r1) ^ 2) ≤
      12 * (81 / 100 : ℝ) * (100 / 19 : ℝ) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      _ = (b * r1) * ((1 - r1)⁻¹) ^ 2 := by ring
      _ ≤ (12 * (81 / 100 : ℝ)) * (100 / 19 : ℝ) ^ 2 :=
        mul_le_mul hbr hinv1sq (by positivity) (by positivity)
  have hpolyUpper : a / (1 - r1) + b * (r1 / (1 - r1) ^ 2) ≤ 22000 := by
    linarith [htermA, htermB]
  have hratioPoly : (1 - mainAlpha) *
      (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) ≤ 5500 := by
    calc
      _ ≤ (1 / 4 : ℝ) *
          (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) :=
        mul_le_mul_of_nonneg_right hweight.2 hpoly0
      _ ≤ 5500 := by nlinarith [hpolyUpper]
  have hnonlinearCoeff : nonlinearCoeff ≤ (201 / 125 : ℝ) * gamma := by
    dsimp [nonlinearCoeff]
    calc
      _ ≤ (603 / 500 : ℝ) * gamma * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow48 (by positivity)
      _ = (201 / 125 : ℝ) * gamma := by ring
  have hnonlinear : (1 - mainAlpha) * nonlinearCoeff *
      (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) ≤ 8844 * gamma := by
    have hnonlinear0 : 0 ≤ nonlinearCoeff := by
      dsimp [nonlinearCoeff]
      positivity
    have hratioPoly0 : 0 ≤ (1 - mainAlpha) *
        (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) :=
      mul_nonneg hweight.1 hpoly0
    calc
      _ = nonlinearCoeff * ((1 - mainAlpha) *
          (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2))) := by ring
      _ ≤ ((201 / 125 : ℝ) * gamma) * ((1 - mainAlpha) *
          (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2))) :=
        mul_le_mul_of_nonneg_right hnonlinearCoeff hratioPoly0
      _ ≤ ((201 / 125 : ℝ) * gamma) * 5500 :=
        mul_le_mul_of_nonneg_left hratioPoly (by positivity)
      _ = 8844 * gamma := by ring
  have hsumMajor :
      (1 - mainAlpha) * (∑' j : ℕ, majorant j) ≤ 10000 * gamma := by
    calc
      _ = (1 - mainAlpha) * (baseCoeff / (1 - r0)) +
          (1 - mainAlpha) * (nonlinearCoeff *
            (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2))) := by
        rw [hsumMajorant, mul_add]
      _ = (1 - mainAlpha) * (baseCoeff / (1 - r0)) +
          ((1 - mainAlpha) * nonlinearCoeff) *
            (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) := by ring
      _ ≤ 960 * gamma + 8844 * gamma := add_le_add hbase hnonlinear
      _ ≤ 10000 * gamma := by nlinarith [hgamma0]
  have hsumControl :
      (1 - mainAlpha) *
        ∑' j : ℕ, mainAlpha ^ j *
          mainRawShellOldFrameP20Control M h m j ≤
        (1 - mainAlpha) * (∑' j : ℕ, majorant j) := by
    exact mul_le_mul_of_nonneg_left
      (hweightedSummable.tsum_le_tsum hpointwise hmajorSummable) hweight.1
  exact hsumControl.trans hsumMajor

private theorem main_envelopeH_base_ge_one : 1 ≤ mainH0 := by
  let r : ℝ := (3 : ℝ) ^ (3 / 4 : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr4 : r ^ 4 = 27 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hr : (4 / 3 : ℝ) ≤ r := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hr0
      (by norm_num : (4 : ℕ) ≠ 0)).1
    rw [hr4]
    norm_num
  unfold mainH0
  calc
    1 ≤ (4 / 3 : ℝ) * (2379 / 2500 : ℝ) := by norm_num
    _ ≤ r * (2379 / 2500 : ℝ) :=
      mul_le_mul_of_nonneg_right hr (by norm_num)

private theorem main_envelopeH_source_cross_factor_ge :
    (5 / 4 : ℝ) ≤
      (3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
        (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld := by
  let r : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr4 : r ^ 4 = 3 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hr : (5 / 4 : ℝ) ≤ r := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hr0
      (by norm_num : (4 : ℕ) ≠ 0)).1
    rw [hr4]
    norm_num
  have hbeta : 1 ≤ mainBetaOld := by norm_num [mainBetaOld]
  have hbeta0 : 0 ≤ mainBetaOld := le_trans (by norm_num) hbeta
  have hbetaSqrt : (1 : ℝ) ≤ Real.sqrt mainBetaOld :=
    (Real.le_sqrt (by norm_num) hbeta0).2 (by nlinarith [hbeta])
  have hfirst : (5 / 4 : ℝ) ≤ r * Real.sqrt mainBetaOld := by
    calc
      _ = (5 / 4 : ℝ) * 1 := by ring
      _ ≤ r * Real.sqrt mainBetaOld :=
        mul_le_mul hr hbetaSqrt (by norm_num) (by positivity)
  have hsecond : 0 ≤ (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld := by
    positivity
  dsimp [r] at hfirst
  exact hfirst.trans (le_add_of_nonneg_right hsecond)

/-- The fixed-time OLD weak-trace history is bounded by the exact frozen
source `mainEnvelopeH`; its depthwise generator is instantiated
fixed-frame raw-shell producer. -/
theorem main_rawWeakTraceHistory_lpNorm_le_mainEnvelopeH_of_fixed_old_frame_state_strong20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M)) :
    ∃ hT : ∀ j : ℕ,
      MemLp (rawWeakTraceSequence M m (originCube 2 (m - 5)) t · j) 2
        (Cutoff.cutoffSampleLaw M).toMeasure,
      ‖rawWeakTraceHistoryLp M m (originCube 2 (m - 5)) t hT‖ ≤
        mainEnvelopeH (theta M) M.gamma t := by
  obtain ⟨hT, hhistory⟩ :=
    main_rawWeakTraceHistory_lpNorm_le_of_fixed_old_frame_state_strong20
      M m h hM hgamma hpast t ht0 ht1 hstrong
  have hcontrol :=
    main_rawShell_fixed_old_frame_p20_control_discounted_linear_gamma_bound
      M h hgamma m hpast
  have hgammaTheta : 10000 * M.gamma = (17 / 5 : ℝ) * theta M := by
    rw [theta]
    field_simp [gammaZero]
    norm_num [gammaZero]
    ring
  have hsourceControl :
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          mainRawShellOldFrameP20Control M h m j ≤
        (17 / 5 : ℝ) * theta M := by
    calc
      _ = (1 - mainAlpha) *
          ∑' j : ℕ, mainAlpha ^ j * mainRawShellOldFrameP20Control M h m j := by
        simp [mainAlpha, Scalar.inverseHistoryDiscount]
      _ ≤ 10000 * M.gamma := hcontrol
      _ = (17 / 5 : ℝ) * theta M := hgammaTheta
  have htheta0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  have htheta1 : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hgamma
  let x : ℝ := theta M * t
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    calc
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right htheta1 ht0
      _ = t := by ring
      _ ≤ 1 := ht1
  have hxsqrt : x ≤ Real.sqrt x := by
    apply (Real.le_sqrt hx0 hx0).2
    nlinarith [hx1]
  have hdelta0 : 0 ≤ mainDeltaH (theta M) M.gamma := by
    rw [mainDeltaH_eq_depth_tsum (theta M) M.gamma
      M.shellPrefix.gamma_pos.le hgamma]
    have hrows : ∀ j : ℕ, 0 ≤ mainEnvelopeHDepthGeneratorRow
        (theta M) M.gamma j := by
      intro j
      exact mainEnvelopeHDepthGeneratorRow_nonneg htheta0
        M.shellPrefix.gamma_pos.le hgamma j
    exact mul_nonneg
      (sub_nonneg.mpr (by
        dsimp [mainAlpha]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by norm_num) (by norm_num)))
      (tsum_nonneg hrows)
  have hrad0 : 1 ≤ Real.sqrt
      (mainH0 + mainDeltaH (theta M) M.gamma * t) := by
    have hdt : 0 ≤ mainDeltaH (theta M) M.gamma * t :=
      mul_nonneg hdelta0 ht0
    have hradarg0 : 0 ≤ mainH0 + mainDeltaH (theta M) M.gamma * t :=
      add_nonneg (le_trans (by norm_num) main_envelopeH_base_ge_one) hdt
    apply (Real.le_sqrt (by norm_num) hradarg0).2
    nlinarith [main_envelopeH_base_ge_one]
  have hcrossC := main_envelopeH_source_cross_factor_ge
  have hsqrt2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hfactor : (7 / 4 : ℝ) ≤ Real.sqrt 2 *
      ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
        (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by
    calc
      _ = (7 / 5 : ℝ) * (5 / 4 : ℝ) := by ring
      _ ≤ _ := mul_le_mul hsqrt2 hcrossC (by norm_num) (by positivity)
  have hsourceSqrt : (7 / 4 : ℝ) * Real.sqrt x ≤
      Real.sqrt (2 * theta M * t) *
        ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
          (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by
    rw [show 2 * theta M * t = 2 * x by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (Real.sqrt 2 *
          ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
            (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) *
            Real.sqrt x :=
          mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg x)
      _ = _ := by ring
  have hcross : (7 / 2 : ℝ) * Real.sqrt x ≤
      2 * Real.sqrt (mainH0 + mainDeltaH (theta M) M.gamma * t) *
        Real.sqrt (2 * theta M * t) *
          ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
            (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by
    have hprod : Real.sqrt (2 * theta M * t) *
        ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
          (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) ≤
        Real.sqrt (mainH0 + mainDeltaH (theta M) M.gamma * t) *
          Real.sqrt (2 * theta M * t) *
            ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
              (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by
      have hsourceTerm0 : 0 ≤ Real.sqrt (2 * theta M * t) *
          ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
            (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by
        positivity
      calc
        _ = 1 * (Real.sqrt (2 * theta M * t) *
            ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
              (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) := by ring
        _ ≤ _ := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_right hrad0 hsourceTerm0)
    calc
      _ = 2 * ((7 / 4 : ℝ) * Real.sqrt x) := by ring
      _ ≤ 2 * (Real.sqrt (2 * theta M * t) *
          ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
            (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) :=
        mul_le_mul_of_nonneg_left hsourceSqrt (by norm_num)
      _ ≤ 2 * (Real.sqrt (mainH0 + mainDeltaH (theta M) M.gamma * t) *
          Real.sqrt (2 * theta M * t) *
            ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
              (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = _ := by ring
  have hEnvelopeLower : mainH0 + (7 / 2 : ℝ) * Real.sqrt x ≤
      mainEnvelopeH (theta M) M.gamma t := by
    let A := Real.sqrt (mainH0 + mainDeltaH (theta M) M.gamma * t)
    let B := Real.sqrt (2 * theta M * t) *
      ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
        (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)
    have hAsq : A ^ 2 = mainH0 + mainDeltaH (theta M) M.gamma * t := by
      dsimp [A]
      have hradarg0 : 0 ≤ mainH0 + mainDeltaH (theta M) M.gamma * t :=
        add_nonneg (le_trans (by norm_num) main_envelopeH_base_ge_one)
          (mul_nonneg hdelta0 ht0)
      rw [Real.sq_sqrt hradarg0]
    have hcrossAB : (7 / 2 : ℝ) * Real.sqrt x ≤ 2 * A * B := by
      simpa only [A, B, mul_assoc] using hcross
    calc
      _ ≤ A ^ 2 + 2 * A * B := by nlinarith [hAsq, hdelta0, ht0, hcrossAB]
      _ ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg B]
      _ = mainEnvelopeH (theta M) M.gamma t := by
        dsimp [A, B, mainEnvelopeH]
  have hcontrolTime : t * ((17 / 5 : ℝ) * theta M) ≤
      (7 / 2 : ℝ) * Real.sqrt x := by
    have hxt : (17 / 5 : ℝ) * x ≤ (7 / 2 : ℝ) * Real.sqrt x := by
      nlinarith [hxsqrt, hx0]
    calc
      _ = (17 / 5 : ℝ) * x := by dsimp [x]; ring
      _ ≤ _ := hxt
  have hhistory' :
      ‖rawWeakTraceHistoryLp M m (originCube 2 (m - 5)) t hT‖ ≤
        mainH0 + (7 / 2 : ℝ) * Real.sqrt x := by
    calc
      _ ≤ mainH0 + t *
          ((1 - Scalar.inverseHistoryDiscount) *
            ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
              mainRawShellOldFrameP20Control M h m j) := hhistory
      _ ≤ mainH0 + t * ((17 / 5 : ℝ) * theta M) :=
        add_le_add (le_rfl) (mul_le_mul_of_nonneg_left hsourceControl ht0)
      _ ≤ _ := add_le_add (le_rfl) hcontrolTime
  exact ⟨hT, hhistory'.trans hEnvelopeLower⟩

end ASDExplicitGamma.Main

end
