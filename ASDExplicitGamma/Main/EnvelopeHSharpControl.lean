module

public import ASDExplicitGamma.Main.EnvelopeHSharpCaps

/-! The per-depth fixed-old-frame p = 20 control with the geometric decay `(1/9)^j`
of the nonlinear coefficient. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Algsuperdiff.Section3 MeasureTheory

/-- The abstract real inequality behind the decaying control coefficient. -/
theorem p20_inner_abstract {κ κB μR C fCap r2 w : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 46 * r2)
    (hκB2 : κB ^ 2 ≤ 217 * r2) (hμR0 : 0 ≤ μR) (hμR : μR ≤ 1600 * r2) (hC : 1 ≤ C)
    (hf : 0 ≤ fCap) (hr20 : 0 ≤ r2) (hr2le : r2 ≤ 1 / 531441) (hdecay : 26148 * r2 ≤ (1 / 20) * w) :
    (78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) + 2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
      (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap ≤
        120 * C + (1 / 20 : ℝ) * w * C ^ 2 * fCap := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hκs : κ ≤ 1 / 10000 := by nlinarith
  have hterm1 : (78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) ≤ 120 * C := by
    have : 78 + 76 * κ ≤ 79 := by nlinarith
    calc _ ≤ 79 * (C * (3683 / 2500 : ℝ)) := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 120 * C := by nlinarith
  have hCsq : C ≤ C ^ 2 := by nlinarith
  have hCmul : C * fCap ≤ C ^ 2 * fCap := mul_le_mul_of_nonneg_right hCsq hf
  have hCF : 0 ≤ C ^ 2 * fCap := by positivity
  have hterm2 : 2 * κ * (C * (3683 / 2500 : ℝ)) * fCap ≤ 138 * r2 * (C ^ 2 * fCap) := by
    have h1 : 2 * κ * (C * (3683 / 2500 : ℝ)) * fCap ≤ 2 * (46 * r2) * (C * (3683 / 2500 : ℝ)) * fCap := by
      gcongr
    calc _ ≤ _ := h1
      _ = (46 * 2 * (3683 / 2500 : ℝ)) * r2 * (C * fCap) := by ring
      _ ≤ 138 * r2 * (C * fCap) := by
        have : 0 ≤ r2 * (C * fCap) := by positivity
        nlinarith
      _ ≤ 138 * r2 * (C ^ 2 * fCap) := mul_le_mul_of_nonneg_left hCmul (by positivity)
  have hterm3 : (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap ≤
      26010 * r2 * (C ^ 2 * fCap) := by
    have hin : μR + 38 * (κB ^ 2 + κ) ≤ 11600 * r2 := by nlinarith
    have hin0 : 0 ≤ μR + 38 * (κB ^ 2 + κ) := by positivity
    calc _ ≤ (11600 * r2) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap := by gcongr
      _ = (11600 * (3683 / 2500) ^ 2) * r2 * (C ^ 2 * fCap) := by ring
      _ ≤ 26010 * r2 * (C ^ 2 * fCap) := by
        have : 0 ≤ r2 * (C ^ 2 * fCap) := by positivity
        nlinarith
  have := mul_le_mul_of_nonneg_right hdecay hCF
  nlinarith [hterm1, hterm2, hterm3, this]

/-- Per-depth control with the decaying nonlinear coefficient `(1/20) 9^(-j)`. -/
theorem main_rawShell_fixed_old_frame_p20_control_decay_bound
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) :
    mainRawShellOldFrameP20Control M h m j ≤
      ((q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2) *
        (120 * rawTraceOldFrameP20LocalClock M.gamma (6 + j) +
          (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j *
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
  have hscale := main_rawShell_fixed_old_frame_p20_source_scales q s hs
  have hrbank : pureFluxCovarianceRho 0 (s - 1) = (1 / 3 : ℝ) ^ s := by
    unfold pureFluxCovarianceRho
    congr 1
    omega
  have hr0 : 0 ≤ (1 / 3 : ℝ) ^ s := by positivity
  have hr729 : (1 / 3 : ℝ) ^ s ≤ 1 / 729 := by
    calc _ ≤ (1 / 3 : ℝ) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
      _ = 1 / 729 := by norm_num
  have hρr : ρ = (1 / 3 : ℝ) ^ s := hscale.1.trans hrbank
  have hδr : δ = (1 / 3 : ℝ) ^ s := by
    refine hscale.2.trans ?_
    unfold pureFluxCovarianceDelta
    rw [hrbank]
    exact min_eq_right (hr729.trans (by norm_num))
  have hcaps := raw_trace_caps_decay ((1 / 3 : ℝ) ^ s) hr0 hr729
  have hArB : A = rawTraceRemainderA ((1 / 3 : ℝ) ^ s) ((1 / 3 : ℝ) ^ s) := by
    dsimp [A]; rw [hrbank]; unfold pureFluxCovarianceDelta; rw [hrbank]
    rw [min_eq_right (hr729.trans (by norm_num))]
  have hBrB : B = rawTraceRemainderB ((1 / 3 : ℝ) ^ s) ((1 / 3 : ℝ) ^ s) := by
    dsimp [B]; rw [hrbank]; unfold pureFluxCovarianceDelta; rw [hrbank]
    rw [min_eq_right (hr729.trans (by norm_num))]
  have hκeq : κ = rawTraceRemainderKappaF ((1 / 3 : ℝ) ^ s) ((1 / 3 : ℝ) ^ s) := by
    dsimp [κ]; rw [hρr, hδr]
  have hκBeq : κB = rawTraceRemainderB ((1 / 3 : ℝ) ^ s) ((1 / 3 : ℝ) ^ s) := by
    dsimp [κB]; rw [hρr, hδr]
  have hμReq : μR = rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA ((1 / 3 : ℝ) ^ s) ((1 / 3 : ℝ) ^ s))
      (rawTraceRemainderB ((1 / 3 : ℝ) ^ s) ((1 / 3 : ℝ) ^ s)) := by
    dsimp [μR]; rw [hArB, hBrB]
  obtain ⟨-, -, hκB, hκB0, hκ, hκ0, hμR, hμR0⟩ := hcaps
  rw [← hκeq] at hκ hκ0
  rw [← hκBeq] at hκB hκB0
  rw [← hμReq] at hμR hμR0
  have hrsq : ((1 / 3 : ℝ) ^ s) ^ 2 = (1 / 531441 : ℝ) * (1 / 9 : ℝ) ^ j := by
    have : ((1 / 3 : ℝ) ^ s) ^ 2 = ((1 / 3 : ℝ) ^ 2) ^ s := by rw [← pow_mul, mul_comm, pow_mul]
    rw [this]
    have hs6 : s = 6 + j := rfl
    rw [hs6, pow_add]
    norm_num
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
    v * (120 * C + (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * fCap)
  have hκB2 : κB ^ 2 ≤ 217 * ((1 / 3 : ℝ) ^ s) ^ 2 := by
    have := pow_le_pow_left₀ hκB0 hκB 2
    nlinarith [sq_nonneg ((1 / 3 : ℝ) ^ s)]
  have hr2le : ((1 / 3 : ℝ) ^ s) ^ 2 ≤ 1 / 531441 := by
    rw [hrsq]
    have : (1 / 9 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hdecay : 26148 * ((1 / 3 : ℝ) ^ s) ^ 2 ≤ (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j := by
    rw [hrsq]
    have : (0 : ℝ) ≤ (1 / 9 : ℝ) ^ j := by positivity
    nlinarith
  have hinside := p20_inner_abstract hκ0 hκ hκB2 hμR0 hμR hCge hfCap0 (sq_nonneg _) hr2le hdecay
  exact mul_le_mul_of_nonneg_left hinside (by
    dsimp [v]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _))


end ASDExplicitGamma.Main
