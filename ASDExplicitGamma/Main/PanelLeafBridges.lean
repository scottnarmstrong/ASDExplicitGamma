module

public import ASDExplicitGamma.Main.PanelLeafPrimitives
public import ASDExplicitGamma.Main.InverseLowerAlgebra
public import ASDExplicitGamma.Main.LoadsAndSlopes

/-! MA-PANEL-ENCLOSURE leaf bridges (L1) and (L2): the certificate's absolute-inverse tree and the
mean and weighted-history transport slopes, evaluated at `γ₀` and `v̄`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror
  ASDExplicitGamma.Numerics.MainReturnCertificate

local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

noncomputable section

theorem leaf_pKb (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pKb = mainKb panelVbar := by
  simp [pKb, eval_esum, evalReal, ec, mainKb, leaf_pA2, leaf_pA4, leaf_pV]
  norm_num <;> ring_nf

theorem mainInverseKA_eq_mainKa (v : ℝ) : mainInverseKA v = mainKa v := by
  simp [mainInverseKA, mainKa, mainInverseA2, mainInverseA4, mainA2, mainA4, div_eq_mul_inv,
    zpow_neg]

theorem mainInverseKB_eq_mainKb (v : ℝ) : mainInverseKB v = mainKb v := by
  simp [mainInverseKB, mainKb, mainInverseA2, mainInverseA4, mainA2, mainA4, div_eq_mul_inv,
    zpow_neg]

theorem leaf_pMuMin (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pMuMin = mainInverseMuMinusSource panelVbar := by
  have ha := leaf_pKa d s f
  have hb := leaf_pKb d s f
  simp only [pMuMin, pDfb, evalReal, eval_epow, ec, ha, hb, mainInverseMuMinusSource,
    mainInverseMuMinus, mainInverseKA_eq_mainKa, mainInverseKB_eq_mainKb]
  norm_num

theorem leaf_pRareRatio (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pRareRatio = mainRho := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  simp only [pRareRatio, evalReal, eval_epow, cb, cen, ec, mainRho, mainEpsNew, mainBeta]
  push_cast
  ring

/-- (L1) The certificate's absolute-inverse tree is `mainInverseAbs`. -/
theorem leaf_inverseAbsolute (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) inverseAbsoluteExpr =
      mainInverseAbs panelVbar (mainInverseMuMinusSource panelVbar) s := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  simp only [inverseAbsoluteExpr, pInverseAbsolute, pKappa, evalReal, eval_epow,
    leaf_pMuMin, leaf_pRareRatio, leaf_pV, cb, cs, ec, mainInverseAbs, mainKappa]
  norm_num


/-! ### (L2) the transport slopes -/

theorem leaf_sqrt3 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pSqrt3 = Real.sqrt 3 := by
  simp [pSqrt3, evalReal, ec]

theorem leaf_pRawFactor (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pRawFactor = mainRawFactor gammaZero := by
  simp [pRawFactor, mainRawFactor, evalReal, ec, pLog3, ev, panelRealEnv, gammaZero,
    exp_mul_log_three]
  norm_num

theorem leaf_pPa0 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pPa0 = mainPa panelVbar 0 := by
  simp [pPa0, mainPa, evalReal, ec, leaf_pA2]

theorem leaf_pPa1 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pPa1 = mainPa panelVbar 1 := by
  simp [pPa1, mainPa, evalReal, ec, leaf_pA2]

theorem leaf_pPa2 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pPa2 = mainPa panelVbar 2 := by
  simp [pPa2, mainPa, evalReal, ec, leaf_pA4]

theorem leaf_pKf (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pKf = mainKf panelVbar := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  simp [pKf, eval_esum, evalReal, ec, mainKf, leaf_pA2, c2]
  try ring_nf
  try simp

theorem leaf_pJ0 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pJ0 = mainJ0 panelVbar gammaZero := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  simp [pJ0, eval_esum, eval_epow, evalReal, ec, mainJ0, cbo, leaf_pRawFactor,
    leaf_pRawA, leaf_pV, leaf_sqrt3]
  try ring_nf
  try simp

theorem leaf_pKj0 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pKj0 = mainK0 panelVbar gammaZero := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  simp [pKj0, eval_esum, eval_epow, evalReal, ec, mainK0, cbo, leaf_pRawFactor,
    leaf_pRawA, leaf_pV, leaf_sqrt3]
  try ring_nf
  try simp

/-- (L2a) The mean slope tree is `mainMu`. -/
theorem leaf_pMeanSlope (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pMeanSlope = mainMu panelVbar gammaZero := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  simp [pMeanSlope, pPaSum, eval_esum, eval_epow, evalReal, ec, mainMu, leaf_pPa0,
    leaf_pPa1, leaf_pPa2, leaf_pJ0, leaf_pKf, leaf_pKj0, leaf_pV, cbo, ceo, leaf_sqrt3]
  ring_nf


theorem growth_pow_eq (g n : ℕ) :
    (3 : ℝ) ^ ((g : ℝ) * 17 / 50000) * (1 / (3 : ℝ) ^ n) =
      (3 : ℝ) ^ ((g : ℝ) * gammaZero - (n : ℝ)) := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, gammaZero]
  have : (g : ℝ) * (17 / 50000) = (g : ℝ) * 17 / 50000 := by ring
  rw [this]
  ring

theorem leaf_pWeightedGeo (d : PanelRealData) (s f : ℝ) (g n : ℕ) :
    evalReal (panelRealEnv d s f) (pWeightedGeo g n) = mainW gammaZero (g : ℝ) n := by
  have h := growth_pow_eq g n
  simp only [pWeightedGeo, pGeo, pPow3Inv, evalReal, eval_epow, ec, leaf_pAlpha, pLog3, ev,
    panelRealEnv, mainW]
  have e1 : Real.exp (((g * 17 / 50000 : ℚ) : ℝ) * Real.log 3) = (3 : ℝ) ^ ((g : ℝ) * 17 / 50000) := by
    rw [exp_mul_log_three]; push_cast; rfl
  have e2 : (((1 / (3 : ℚ) ^ n : ℚ)) : ℝ) = 1 / (3 : ℝ) ^ n := by push_cast; rfl
  simp only [ite_true, e1, e2, mul_assoc, h]
  push_cast
  ring

theorem leaf_pWeightedGeoPoly (d : PanelRealData) (s f : ℝ) (g n : ℕ) :
    evalReal (panelRealEnv d s f) (pWeightedGeoPoly g n) = mainRawW gammaZero (g : ℝ) n := by
  have h := growth_pow_eq g n
  simp only [pWeightedGeoPoly, pGeoPoly, pPow3Inv, evalReal, eval_epow, ec, leaf_pAlpha,
    pLog3, ev, panelRealEnv, mainRawW, mainRawGeo, leaf_pRawA, leaf_pRawS]
  have e1 : Real.exp (((g * 17 / 50000 : ℚ) : ℝ) * Real.log 3) = (3 : ℝ) ^ ((g : ℝ) * 17 / 50000) := by
    rw [exp_mul_log_three]; push_cast; rfl
  have e2 : (((1 / (3 : ℚ) ^ n : ℚ)) : ℝ) = 1 / (3 : ℝ) ^ n := by push_cast; rfl
  simp only [ite_true, e1, e2, mul_assoc, h]
  push_cast
  ring

/-- (L2b) The weighted-history slope tree is `mainChi`. -/
theorem leaf_pXiSlope (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pXiSlope = mainChi panelVbar gammaZero := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  have hq : ((4 * 17 / 50000 + 1 / 64 : ℚ) : ℝ) = 4 * gammaZero + 1 / 64 := by
    norm_num [gammaZero]
  have hQ : evalReal (panelRealEnv d s f) pQRare =
      mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gammaZero + 1 / 64) := by
    simp [pQRare, evalReal, eval_epow, ec, leaf_pAlpha, pLog3, ev, panelRealEnv,
      exp_mul_log_three]
    left
    congr 1
    norm_num [gammaZero]
  simp [pXiSlope, pXiCoefficientTerm, pKfXiTerm, pBetaXiTerm, pRareXiTerm, eval_esum,
    eval_epow, evalReal, ec, pMeanCoeff2, pMeanCoeff3, pMeanCoeff4, leaf_pWeightedGeo,
    leaf_pWeightedGeoPoly, leaf_pRawFactor, leaf_pPa0, leaf_pPa1, leaf_pPa2, leaf_pKf, leaf_pV,
    leaf_sqrt3, cbo, ceo, hQ, leaf_pAlpha, mainChi, mainXiCoefficients, Fin.sum_univ_three]
  norm_num
  ring_nf

end

end ASDExplicitGamma.Main
