module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Main.EnvelopeHSharpEnv
public import ASDExplicitGamma.Main.CalibratedError
public import ASDExplicitGamma.Main.ErrorCorrected
public import ASDExplicitGamma.Main.ErrorSupportCorrected

/-! MA-PANEL-ENCLOSURE: evaluation of the certificate's primitive `Expr` leaves, at `γ₀` and
`v̄ = mainSourceClock γ₀`, in the Lean definitions. -/

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

/-- The calibrated shell clock `v̄ = mainSourceClock γ₀`. -/
abbrev panelVbar : ℝ := mainSourceClock gammaZero

theorem exp_mul_log_three (c : ℝ) : Real.exp (c * Real.log 3) = (3 : ℝ) ^ c := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

theorem sqrt_sqrt_three : √(√(3 : ℝ)) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem eval_epow (env : ℕ → ℝ) (a : Expr) (n : ℕ) :
    evalReal env (epow a n) = (evalReal env a) ^ n := by
  induction n with
  | zero => simp [epow, ec, evalReal]
  | succ n ih => simp [epow, evalReal, ih, pow_succ]

theorem eval_esum (env : ℕ → ℝ) (l : List Expr) :
    evalReal env (esum l) = (l.map (evalReal env)).sum := by
  have h : ∀ (acc : Expr) (l : List Expr),
      evalReal env (l.foldl Expr.add acc) = evalReal env acc + (l.map (evalReal env)).sum := by
    intro acc l
    induction l generalizing acc with
    | nil => simp
    | cons x xs ih => simp [List.foldl, ih, evalReal]; ring
  simp [esum, h, evalReal, ec]

theorem leaf_pAlpha (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pAlpha = mainAlpha := by
  simp [pAlpha, pZ4, pSqrt3, evalReal, ec, mainAlpha, sqrt_sqrt_three]
  rw [Real.rpow_neg (by norm_num)]

theorem leaf_pBetaPrime (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pBetaPrime = mainBetaPrime := by
  simp [pBetaPrime, pLog3, ev, evalReal, ec, mainBetaPrime, panelRealEnv]
  rw [Real.rpow_neg (by norm_num), exp_mul_log_three]

theorem leaf_pRawA (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pRawA = mainRawA gammaZero := by
  simp [pRawA, pGamma, evalReal, ec, mainRawA, gammaZero]

theorem leaf_pRawS (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pRawS = mainRawS gammaZero := by
  simp [pRawS, pGamma, evalReal, ec, mainRawS, gammaZero]
  ring

theorem leaf_pDelta (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pDelta = mainDeltaH35 gammaZero := by
  simp [pDelta, pGamma540, pR0H, pR1H, pGeo, pGeoPoly, pRawA, pRawS, pGamma, evalReal, ec,
    mainDeltaH35, mainRawA, mainRawS, gammaZero, leaf_pAlpha, leaf_pBetaPrime, pLog3, ev,
    panelRealEnv, exp_mul_log_three, eval_epow]
  left
  norm_num
  ring

theorem leaf_pV (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pV = panelVbar := by
  simp [pV, evalReal, ec, mainSourceClock, gammaZero, pLog3, ev, panelRealEnv,
    exp_mul_log_three]
  norm_num

theorem leaf_pA2 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pA2 = mainA2 panelVbar := by
  simp [pA2, evalReal, ec, mainA2, leaf_pV]

theorem leaf_pA4 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pA4 = mainA4 panelVbar := by
  simp [pA4, evalReal, ec, mainA4, leaf_pV]

theorem leaf_pKa (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pKa = mainKa panelVbar := by
  simp [pKa, eval_esum, evalReal, ec, mainKa, leaf_pA2, leaf_pA4, leaf_pV]
  norm_num <;> ring_nf

theorem leaf_pKd (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pKd = mainKd panelVbar := by
  simp [pKd, eval_esum, evalReal, ec, mainKd, leaf_pA2, leaf_pA4, leaf_pV]
  norm_num <;> ring_nf

theorem leaf_pOp (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pOp = mainOp panelVbar := by
  simp [pOp, pSqrt2, evalReal, ec, mainOp, leaf_pA2]
  norm_num <;> ring_nf

theorem leaf_pOm (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pOm = mainOm panelVbar := by
  simp [pOm, evalReal, ec, mainOm, leaf_pA2]
  norm_num <;> ring_nf

theorem leaf_pSigma1 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pSigma1 = Real.sqrt ((156 / 5) * mainA2 panelVbar) := by
  simp [pSigma1, evalReal, ec, leaf_pA2]

theorem leaf_pSigma2 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pSigma2 = Real.sqrt ((46488 / 25) * mainA4 panelVbar) := by
  simp [pSigma2, evalReal, ec, leaf_pA4]

theorem leaf_pKrem (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pKrem = mainKrem panelVbar := by
  simp [pKrem, evalReal, ec, mainKrem, leaf_pSigma1, leaf_pSigma2]
  norm_num <;> ring_nf

theorem leaf_pB0 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pB0 = panelVbar * d.covarianceCap := by
  simp [pB0, pQCap, ev, evalReal, panelRealEnv, leaf_pV]

theorem leaf_pBe (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pBe = mainBe panelVbar d.covarianceCap := by
  simp [pBe, pQCap, ev, eval_esum, evalReal, ec, panelRealEnv, mainBe, leaf_pV]
  norm_num <;> ring_nf

theorem leaf_pX (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pX =
      Real.sqrt (panelVbar + panelVbar * d.covarianceCap / 2) := by
  simp [pX, leaf_pB0, leaf_pV, evalReal, ec]

theorem leaf_pY (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pY = Real.sqrt panelVbar := by
  simp [pY, evalReal, leaf_pV]

theorem leaf_pEcov (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pEcov = mainEcov panelVbar d.covarianceCap := by
  simp [pEcov, pEplus, pEminus, eval_epow, leaf_pB0, leaf_pV, leaf_pSigma1, leaf_pOp,
    leaf_pOm, evalReal, ec, mainEcov, mainA2]

theorem leaf_pH0 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pH0 = mainH0 := by
  simp [pH0, mainH0, evalReal, ec, pLog3, ev, panelRealEnv, exp_mul_log_three]
  ring

theorem leaf_pZ4 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pZ4 = (3 : ℝ) ^ (1 / 4 : ℝ) := by
  simp [pZ4, pSqrt3, evalReal, ec, sqrt_sqrt_three]

theorem leaf_pZ8 (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pZ8 = (105 : ℝ) ^ (1 / 8 : ℝ) := by
  simp [pZ8, evalReal, ec]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem leaf_pDgeom (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pDgeom = mainD := by
  simp [pDgeom, mainD, leaf_pAlpha, evalReal, ec]

theorem leaf_consts (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) pSqrt2 = Real.sqrt 2 ∧
    evalReal (panelRealEnv d s f) pBeta = mainBeta ∧
    evalReal (panelRealEnv d s f) pBetaOld = mainBetaOld ∧
    evalReal (panelRealEnv d s f) pEpsOld = mainEpsOld ∧
    evalReal (panelRealEnv d s f) pEpsNew = mainEpsNew ∧
    evalReal (panelRealEnv d s f) pS = s ∧
    evalReal (panelRealEnv d s f) pXi0 = d.initialInverseMean ∧
    evalReal (panelRealEnv d s f) pA0 = d.initialMean ∧
    evalReal (panelRealEnv d s f) pF = f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [pSqrt2, pBeta, pBetaOld, pEpsOld, pEpsNew, pS, pXi0, pA0, pF, ev, evalReal, ec,
      panelRealEnv, mainBeta, mainBetaOld, mainEpsOld, mainEpsNew]

theorem leaf_energy (d : PanelRealData) (s f : ℝ)
    (hR : 0 ≤ mainBeta * (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s - f) +
      mainEpsNew * (mainEnvelopeH35 panelVbar gammaZero s / (1 - mainAlpha))) :
    evalReal (panelRealEnv d s f) energyExpr =
      mainSourceError' panelVbar
        (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s) f
        (mainEnvelopeH35 panelVbar gammaZero s)
        (d.initialInverseMean + evalReal (panelRealEnv d s f) pXiSlope * s) d.covarianceCap := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  have hD := leaf_pDgeom d s f
  unfold energyExpr mainReturnPanelFormula
  simp only [evalReal, eval_epow, c2, cb, cbo, ceo, cen, cs, cxi, ca, cf, hD,
    leaf_pH0, leaf_pDelta, leaf_pV, leaf_pZ4, leaf_pZ8, leaf_pKa, leaf_pKd, leaf_pKrem,
    leaf_pOp, leaf_pOm, leaf_pBe, leaf_pEcov, leaf_pX, leaf_pY, leaf_pAlpha, leaf_pB0, ec]
  simp only [mainSourceError', mainError', mainLinearError, mainFourLoadAG, mainLoadZ,
    mainLoadD, mainLoadQ, mainR1, mainR2, mainT0, mainG, mainRec, mainV, mainM0, mainTm, mainBm,
    mainC, mainHd, mainEnvelopeH35, Rat.cast_ofNat, Rat.cast_one, Nat.cast_ofNat]
  set X := Real.sqrt (mainH0 + mainDeltaH35 gammaZero * s) + Real.sqrt (2 * panelVbar * s) *
    ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld + (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)
    with hX
  have hbm : 0 ≤ mainBeta * (1 + 2 * X ^ 2 + Real.sqrt (2 * X ^ 2)) := by
    have : (0 : ℝ) ≤ mainBeta := by norm_num [mainBeta]
    positivity
  have hR' : 0 ≤ mainBeta * (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s - f) +
      mainEpsNew * (X ^ 2 / (1 - mainAlpha)) := by simpa [mainEnvelopeH35, hX] using hR
  simp only [Real.sq_sqrt hbm, Real.sq_sqrt hR']
  push_cast
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_
  all_goals first | (ring_nf; done) | skip

theorem leaf_lambda (d : PanelRealData) (s f : ℝ)
    (hR1 : 0 < mainBeta * (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s - f) +
      mainEpsNew * (mainEnvelopeH35 panelVbar gammaZero s / (1 - mainAlpha)))
    (hR2 : 0 < mainBeta ^ 2 * (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s - f) +
      (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
        (mainEnvelopeH35 panelVbar gammaZero s / (1 - mainAlpha)))
    (hV : 0 < d.initialInverseMean + evalReal (panelRealEnv d s f) pXiSlope * s -
      mainBetaOld * f) :
    evalReal (panelRealEnv d s f) negativeAnchorDerivativeExpr =
      mainRadicalSlope (mainErrorSlope panelVbar)
        (mainErrorWeights' panelVbar (mainEnvelopeH35 panelVbar gammaZero s)
          (d.initialInverseMean + evalReal (panelRealEnv d s f) pXiSlope * s)
          (mainEcov panelVbar d.covarianceCap) (mainBe panelVbar d.covarianceCap)
          (mainKd panelVbar) (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar)
          d.covarianceCap)
        (mainErrorOffsets (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s)
          (mainEnvelopeH35 panelVbar gammaZero s)
          (d.initialInverseMean + evalReal (panelRealEnv d s f) pXiSlope * s))
        mainErrorRates f := by
  obtain ⟨c2, cb, cbo, ceo, cen, cs, cxi, ca, cf⟩ := leaf_consts d s f
  have hD := leaf_pDgeom d s f
  unfold negativeAnchorDerivativeExpr mainReturnPanelFormula
  simp only [evalReal, eval_epow, c2, cb, cbo, ceo, cen, cs, cxi, ca, cf, hD,
    leaf_pH0, leaf_pDelta, leaf_pV, leaf_pZ4, leaf_pZ8, leaf_pKa, leaf_pKd, leaf_pKrem,
    leaf_pOp, leaf_pOm, leaf_pBe, leaf_pEcov, leaf_pX, leaf_pY, leaf_pAlpha, leaf_pB0, ec]
  simp only [mainRadicalSlope, mainErrorSlope, mainErrorWeights', mainErrorOffsets,
    mainErrorRates, mainErrorSourceRoot, mainHd, mainEnvelopeH35, mainT0, mainRec, mainLoadQ, mainM0,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Rat.cast_ofNat, Rat.cast_one]
  set X := Real.sqrt (mainH0 + mainDeltaH35 gammaZero * s) + Real.sqrt (2 * panelVbar * s) *
    ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld + (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)
    with hX
  set A := d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s with hA
  set ξ' := d.initialInverseMean + evalReal (panelRealEnv d s f) pXiSlope * s with hξ
  have hbm : 0 ≤ mainBeta * (1 + 2 * X ^ 2 + Real.sqrt (2 * X ^ 2)) := by
    have : (0 : ℝ) ≤ mainBeta := by norm_num [mainBeta]
    positivity
  have hR1' : 0 < mainBeta * (A - f) + mainEpsNew * (X ^ 2 / (1 - mainAlpha)) := by
    simpa [mainEnvelopeH35, hX] using hR1
  have hR2' : 0 < mainBeta ^ 2 * (A - f) +
      (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) * (X ^ 2 / (1 - mainAlpha)) := by
    simpa [mainEnvelopeH35, hX] using hR2
  have e1 : mainBeta * A + mainEpsNew * (X ^ 2 / (1 - mainAlpha)) - mainBeta * f =
      mainBeta * (A - f) + mainEpsNew * (X ^ 2 / (1 - mainAlpha)) := by ring
  have e2 : mainBeta ^ 2 * A + (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
      (X ^ 2 / (1 - mainAlpha)) - mainBeta ^ 2 * f =
      mainBeta ^ 2 * (A - f) + (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
        (X ^ 2 / (1 - mainAlpha)) := by ring
  simp only [Real.sq_sqrt hbm, e1, e2]
  have p1 := Real.sqrt_pos.2 hR1'
  have p2 := Real.sqrt_pos.2 hR2'
  have hV' : 0 < ξ' - mainBetaOld * f := hV
  have p3 := Real.sqrt_pos.2 hV'
  generalize Real.sqrt (mainBeta * (A - f) + mainEpsNew * (X ^ 2 / (1 - mainAlpha))) = R1 at p1 ⊢
  generalize Real.sqrt (mainBeta ^ 2 * (A - f) + (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
    (X ^ 2 / (1 - mainAlpha))) = R2 at p2 ⊢
  generalize Real.sqrt (ξ' - mainBetaOld * f) = V at p3 ⊢
  field_simp
  ring

theorem leaf_support (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) supportLineExpr =
      evalReal (panelRealEnv d s f) energyExpr +
        f * evalReal (panelRealEnv d s f) negativeAnchorDerivativeExpr := by
  obtain ⟨-, -, -, -, -, -, -, -, cf⟩ := leaf_consts d s f
  simp [supportLineExpr, energyExpr, negativeAnchorDerivativeExpr, mainReturnPanelFormula,
    evalReal, cf]

theorem leaf_generatorUpper (d : PanelRealData) (s f : ℝ) :
    evalReal (panelRealEnv d s f) generatorUpperExpr =
      panelVbar * d.covarianceCap +
        ((panelVbar / 2 * (d.initialMean + evalReal (panelRealEnv d s f) pMeanSlope * s) +
          panelVbar * d.covarianceCap * (mainBeta - 1) +
            (4 + 2 * Real.sqrt 2) * (156 / 5) * mainA2 panelVbar / 9) +
        evalReal (panelRealEnv d s f) supportLineExpr +
        evalReal (panelRealEnv d s f) inverseAbsoluteExpr) := by
  obtain ⟨c2, cb, -, -, -, cs, -, ca, -⟩ := leaf_consts d s f
  unfold generatorUpperExpr
  simp only [evalReal, leaf_pB0, leaf_pV, leaf_pA2, c2, cb, ca, cs, ec, Rat.cast_ofNat]
  simp only [supportLineExpr, inverseAbsoluteExpr]
  push_cast
  ring

end

end ASDExplicitGamma.Main
