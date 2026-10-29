module

public import ASDExplicitGamma.Numerics.Mirror.Composition
public import ASDExplicitGamma.Numerics.Spike.MainCertTypes
import Mathlib.Tactic.NormNum

/-!
# Production main-return panel formula

This module isolates the expression trees from generated panel data. The trees
are the paper's formulas; each panel supplies the
observer, panel interval, base point, initial mean, initial inverse mean, and covariance cap as pure
data. The real interpretation and outward grid evaluator come from `Composition`.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.Mirror

local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt
local prefix:max "expₑ " => Expr.exp

def ec (q : ℚ) : Expr := .const q
def ev (i : ℕ) : Expr := .var i

def epow (a : Expr) : ℕ → Expr
  | 0 => ec 1
  | n + 1 => epow a n *ₑ a

def esum (terms : List Expr) : Expr := terms.foldl Expr.add (ec 0)

def pLog3 : Expr := ev 0
def pS : Expr := ev 1
def pA0 : Expr := ev 2
def pXi0 : Expr := ev 3
def pQCap : Expr := ev 4
def pF : Expr := ev 5

/- The calibration constants γ, β₀, β, ε₀, εₙ, η, clock, and d_fb are the exact
   rationals, including the per-observer and old/new roles. -/
def pGamma : Expr := ec (17 / 50000)
def pBetaOld : Expr := ec (3683 / 2500)
def pBeta : Expr := ec (14103 / 10000)
def pEpsOld : Expr := ec (3 / 10 ^ 46)
def pEpsNew : Expr := ec (1 / 10 ^ 24)

/- √2, √3, 3^(1/4), 105^(1/8), α, D, and β′ are the constants. -/
def pSqrt2 : Expr := √ₑ (ec 2)
def pSqrt3 : Expr := √ₑ (ec 3)
def pZ4 : Expr := √ₑ pSqrt3
def pZ8 : Expr := √ₑ (√ₑ (√ₑ (ec 105)))
def pAlpha : Expr := ec 1 /ₑ pZ4
def pDgeom : Expr := ec 1 +ₑ pAlpha
def pBetaPrime : Expr := ec 1 /ₑ expₑ (ec (3 / 20) *ₑ pLog3)
def pDfb : Expr := ec (63 / 50)

/- H₀, v, A₂, A₄, k_a, k_b, k_d, o₊, and o₋ are the per-observer constants. -/
def pH0 : Expr := ec (2379 / 2500) *ₑ expₑ (ec (3 / 4) *ₑ pLog3)
def pV : Expr := ec (443 / 125 * (17 / 50000)) *ₑ expₑ (ec (2 * 17 / 50000) *ₑ pLog3)
def pA2 : Expr := pV *ₑ ec (1 / (3 : ℚ) ^ 12)
def pA4 : Expr := pV *ₑ ec (1 / (3 : ℚ) ^ 24)

def pKa : Expr := esum [√ₑ pV,
  ec (36 / 25) *ₑ √ₑ (ec (156 / 5) *ₑ pA2),
  ec (57 / 200) *ₑ √ₑ (ec (46488 / 25) *ₑ pA4)]
def pKb : Expr := esum [√ₑ pV,
  ec (36 / 25) *ₑ √ₑ (ec (78 / 5) *ₑ pA2),
  ec (57 / 200) *ₑ √ₑ (ec (23244 / 25) *ₑ pA4)]
def pKd : Expr := esum [
  ec (637 / 1000) *ₑ √ₑ (ec (156 / 5) *ₑ pA2),
  ec (11 / 25 * (38 / 125)) *ₑ √ₑ (ec (46488 / 25) *ₑ pA4)]

/- The absolute inverse branch is
   v(2 + 4εₙ + 6εₙ²/β + 2εₙ³/β²)(1 - exp(-μ₋β²s)). The generator inequality uses I_abs
   alone; the relative branch does not occur in this formula. -/
def pMuMin : Expr := (epow pKb 2 +ₑ √ₑ (epow pKb 4 +ₑ
  ec 4 *ₑ epow pDfb 2 *ₑ epow pKa 2 *ₑ epow pKb 2)) /ₑ ec 2
def pKappa : Expr := pMuMin *ₑ epow pBeta 2
def pRareRatio : Expr := ec 4 *ₑ pEpsNew +ₑ
  ec 6 *ₑ epow pEpsNew 2 /ₑ pBeta +ₑ
  ec 2 *ₑ epow pEpsNew 3 /ₑ epow pBeta 2
def pInverseAbsolute : Expr := pV *ₑ (ec 2 +ₑ pRareRatio) *ₑ
  (ec 1 -ₑ expₑ (Expr.neg (pKappa *ₑ pS)))
def pOp : Expr := (ec 1 +ₑ pSqrt2) *ₑ ec (11 / 25) *ₑ √ₑ (ec (156 / 5) *ₑ pA2)
def pOm : Expr := ec (11 / 25) *ₑ √ₑ (ec (156 / 5) *ₑ pA2)

def pB0 : Expr := pV *ₑ pQCap
def pBe : Expr := pV *ₑ esum [
  √ₑ (pQCap /ₑ ec 2),
  ec (38 / 125) *ₑ √ₑ (ec (156 / 5)) *ₑ ec (1 / (3 : ℚ) ^ 6) *ₑ
    (√ₑ (pQCap /ₑ ec 2) +ₑ ec 2)]
def pX : Expr := √ₑ (pV +ₑ pB0 /ₑ ec 2)
def pY : Expr := √ₑ pV

def pPa0 : Expr := √ₑ (ec (39 / 5) *ₑ pA2)
def pPa1 : Expr := ec (36 / 25) *ₑ √ₑ (ec (156 / 5) *ₑ pA2)
def pPa2 : Expr := ec (57 / 200) *ₑ √ₑ (ec (46488 / 25) *ₑ pA4)

/- The polynomial coefficients and raw geometric-series constants transcribe
   given by the displayed exact expressions; δ is the five-term sum. -/

def pRawA : Expr := ec (1009309 / 500000) +ₑ pGamma *ₑ
  (ec 32474 *ₑ ec 7 +ₑ ec 11483216)
def pRawS : Expr := pGamma *ₑ ec 32474
def pRawFactor : Expr := ec 4 *ₑ expₑ (ec (26 * 17 / 50000) *ₑ pLog3)

def pGeo (q : Expr) : Expr := ec 1 /ₑ (ec 1 -ₑ q)
def pGeoPoly (q : Expr) : Expr :=
  pRawA /ₑ (ec 1 -ₑ q) +ₑ
    (pRawS *ₑ q) /ₑ epow (ec 1 -ₑ q) 2

def pPow3Inv (n : ℕ) : Expr := ec (1 / (3 : ℚ) ^ n)

/- The provable history slope δ'_H(γ₀) is used in place of δ_H. -/
def pGamma540 : Expr := ec (540 * 17 / 50000)
def pR0H : Expr := pBetaPrime *ₑ expₑ (ec (2 * 17 / 50000) *ₑ pLog3)
def pR1H : Expr := pBetaPrime *ₑ expₑ (ec (8 * 17 / 50000) *ₑ pLog3) *ₑ ec (1 / 9)

def pDelta : Expr :=
  (ec 1 -ₑ pAlpha) *ₑ
    (pGamma540 *ₑ expₑ (ec (12 * 17 / 50000) *ₑ pLog3) *ₑ pGeo pR0H +ₑ
      ec (9 / 10 * (17 / 50000)) *ₑ expₑ (ec (48 * 17 / 50000) *ₑ pLog3) *ₑ pGeoPoly pR1H)

/- k_f, J₀, K_{J₀}, and μ (meanslope) are the formulas at
   the displayed exact expressions; the weighted geometric terms and χ (xis) follow. -/
def pKf : Expr := ec (78 / 5) *ₑ pA2 *ₑ esum [ec (1 / 4),
  ec (36 / 25) /ₑ pSqrt2, ec (57 / 200) *ₑ pSqrt2]

def pJ0 : Expr := esum [ec (26 / 25) *ₑ epow pBetaOld 2 *ₑ pRawFactor *ₑ pRawA,
  ec 26 *ₑ ec 2 *ₑ pV *ₑ pSqrt3 *ₑ epow pBetaOld 3]
def pKj0 : Expr := esum [ec (26 / 25) *ₑ pBetaOld *ₑ pRawFactor *ₑ pRawA,
  ec 26 *ₑ ec 2 *ₑ pV *ₑ pSqrt3 *ₑ epow pBetaOld 2]

def pPaSum : Expr := esum [pPa0, pPa1, pPa2]
def pMeanSlope : Expr := esum [ec (232 / 125) *ₑ epow pPaSum 2 *ₑ pJ0,
  ec 2 *ₑ pKf *ₑ pKj0,
  ec 2 *ₑ pV *ₑ (pBetaOld +ₑ pSqrt3 *ₑ pEpsOld)]

def pWeightedGeo (growth n : ℕ) : Expr :=
  (ec 1 -ₑ epow pAlpha 2) *ₑ pGeo
    (epow pAlpha 2 *ₑ expₑ (ec (growth * 17 / 50000) *ₑ pLog3) *ₑ pPow3Inv n)
def pWeightedGeoPoly (growth n : ℕ) : Expr :=
  (ec 1 -ₑ epow pAlpha 2) *ₑ pGeoPoly
    (epow pAlpha 2 *ₑ expₑ (ec (growth * 17 / 50000) *ₑ pLog3) *ₑ pPow3Inv n)

def pMeanCoeff2 : Expr := ec (232 / 125) *ₑ epow (pPa0 +ₑ pPa1) 2
def pMeanCoeff3 : Expr := ec (464 / 125) *ₑ (pPa0 +ₑ pPa1) *ₑ pPa2
def pMeanCoeff4 : Expr := ec (232 / 125) *ₑ epow pPa2 2

def pXiCoefficientTerm (coeff : Expr) (n : ℕ) : Expr := coeff *ₑ esum [
  ec (26 / 25) *ₑ epow pBetaOld 3 *ₑ pRawFactor *ₑ pWeightedGeoPoly 10 n,
  ec 26 *ₑ ec 2 *ₑ pV *ₑ pSqrt3 *ₑ epow pBetaOld 4 *ₑ pWeightedGeo 8 n]

def pKfXiTerm : Expr := ec 2 *ₑ pKf *ₑ esum [
  ec (26 / 25) *ₑ epow pBetaOld 2 *ₑ pRawFactor *ₑ pWeightedGeoPoly 8 2,
  ec 26 *ₑ ec 2 *ₑ pV *ₑ pSqrt3 *ₑ epow pBetaOld 3 *ₑ pWeightedGeo 6 2]
def pBetaXiTerm : Expr := ec 2 *ₑ pV *ₑ epow pBetaOld 2 *ₑ pWeightedGeo 4 0
def pQRare : Expr := epow pAlpha 2 *ₑ expₑ (ec (4 * 17 / 50000 + 1 / 64) *ₑ pLog3)
def pRareXiTerm : Expr := ec 2 *ₑ pV *ₑ pBetaOld *ₑ pSqrt3 *ₑ pEpsOld *ₑ
  (ec 1 -ₑ epow pAlpha 2) /ₑ (ec 1 -ₑ pQRare)
def pXiSlope : Expr := esum [pXiCoefficientTerm pMeanCoeff2 2,
  pXiCoefficientTerm pMeanCoeff3 3, pXiCoefficientTerm pMeanCoeff4 4,
  pKfXiTerm, pBetaXiTerm, pRareXiTerm]

/- σ₁, σ₂, k_rem, e₊, e₋, and e_cov are given by the displayed exact expressions. -/
def pSigma1 : Expr := √ₑ (ec (156 / 5) *ₑ pA2)
def pSigma2 : Expr := √ₑ (ec (46488 / 25) *ₑ pA4)
def pKrem : Expr := ec (1009 / 500) *ₑ pSigma1 +ₑ ec (57 / 200) *ₑ pSigma2
def pEplus : Expr := √ₑ (pV *ₑ pB0 /ₑ ec 2) +ₑ
  ec (319 / 1000) *ₑ pSigma1 *ₑ pOp
def pEminus : Expr := √ₑ (pV *ₑ pB0 /ₑ ec 2) +ₑ
ec (319 / 1000) *ₑ pSigma1 *ₑ pOm
def pEcov : Expr := √ₑ (epow pEplus 2 +ₑ epow pEminus 2)

/- The derived and f-dependent expressions. In particular λ is the displayed `lam`, the checked value of
   -∂_f E_t at f=1/100 (decreasing and concave in f). -/
/-- The energy, negative base-point derivative, and affine support expression as `Expr` trees. -/
structure PanelFormula where
  energy : Expr
  lambda : Expr
  support : Expr

def mainReturnPanelFormula : PanelFormula := by
  let h := epow (√ₑ (pH0 +ₑ pDelta *ₑ pS) +ₑ
      √ₑ (ec 2 *ₑ pV *ₑ pS) *ₑ
        (pZ4 *ₑ √ₑ pBetaOld +ₑ pZ8 *ₑ √ₑ pEpsOld)) 2
  let atVal := pA0 +ₑ pMeanSlope *ₑ pS
  let xi := pXi0 +ₑ pXiSlope *ₑ pS
  let t := √ₑ xi
  let m := ec 1 +ₑ ec 2 *ₑ h +ₑ √ₑ (ec 2 *ₑ h)
  let tm := √ₑ (pDgeom *ₑ m *ₑ h)
  let bm := √ₑ (pBeta *ₑ m)
  let localTerm := pSqrt2 *ₑ t *ₑ pX *ₑ pOp +ₑ
    ec 2 *ₑ pSqrt2 *ₑ tm *ₑ pY *ₑ pOm +ₑ
    pBeta *ₑ epow pOp 2 +ₑ m *ₑ epow pOm 2
  let c := bm +ₑ ec 1
  let q := √ₑ (epow (pBeta +ₑ ec 1) 2 *ₑ epow pOp 2 +ₑ epow bm 2 *ₑ epow pOm 2)
  let lq := localTerm +ₑ ec 2 *ₑ pKd *ₑ (t *ₑ pY +ₑ pSqrt2 *ₑ c *ₑ pOm)
  let ag := ec 2 *ₑ pBe +ₑ ec 2 *ₑ pKd *ₑ
    (t *ₑ (pX +ₑ pY) /ₑ pSqrt2 +ₑ ec (63 / 50) *ₑ pBeta *ₑ pOp +ₑ c *ₑ pOm)
  let parentGap := √ₑ (xi -ₑ pBetaOld *ₑ pF)
  let fourLoad := √ₑ (ec 2 *ₑ xi)
  let hdrop := h /ₑ (ec 1 -ₑ pAlpha)
  let r1 := √ₑ (pBeta *ₑ (atVal -ₑ pF) +ₑ pEpsNew *ₑ hdrop)
  let r2 := √ₑ (epow pBeta 2 *ₑ (atVal -ₑ pF) +ₑ
    (ec 2 *ₑ pBeta *ₑ pEpsNew +ₑ epow pEpsNew 2) *ₑ hdrop)
  let d := pKa *ₑ r1 +ₑ pKd *ₑ t
  let z := pKa *ₑ r2 +ₑ pKd *ₑ √ₑ (pBeta *ₑ xi +ₑ pEpsNew *ₑ pDgeom *ₑ pBeta *ₑ h)
  let ds := pKa *ₑ pBeta /ₑ (ec 2 *ₑ r1)
  let zs := pKa *ₑ epow pBeta 2 /ₑ (ec 2 *ₑ r2)
  let reciprocal := √ₑ (ec 2 *ₑ pBeta *ₑ xi)
  let xs := pBeta /ₑ (ec 2 *ₑ r1)
  let muDrop := pBeta *ₑ (atVal -ₑ pF) +ₑ pEpsNew *ₑ hdrop
  let crossCov := pV *ₑ muDrop /ₑ ec 2 +ₑ
    ec 2 *ₑ (pKrem *ₑ r1 +ₑ pKd *ₑ t) *ₑ t *ₑ √ₑ (pV +ₑ pB0 /ₑ ec 4) +ₑ
    pSqrt2 *ₑ t *ₑ r1 *ₑ pEcov
  let dampCov := pV *ₑ pBeta /ₑ ec 2 +ₑ
    ec 2 *ₑ pKrem *ₑ xs *ₑ t *ₑ √ₑ (pV +ₑ pB0 /ₑ ec 4) +ₑ
    pSqrt2 *ₑ t *ₑ xs *ₑ pEcov
  let energy := lq +ₑ epow z 2 +ₑ crossCov +ₑ ec 2 *ₑ d *ₑ q +ₑ
    ec 2 *ₑ pBe *ₑ parentGap +ₑ ag *ₑ fourLoad +ₑ
    ec 2 *ₑ pKd *ₑ ec (63 / 50) *ₑ
      (pSqrt2 *ₑ pBeta *ₑ d +ₑ z *ₑ reciprocal)
  let lambda := ec 2 *ₑ z *ₑ zs +ₑ dampCov +ₑ ec 2 *ₑ ds *ₑ q +ₑ
    pBe *ₑ pBetaOld /ₑ parentGap +ₑ
    ec 2 *ₑ pKd *ₑ ec (63 / 50) *ₑ
      (pSqrt2 *ₑ pBeta *ₑ ds +ₑ zs *ₑ reciprocal)
  exact { energy := energy, lambda := lambda, support := energy +ₑ pF *ₑ lambda }

/-- The source energy `E_t(s,f)` as an `Expr` tree. -/
def energyExpr : Expr := mainReturnPanelFormula.energy

/-- The source quantity `-∂E_t/∂f` as an `Expr` tree. -/
def negativeAnchorDerivativeExpr : Expr := mainReturnPanelFormula.lambda

/-- The source supporting line `E_t(s,f) + f(-∂E_t/∂f)` as an `Expr` tree. -/
def supportLineExpr : Expr := mainReturnPanelFormula.support

/-- The generator's absolute inverse-deficit branch `I_abs(s)` as an `Expr` tree. -/
def inverseAbsoluteExpr : Expr := pInverseAbsolute

/-- The additive generator error `b₀ + aff + J + I_abs`, with no relative-branch minimum. -/
def generatorUpperExpr : Expr := by
  let atVal := pA0 +ₑ pMeanSlope *ₑ pS
  let affine := pV /ₑ ec 2 *ₑ atVal +ₑ pB0 *ₑ (pBeta -ₑ ec 1) +ₑ
    (ec 4 +ₑ ec 2 *ₑ pSqrt2) *ₑ ec (156 / 5) *ₑ pA2 /ₑ ec 9
  exact pB0 +ₑ affine +ₑ mainReturnPanelFormula.support +ₑ pInverseAbsolute

/-! ### Real and interval panel data -/

/-- The three real inputs that vary from panel to panel. -/
structure PanelRealData where
  initialMean : ℝ
  initialInverseMean : ℝ
  covarianceCap : ℝ

/-- Their interval enclosures. -/
structure PanelIntervalData where
  initialMean : QInterval
  initialInverseMean : QInterval
  covarianceCap : QInterval

/-- The panel's real environment, including the independent `s` and base point `f`. -/
noncomputable def panelRealEnv (d : PanelRealData) (s f : ℝ) : ℕ → ℝ := fun i =>
  if i = 0 then Real.log 3 else if i = 1 then s else
  if i = 2 then d.initialMean else if i = 3 then d.initialInverseMean else
  if i = 4 then d.covarianceCap else if i = 5 then f else 0

/-- The corresponding grid interval environment. -/
def panelIntervalEnv (G : ℕ) (d : PanelIntervalData)
    (s f : QInterval) : ℕ → QInterval := fun i =>
  if i = 0 then logThree G else if i = 1 then s else
  if i = 2 then d.initialMean else if i = 3 then d.initialInverseMean else
  if i = 4 then d.covarianceCap else if i = 5 then f else gridConstant G 0

theorem panelEnv_sound (G : ℕ) (d : PanelRealData) (di : PanelIntervalData)
    (s f : ℝ) (si fi : QInterval)
    (hmean : QInterval.Contains di.initialMean d.initialMean)
    (hinv : QInterval.Contains di.initialInverseMean d.initialInverseMean)
    (hcap : QInterval.Contains di.covarianceCap d.covarianceCap)
    (hs : QInterval.Contains si s) (hf : QInterval.Contains fi f) :
    ∀ i, QInterval.Contains (panelIntervalEnv G di si fi i) (panelRealEnv d s f i) := by
  intro i
  by_cases h0 : i = 0
  · subst i
    simpa [panelIntervalEnv, panelRealEnv] using logThree_sound G
  · by_cases h1 : i = 1
    · subst i
      simpa [panelIntervalEnv, panelRealEnv, h0] using hs
    · by_cases h2 : i = 2
      · subst i
        simpa [panelIntervalEnv, panelRealEnv, h0, h1] using hmean
      · by_cases h3 : i = 3
        · subst i
          simpa [panelIntervalEnv, panelRealEnv, h0, h1, h2] using hinv
        · by_cases h4 : i = 4
          · subst i
            simpa [panelIntervalEnv, panelRealEnv, h0, h1, h2, h3] using hcap
          · by_cases h5 : i = 5
            · subst i
              simpa [panelIntervalEnv, panelRealEnv, h0, h1, h2, h3, h4] using hf
            · simpa [panelIntervalEnv, panelRealEnv, h0, h1, h2, h3, h4, h5] using
                (gridConstant_sound G (0 : ℚ))

/-- The real-valued panel energy `E_t(s,f)`. -/
noncomputable def panelEnergyReal (d : PanelRealData) (s f : ℝ) : ℝ :=
  evalReal (panelRealEnv d s f) mainReturnPanelFormula.energy

/-- The negative base-point derivative `-∂E_t/∂f` used by the support line. -/
noncomputable def panelLambdaReal (d : PanelRealData) (s f : ℝ) : ℝ :=
  evalReal (panelRealEnv d s f) mainReturnPanelFormula.lambda

/-- The affine support value `E_t(s,f) + f(-∂E_t/∂f)`. -/
noncomputable def panelSupportReal (d : PanelRealData) (s f : ℝ) : ℝ :=
  evalReal (panelRealEnv d s f) mainReturnPanelFormula.support

/-- The real absolute inverse branch used by the generator. -/
noncomputable def panelInverseAbsoluteReal (d : PanelRealData) (s f : ℝ) : ℝ :=
  evalReal (panelRealEnv d s f) inverseAbsoluteExpr

/-- The real generator error assembled from `b₀`, the affine term, the support line, and `I_abs`. -/
noncomputable def panelGeneratorUpperReal (d : PanelRealData) (s f : ℝ) : ℝ :=
  evalReal (panelRealEnv d s f) generatorUpperExpr

theorem panelEnergy_sound (G n : ℕ) (hn : 5 ≤ n) (d : PanelRealData) (di : PanelIntervalData)
    (s f : ℝ) (si fi : QInterval)
    (hmean : QInterval.Contains di.initialMean d.initialMean)
    (hinv : QInterval.Contains di.initialInverseMean d.initialInverseMean)
    (hcap : QInterval.Contains di.covarianceCap d.covarianceCap)
    (hs : QInterval.Contains si s) (hf : QInterval.Contains fi f)
    {out : QInterval}
    (heval : evalGrid G n hn (panelIntervalEnv G di si fi) mainReturnPanelFormula.energy = some out) :
    QInterval.Contains out (panelEnergyReal d s f) := by
  exact evalGrid_sound G n hn (panelIntervalEnv G di si fi) (panelRealEnv d s f)
    (panelEnv_sound G d di s f si fi hmean hinv hcap hs hf)
    mainReturnPanelFormula.energy out heval

theorem panelLambda_sound (G n : ℕ) (hn : 5 ≤ n) (d : PanelRealData) (di : PanelIntervalData)
    (s f : ℝ) (si fi : QInterval)
    (hmean : QInterval.Contains di.initialMean d.initialMean)
    (hinv : QInterval.Contains di.initialInverseMean d.initialInverseMean)
    (hcap : QInterval.Contains di.covarianceCap d.covarianceCap)
    (hs : QInterval.Contains si s) (hf : QInterval.Contains fi f)
    {out : QInterval}
    (heval : evalGrid G n hn (panelIntervalEnv G di si fi) mainReturnPanelFormula.lambda = some out) :
    QInterval.Contains out (panelLambdaReal d s f) := by
  exact evalGrid_sound G n hn (panelIntervalEnv G di si fi) (panelRealEnv d s f)
    (panelEnv_sound G d di s f si fi hmean hinv hcap hs hf)
    mainReturnPanelFormula.lambda out heval

theorem panelSupport_sound (G n : ℕ) (hn : 5 ≤ n) (d : PanelRealData) (di : PanelIntervalData)
    (s f : ℝ) (si fi : QInterval)
    (hmean : QInterval.Contains di.initialMean d.initialMean)
    (hinv : QInterval.Contains di.initialInverseMean d.initialInverseMean)
    (hcap : QInterval.Contains di.covarianceCap d.covarianceCap)
    (hs : QInterval.Contains si s) (hf : QInterval.Contains fi f)
    {out : QInterval}
    (heval : evalGrid G n hn (panelIntervalEnv G di si fi) mainReturnPanelFormula.support = some out) :
    QInterval.Contains out (panelSupportReal d s f) := by
  exact evalGrid_sound G n hn (panelIntervalEnv G di si fi) (panelRealEnv d s f)
    (panelEnv_sound G d di s f si fi hmean hinv hcap hs hf)
    mainReturnPanelFormula.support out heval

/-! ## Pure panel data and formula-level leaves -/

/-- Grid precision of the production certificate, matching the 10⁻³² grid. -/
def mainReturnGridDigits : ℕ := 32

/-- The degree-24 exponential Taylor polynomial with its proved remainder. -/
def mainReturnTaylorDegree : ℕ := 25

theorem mainReturnTaylorDegree_ge : 5 ≤ mainReturnTaylorDegree := by
  norm_num [mainReturnTaylorDegree]

/- Every panel's exact source inputs are the exact values `a0`, `xi0`, and
   `q_cap(observer - 1, q3_caps)`, together with the base point and the panel interval. -/
/-- All varying production inputs for one observer and one panel. The interval endpoints are
stored as exact rationals; `initialMean`, `initialInverseMean`, and `covarianceCap` are exact
real inputs, and the interval evaluator rounds their point enclosures outward. -/
structure MainPanelData where
  observer : ℕ
  panel : ℕ
  panelCount : ℕ
  initialMean : ℚ
  initialInverseMean : ℚ
  covarianceCap : ℚ
  time : QInterval
  anchor : ℚ

/-- Every integer grid endpoint contributed by one panel leaf. Every per-panel field consumed
by the production recurrence is carried here alongside the formula bounds. -/
structure PanelEndpoints where
  aUpper : ℕ
  ellLower : ℕ
  rhoLower : ℕ
  rhoUpper : ℕ
  offsetLower : ℕ
  offsetUpper : ℕ
  supportELower : ℕ
  supportEUpper : ℕ
  supportLambdaLower : ℕ
  supportLambdaUpper : ℕ
  supportJLower : ℕ
  supportJUpper : ℕ
  inverseAbsoluteUpper : ℕ

def PanelEndpoints.energyUpper (e : PanelEndpoints) : ℚ :=
  (e.supportEUpper : ℚ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℚ)

def PanelEndpoints.lambdaLower (e : PanelEndpoints) : ℚ :=
  (e.supportLambdaLower : ℚ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℚ)

def PanelEndpoints.supportUpper (e : PanelEndpoints) : ℚ :=
  (e.supportJUpper : ℚ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℚ)

def PanelEndpoints.generatorUpper (e : PanelEndpoints) : ℚ :=
  (e.aUpper : ℚ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℚ)

/-- The absolute inverse endpoint in real units. The stored natural number is a grid-unit
endpoint, just like the support and generator endpoints. -/
def PanelEndpoints.inverseAbsoluteUpperBound (e : PanelEndpoints) : ℚ :=
  (e.inverseAbsoluteUpper : ℚ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℚ)

/-- All three mirror outputs are computed from the same panel data. -/
structure MainPanelEnclosures where
  energy : QInterval
  lambda : QInterval
  support : QInterval
  inverseAbsolute : QInterval
  generatorUpper : QInterval

/-- The insertion-level frame endpoints and its eight panel leaves. -/
structure MainInsertionEndpoints where
  observer : ℕ
  frameLower : ℕ
  frameUpper : ℕ
  panels : List PanelEndpoints

def mainPanelRealData (d : MainPanelData) : PanelRealData :=
  ⟨d.initialMean, d.initialInverseMean, d.covarianceCap⟩

def mainPanelIntervalData (G : ℕ) (d : MainPanelData) : PanelIntervalData :=
  ⟨gridConstant G d.initialMean, gridConstant G d.initialInverseMean,
    gridConstant G d.covarianceCap⟩

def mainPanelAnchorInterval (G : ℕ) (d : MainPanelData) : QInterval :=
  gridConstant G d.anchor

def mainPanelEvaluation (G n : ℕ) (hn : 5 ≤ n) (d : MainPanelData) :
    Option MainPanelEnclosures := do
  let di := mainPanelIntervalData G d
  let fi := mainPanelAnchorInterval G d
  let energy ← evalGrid G n hn (panelIntervalEnv G di d.time fi) mainReturnPanelFormula.energy
  let lambda ← evalGrid G n hn (panelIntervalEnv G di d.time fi) mainReturnPanelFormula.lambda
  let support ← evalGrid G n hn (panelIntervalEnv G di d.time fi) mainReturnPanelFormula.support
  let inverseAbsolute ← evalGrid G n hn (panelIntervalEnv G di d.time fi) inverseAbsoluteExpr
  let generatorUpper ← evalGrid G n hn (panelIntervalEnv G di d.time fi) generatorUpperExpr
  return ⟨energy, lambda, support, inverseAbsolute, generatorUpper⟩

theorem mainPanelEvaluation_components {G n : ℕ} {hn : 5 ≤ n} {d : MainPanelData}
    {out : MainPanelEnclosures} (h : mainPanelEvaluation G n hn d = some out) :
    evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
        (mainPanelAnchorInterval G d)) mainReturnPanelFormula.energy = some out.energy ∧
      evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
        (mainPanelAnchorInterval G d)) mainReturnPanelFormula.lambda = some out.lambda ∧
      evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
        (mainPanelAnchorInterval G d)) mainReturnPanelFormula.support = some out.support ∧
      evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
        (mainPanelAnchorInterval G d)) inverseAbsoluteExpr = some out.inverseAbsolute ∧
      evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
        (mainPanelAnchorInterval G d)) generatorUpperExpr = some out.generatorUpper := by
  unfold mainPanelEvaluation at h
  cases he : evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
      (mainPanelAnchorInterval G d)) mainReturnPanelFormula.energy with
  | none => simp [he] at h
  | some energy =>
    cases hl : evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
        (mainPanelAnchorInterval G d)) mainReturnPanelFormula.lambda with
    | none => simp [he, hl] at h
    | some lambda =>
      cases hs : evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
          (mainPanelAnchorInterval G d)) mainReturnPanelFormula.support with
      | none => simp [he, hl, hs] at h
      | some support =>
        cases hi : evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
            (mainPanelAnchorInterval G d)) inverseAbsoluteExpr with
        | none => simp [he, hl, hs, hi] at h
        | some inverseAbsolute =>
          cases hg : evalGrid G n hn (panelIntervalEnv G (mainPanelIntervalData G d) d.time
              (mainPanelAnchorInterval G d)) generatorUpperExpr with
          | none => simp [he, hl, hs, hi, hg] at h
          | some generatorUpper =>
            simp [he, hl, hs, hi, hg] at h
            cases h
            simp

def mainPanelEndpointsCheck (out : MainPanelEnclosures) (e : PanelEndpoints) : Bool :=
  decide (out.energy.hi ≤ e.energyUpper ∧
    e.lambdaLower ≤ out.lambda.lo ∧ out.support.hi ≤ e.supportUpper ∧
    out.inverseAbsolute.hi ≤ e.inverseAbsoluteUpperBound ∧
    out.generatorUpper.hi ≤ e.generatorUpper)

def mainPanelCheck (G n : ℕ) (hn : 5 ≤ n) (d : MainPanelData)
    (e : PanelEndpoints) : Bool :=
  match mainPanelEvaluation G n hn d with
  | none => false
  | some out => mainPanelEndpointsCheck out e

/-- The exact real meaning of one successful formula-level panel check. -/
theorem mainPanel_sound (G n : ℕ) (hn : 5 ≤ n) (d : MainPanelData)
    (e : PanelEndpoints) (hcheck : mainPanelCheck G n hn d e = true) (s : ℝ)
    (hs : QInterval.Contains d.time s) :
    panelEnergyReal (mainPanelRealData d) s d.anchor ≤ (e.energyUpper : ℝ) ∧
      (e.lambdaLower : ℝ) ≤ panelLambdaReal (mainPanelRealData d) s d.anchor ∧
      panelSupportReal (mainPanelRealData d) s d.anchor ≤ (e.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData d) s d.anchor ≤
        (e.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData d) s d.anchor ≤
        (e.generatorUpper : ℝ) := by
  have hcheck' : (match mainPanelEvaluation G n hn d with
      | none => false
      | some out => mainPanelEndpointsCheck out e) = true := hcheck
  cases heval : mainPanelEvaluation G n hn d with
  | none =>
    simp only [heval] at hcheck'
    cases hcheck'
  | some out =>
    have hbool : mainPanelEndpointsCheck out e = true := by
      simpa only [heval] using hcheck'
    have hcmp : out.energy.hi ≤ e.energyUpper ∧
        e.lambdaLower ≤ out.lambda.lo ∧ out.support.hi ≤ e.supportUpper ∧
        out.inverseAbsolute.hi ≤ e.inverseAbsoluteUpperBound ∧
        out.generatorUpper.hi ≤ e.generatorUpper := by
      change decide (out.energy.hi ≤ e.energyUpper ∧
        e.lambdaLower ≤ out.lambda.lo ∧ out.support.hi ≤ e.supportUpper ∧
        out.inverseAbsolute.hi ≤ e.inverseAbsoluteUpperBound ∧
        out.generatorUpper.hi ≤ e.generatorUpper) = true at hbool
      exact of_decide_eq_true hbool
    obtain ⟨henergyEval, hlambdaEval, hsupportEval, hinverseEval, hgeneratorEval⟩ :=
      mainPanelEvaluation_components heval
    have hmean : QInterval.Contains (mainPanelIntervalData G d).initialMean
        (mainPanelRealData d).initialMean := gridConstant_sound G d.initialMean
    have hinv : QInterval.Contains (mainPanelIntervalData G d).initialInverseMean
        (mainPanelRealData d).initialInverseMean := gridConstant_sound G d.initialInverseMean
    have hcap : QInterval.Contains (mainPanelIntervalData G d).covarianceCap
        (mainPanelRealData d).covarianceCap := gridConstant_sound G d.covarianceCap
    have hf : QInterval.Contains (mainPanelAnchorInterval G d) d.anchor := gridConstant_sound G d.anchor
    have henergy := panelEnergy_sound G n hn (mainPanelRealData d) (mainPanelIntervalData G d)
      s d.anchor d.time (mainPanelAnchorInterval G d) hmean hinv hcap hs hf henergyEval
    have hlambda := panelLambda_sound G n hn (mainPanelRealData d) (mainPanelIntervalData G d)
      s d.anchor d.time (mainPanelAnchorInterval G d) hmean hinv hcap hs hf hlambdaEval
    have hsupport := panelSupport_sound G n hn (mainPanelRealData d) (mainPanelIntervalData G d)
      s d.anchor d.time (mainPanelAnchorInterval G d) hmean hinv hcap hs hf hsupportEval
    have hinputs := panelEnv_sound G (mainPanelRealData d) (mainPanelIntervalData G d)
      s d.anchor d.time (mainPanelAnchorInterval G d) hmean hinv hcap hs hf
    have hinverse := evalGrid_sound G n hn
      (panelIntervalEnv G (mainPanelIntervalData G d) d.time (mainPanelAnchorInterval G d))
      (panelRealEnv (mainPanelRealData d) s d.anchor) hinputs inverseAbsoluteExpr
      out.inverseAbsolute hinverseEval
    have hgenerator := evalGrid_sound G n hn
      (panelIntervalEnv G (mainPanelIntervalData G d) d.time (mainPanelAnchorInterval G d))
      (panelRealEnv (mainPanelRealData d) s d.anchor) hinputs generatorUpperExpr
      out.generatorUpper hgeneratorEval
    exact ⟨le_trans henergy.2 (by exact_mod_cast hcmp.1),
      le_trans (by exact_mod_cast hcmp.2.1) hlambda.1,
      le_trans hsupport.2 (by exact_mod_cast hcmp.2.2.1),
      le_trans hinverse.2 (by exact_mod_cast hcmp.2.2.2.1),
      le_trans hgenerator.2 (by exact_mod_cast hcmp.2.2.2.2)⟩

/-- Formula meaning exported by every generated panel leaf. -/
def panelFormulaBounds (d : MainPanelData) (e : PanelEndpoints) : Prop :=
  ∀ s : ℝ, QInterval.Contains d.time s →
    panelEnergyReal (mainPanelRealData d) s d.anchor ≤ (e.energyUpper : ℝ) ∧
      (e.lambdaLower : ℝ) ≤ panelLambdaReal (mainPanelRealData d) s d.anchor ∧
      panelSupportReal (mainPanelRealData d) s d.anchor ≤ (e.supportUpper : ℝ) ∧
      panelInverseAbsoluteReal (mainPanelRealData d) s d.anchor ≤
        (e.inverseAbsoluteUpperBound : ℝ) ∧
      panelGeneratorUpperReal (mainPanelRealData d) s d.anchor ≤
        (e.generatorUpper : ℝ)

end ASDExplicitGamma.Numerics.MainReturnCertificate
