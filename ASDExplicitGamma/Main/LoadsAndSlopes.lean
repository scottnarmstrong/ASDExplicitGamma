module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
Literal real formulas of DEF-MA-LOADS-AND-SLOPES.
The global and OLD banks have distinct names. The molecular parameter and the
true frame do not occur in these formulas. Quantities defined by other source
nodes are explicit scalar arguments; none is an assumed estimate.
-/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

/-- The weak triadic history ratio. -/
def mainAlpha : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
def mainD : ℝ := 1 + mainAlpha
def mainBeta : ℝ := 14103 / 10000
def mainEpsNew : ℝ := 1 / 10 ^ 24
def mainBetaOld : ℝ := 3683 / 2500
def mainEpsOld : ℝ := 3 / 10 ^ 46
def mainEta : ℝ := 1 / 25
def mainBetaPrime : ℝ := (3 : ℝ) ^ (-(3 / 20 : ℝ))
def mainA2 (v : ℝ) : ℝ := v * (3 : ℝ) ^ (-12 : ℤ)
def mainA4 (v : ℝ) : ℝ := v * (3 : ℝ) ^ (-24 : ℤ)
def mainT0 (xi : ℝ) : ℝ := Real.sqrt xi
def mainM0 (H : ℝ) : ℝ := 1 + 2 * H + Real.sqrt (2 * H)
def mainTm (H : ℝ) : ℝ := Real.sqrt (mainD * mainM0 H * H)
def mainBm (H : ℝ) : ℝ := Real.sqrt (mainBeta * mainM0 H)
def mainC (H : ℝ) : ℝ := mainBm H + 1
def mainG (xi : ℝ) : ℝ := Real.sqrt (2 * xi)
def mainRec (xi : ℝ) : ℝ := Real.sqrt (2 * mainBeta * xi)
def mainKa (v : ℝ) : ℝ := Real.sqrt v +
  (1440 / 1000) * Real.sqrt ((156 / 5) * mainA2 v) +
  (285 / 1000) * Real.sqrt ((46488 / 25) * mainA4 v)
def mainKb (v : ℝ) : ℝ := Real.sqrt v +
  (1440 / 1000) * Real.sqrt ((78 / 5) * mainA2 v) +
  (285 / 1000) * Real.sqrt ((23244 / 25) * mainA4 v)
def mainHd (H : ℝ) : ℝ := H / (1 - mainAlpha)
def mainR1 (a f H : ℝ) : ℝ :=
  Real.sqrt (mainBeta * (a - f) + mainEpsNew * mainHd H)
def mainR2 (a f H : ℝ) : ℝ :=
  Real.sqrt (mainBeta ^ 2 * (a - f) +
    (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) * mainHd H)
def mainV (xi f : ℝ) : ℝ := Real.sqrt (xi - mainBetaOld * f)
def mainLoadD (v a f H xi kd : ℝ) : ℝ := mainKa v * mainR1 a f H + kd * mainT0 xi
def mainLoadZ (v a f H xi kd : ℝ) : ℝ := mainKa v * mainR2 a f H +
  kd * Real.sqrt (mainBeta * xi + mainEpsNew * mainD * mainBeta * H)
def mainLoadQ (H op om : ℝ) : ℝ :=
  Real.sqrt ((mainBeta + 1) ^ 2 * op ^ 2 + mainBeta * mainM0 H * om ^ 2)

/-- The source's raw mean-response coefficients, with the scale parameter explicit. -/
def mainRawA (gamma : ℝ) : ℝ :=
  1009309 / 500000 + gamma * (32474 * 7 + 11483216)
def mainRawS (gamma : ℝ) : ℝ := 32474 * gamma
def mainRawFactor (gamma : ℝ) : ℝ := 4 * (3 : ℝ) ^ (26 * gamma)

def mainPa (v : ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt ((39 / 5) * mainA2 v),
    (36 / 25) * Real.sqrt ((156 / 5) * mainA2 v),
    (57 / 200) * Real.sqrt ((46488 / 25) * mainA4 v)]
def mainPb (v : ℝ) : Fin 3 → ℝ :=
  ![mainPa v 0,
    (36 / 25) * Real.sqrt ((78 / 5) * mainA2 v),
    (57 / 200) * Real.sqrt ((23244 / 25) * mainA4 v)]

/-- Coefficients of `(232/125) P_a(z)^2 + 38 P_b(z)^2`, in increasing degree. -/
def mainSlopeCoefficients (v : ℝ) : Fin 5 → ℝ :=
  let a := mainPa v
  let b := mainPb v
  ![(232 / 125) * a 0 ^ 2 + 38 * b 0 ^ 2,
    (464 / 125) * a 0 * a 1 + 76 * b 0 * b 1,
    (232 / 125) * (2 * a 0 * a 2 + a 1 ^ 2) + 38 * (2 * b 0 * b 2 + b 1 ^ 2),
    (464 / 125) * a 1 * a 2 + 76 * b 1 * b 2,
    (232 / 125) * a 2 ^ 2 + 38 * b 2 ^ 2]

def mainGeo (q : ℝ) : ℝ := (1 - q)⁻¹
def mainRawGeo (gamma q : ℝ) : ℝ :=
  mainRawA gamma / (1 - q) + mainRawS gamma * q / (1 - q) ^ 2
def mainW (gamma r : ℝ) (n : ℕ) : ℝ :=
  (1 - mainAlpha ^ 2) / (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (r * gamma - n))
def mainRawW (gamma r : ℝ) (n : ℕ) : ℝ :=
  (1 - mainAlpha ^ 2) * mainRawGeo gamma (mainAlpha ^ 2 * (3 : ℝ) ^ (r * gamma - n))
def mainKf (v : ℝ) : ℝ := (78 / 5) * mainA2 v *
  (1 / 4 + (36 / 25) / Real.sqrt 2 + (57 / 200) * Real.sqrt 2)
def mainJ0 (v gamma : ℝ) : ℝ :=
  (26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma * mainRawA gamma +
    52 * v * Real.sqrt 3 * mainBetaOld ^ 3
def mainK0 (v gamma : ℝ) : ℝ :=
  (26 / 25) * mainBetaOld * mainRawFactor gamma * mainRawA gamma +
    52 * v * Real.sqrt 3 * mainBetaOld ^ 2

/-- Ordinary-mean transport slope `mu`, distinct from the inverse-generator `mu_-`. -/
def mainMu (v gamma : ℝ) : ℝ :=
  (232 / 125) * (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 * mainJ0 v gamma +
    2 * mainKf v * mainK0 v gamma + 2 * v * (mainBetaOld + Real.sqrt 3 * mainEpsOld)

def mainXiCoefficients (v : ℝ) : Fin 3 → ℝ :=
  ![(232 / 125) * (mainPa v 0 + mainPa v 1) ^ 2,
    (464 / 125) * (mainPa v 0 + mainPa v 1) * mainPa v 2,
    (232 / 125) * mainPa v 2 ^ 2]

/-- OLD local weak-history transport slope `chi`. -/
def mainChi (v gamma : ℝ) : ℝ :=
  (∑ i : Fin 3, mainXiCoefficients v i *
    ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor gamma * mainRawW gamma 10 (i.val + 2) +
      52 * v * Real.sqrt 3 * mainBetaOld ^ 4 * mainW gamma 8 (i.val + 2))) +
  2 * mainKf v *
    ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma * mainRawW gamma 8 2 +
      52 * v * Real.sqrt 3 * mainBetaOld ^ 3 * mainW gamma 6 2) +
  2 * v * mainBetaOld ^ 2 * mainW gamma 4 0 +
  2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld * (1 - mainAlpha ^ 2) /
    (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64))

/-- Strong-history transport slope; the frozen beta-prime exponent contains no gamma. -/
def mainDeltaH (v gamma : ℝ) : ℝ :=
  (1 - mainAlpha) * ∑ i : Fin 5, mainSlopeCoefficients v i *
    ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor gamma *
        mainRawGeo gamma (mainBetaPrime * (3 : ℝ) ^ (8 * gamma - i.val)) +
      26 * 48 * v * mainBetaOld ^ 3 *
        mainGeo (mainBetaPrime * (3 : ℝ) ^ (6 * gamma - i.val)))

def mainEnvelopeA (v gamma a0 t : ℝ) : ℝ := a0 + t * mainMu v gamma
def mainEnvelopeXi (v gamma xiPre theta t : ℝ) : ℝ :=
  xiPre + (1 / 10 ^ 12) * theta + t * mainChi v gamma
def mainH0 : ℝ := (3 : ℝ) ^ (3 / 4 : ℝ) * (2379 / 2500)
def mainEnvelopeH (v gamma t : ℝ) : ℝ :=
  (Real.sqrt (mainH0 + mainDeltaH v gamma * t) + Real.sqrt (2 * v * t) *
    ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
      (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) ^ 2

/-- Inverse forcing ratio, separate from the history slope. -/
def mainRho : ℝ :=
  4 * mainEpsNew + 6 * mainEpsNew ^ 2 / mainBeta + 2 * mainEpsNew ^ 3 / mainBeta ^ 2
def mainKappa (muMinus : ℝ) : ℝ := muMinus * mainBeta ^ 2
def mainInverseAbs (v muMinus t : ℝ) : ℝ :=
  v * (2 + mainRho) * (1 - Real.exp (-(mainKappa muMinus * t)))

/-- The full source additive error; Lq, ecov, AG, be, kd and krem are supplied
by their own nodes, with their precise scalar roles preserved. -/
def mainError (v a f H xi Lq ecov AG be kd krem op om : ℝ) : ℝ :=
  Lq + mainLoadZ v a f H xi kd ^ 2 +
  (v / 2 * mainR1 a f H ^ 2 +
    2 * (krem * mainR1 a f H + kd * mainT0 xi) * mainT0 xi * Real.sqrt v +
    Real.sqrt 2 * mainT0 xi * mainR1 a f H * ecov) +
  2 * mainLoadD v a f H xi kd * mainLoadQ H op om + 2 * be * mainV xi f + AG * mainG xi +
  2 * kd * (63 / 50) *
    (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi kd + mainLoadZ v a f H xi kd * mainRec xi)

end

end ASDExplicitGamma.Main
