module

public import ASDExplicitGamma.Numerics.Cold.Recurrence
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

/-! Checked moment, interpolation, and graph endpoints used by the recurrence replay. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

def coldScaleQ : ℚ := coldScale

def coldRoundDown (x : ℚ) : ℚ :=
  (Int.floor (coldScaleQ * x) : ℚ) / coldScaleQ

def coldUpMul (x y : ℚ) : ℚ := coldRoundUp (x*y)
def coldUpAdd (x y : ℚ) : ℚ := coldRoundUp (x+y)

def coldDecay (d : ℕ) : ℚ := (1/3 : ℚ)^d

def coldInitialMoment (ell : ℕ) : ℚ :=
  if ell = 0 then coldR20 else min coldR20 (coldA + coldSqrt19Upper*coldR20*coldDecay ell)

def coldMomentCandidate (ell k : ℕ) : ℚ :=
  let e := min (coldMomentAt k) (coldSqrt19Upper*coldDecay (ell-k)*coldMomentAt k)
  min (coldMomentAt k) (coldMeanAt k + e)

def coldMomentExpected (ell : ℕ) : ℚ :=
  if ell = 0 then coldR20 else
    coldRoundUp ((List.range ell).foldl
      (fun acc k => min acc (coldMomentCandidate ell k)) (coldInitialMoment ell))

def coldVUpper (k : ℕ) : ℚ := coldVData.getD k 0
def coldGraphRootAt (ell : ℕ) : ℚ := coldGraphRootData.getD ell 0
def coldGraphSqrtInputAt (ell : ℕ) : ℚ := coldGraphSqrtInputData.getD ell 0
def coldGraphChoiceAt (ell : ℕ) : ℕ := coldGraphChoiceData.getD ell 0

def coldOldGraph (ell : ℕ) : ℚ :=
  min (2*(2*coldA + 2*(coldV0Upper+coldL0)*coldDecay ell)^2)
      (4*(coldA+coldL0^2))

def coldFiveSixthsRadicand (ell k : ℕ) : ℚ :=
  let d := 2*coldDecay (ell-k)
  let meanSq := coldUpMul (coldMeanAt k) (coldMeanAt k)
  let fiveSixths := coldUpMul (coldRoundUp (5/6 : ℚ)) meanSq
  let interpolationSq := coldRoundUp ((d*coldInterpolationAt k)^2)
  coldUpAdd fiveSixths interpolationSq

def coldSandwichRadicand (ell k : ℕ) : ℚ :=
  let d := 2*coldDecay (ell-k)
  let e := coldRoundUp (d*coldVUpper k)
  let e2 := coldRoundUp (e^2)
  coldRoundUp (coldMeanAt k^2/2 + 2*e2)

def coldGraphRadicand (ell : ℕ) : ℚ :=
  let choice := coldGraphChoiceAt ell
  if choice = 0 then 0
  else if choice % 2 = 1 then coldFiveSixthsRadicand ell ((choice-1)/2)
  else coldSandwichRadicand ell ((choice-2)/2)

def coldFiveSixthsGraph (ell k : ℕ) : ℚ :=
  let d := 2*coldDecay (ell-k)
  let e := coldRoundUp (d*coldVUpper k)
  let radical := coldGraphRootAt ell
  2*(coldUpAdd e radical)^2

def coldSandwichGraph (ell k : ℕ) : ℚ :=
  let d := 2*coldDecay (ell-k)
  let e := coldRoundUp (d*coldVUpper k)
  let radical := coldGraphRootAt ell
  2*(coldUpAdd e radical)^2

/-- A source-selected branch of the minimum.  It is itself a valid graph cap; choosing one
branch suffices for the upper recurrence, while the frozen choice table reproduces the minimum
endpoint used by the numeric run. -/
def coldGraphChoiceValue (ell : ℕ) : ℚ :=
  let choice := coldGraphChoiceAt ell
  if choice = 0 then coldOldGraph ell
  else if choice % 2 = 1 then coldFiveSixthsGraph ell ((choice-1)/2)
  else coldSandwichGraph ell ((choice-2)/2)

def coldGraphExpected (ell : ℕ) : ℚ := coldRoundUp (coldGraphChoiceValue ell)

def coldCheckedGraphLags : List ℕ := List.range 127

theorem cold_moment_table_check :
    ∀ ell ∈ List.range 129, coldMomentAt ell = coldMomentExpected ell := by
  decide +kernel

theorem cold_graph_table_check :
    ∀ ell ∈ coldCheckedGraphLags, coldGraphAt ell = coldGraphExpected ell := by
  decide +kernel

theorem cold_interpolation_power_check :
    ∀ k ∈ List.range 127,
      coldInterpolationAt k ≤ coldL0 ∧
      coldInterpolationAt k ^ 19 ≥ coldMeanAt k ^ 9 * coldMomentAt k ^ 10 := by
  decide +kernel

theorem cold_v_endpoints_check :
    ∀ k ∈ List.range 127,
      coldVUpper k ^ 2 ≥ coldRoundUp (2*coldMeanAt k + coldInterpolationAt k^2) ∧
      (coldVUpper k - 1/coldScaleQ)^2 < coldRoundUp (2*coldMeanAt k + coldInterpolationAt k^2) := by
  decide +kernel

theorem cold_v0_endpoint_check :
    coldV0Upper ^ 2 ≥ coldRoundUp (2*coldA+coldL0^2) ∧
      (coldV0Upper - 1/coldScaleQ)^2 < coldRoundUp (2*coldA+coldL0^2) := by
  decide +kernel

theorem cold_graph_root_endpoints_check :
    ∀ ell ∈ coldCheckedGraphLags, coldGraphChoiceAt ell ≠ 0 →
      coldGraphRootAt ell ^ 2 ≥ coldGraphSqrtInputAt ell ∧
      (coldGraphRootAt ell - 1/coldScaleQ)^2 < coldGraphSqrtInputAt ell := by
  decide +kernel

theorem cold_graph_root_input_check :
    ∀ ell ∈ coldCheckedGraphLags, coldGraphChoiceAt ell ≠ 0 →
      coldGraphSqrtInputAt ell = coldGraphRadicand ell := by
  decide +kernel

end ASDExplicitGamma.Numerics.Cold
