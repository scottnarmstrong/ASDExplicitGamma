module

public import ASDExplicitGamma.Numerics.Cold.Data
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor

/-!
# Exact rational recurrence and kernel replay

`coldHistoryData` and `coldGraphData` are the checked outward endpoints for the history and
graph caps produced by the independent exact-rational transcription.  The update below spells
out NU-CO-COLD-LAGS: the transport weights and tail, the q/F and plateau parameters, and the 10^42 scale. The
129-lag mean table is accepted only after each of its 63 updates is checked by the kernel.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

def coldListSum (xs : List ℕ) (f : ℕ → ℚ) : ℚ :=
  xs.foldl (fun acc i => acc + f i) 0

def coldUpdatedLags : List ℕ := (List.range 63).map (fun i => 4 + 2*i)

def coldMeanAt (j : ℕ) : ℚ := coldMeanData.getD j 0
def coldMomentAt (j : ℕ) : ℚ := coldMomentData.getD j 0
def coldHistoryAt (j : ℕ) : ℚ := coldHistoryData.getD j 0
def coldInterpolationAt (j : ℕ) : ℚ := coldInterpolationData.getD j 0
def coldGraphAt (j : ℕ) : ℚ := coldGraphData.getD j 0

/-- The transport weights `w_r`, for even `r ≥ 2`. -/
def coldWeight (r : ℕ) : ℚ :=
  if r = 2 then 53 / 72 else 28 / (9 : ℚ) ^ (r / 2)

def coldCT (j : ℕ) : ℚ := 4 / (7 * (1 - (paramsForLag j).c))
def coldCD (j : ℕ) : ℚ := 96 / 49 / (paramsForLag j).c - 1
def coldG0 (j : ℕ) : ℚ := 2 * (1 + (paramsForLag j).eta)
def coldG1 (j : ℕ) : ℚ := 2 + 1 / (4 * (paramsForLag j).eta)
def coldXi (j : ℕ) : ℚ := (paramsForLag j).lambda * coldHistoryAt j

/-- The q-coefficients, with the `sqrt 3` tail replaced by `26/15`
(see NU-CO-SQRT3-BOUND). -/
def coldQ (j r : ℕ) : ℚ :=
  2 * coldCT j * (1 + 1 / (paramsForLag j).t) *
    (coldG0 j + coldG1 j * coldXi j * (26 / 15 : ℚ) ^ (r / 2)) * coldWeight r +
    if r = 4 then coldCD j else 0

/-- `F_j` with the geometric tail ratio `z = 26/135`. -/
def coldFineTail (j : ℕ) : ℚ :=
  2 * coldCT j *
    (coldG0 j * (7 / 2 : ℚ) * (1 / 3 : ℚ) ^ j +
      coldG1 j * coldXi j * 28 * (26 / 135 : ℚ) ^ (j / 2 + 1) /
        (1 - 26 / 135 : ℚ))

def coldQSum (j : ℕ) : ℚ :=
  coldListSum ((List.range (j / 2)).map (fun i => 2 * (i + 1))) (coldQ j)

def coldWeightedMeans (j : ℕ) : ℚ :=
  coldListSum ((List.range (j / 2)).map (fun i => 2 * (i + 1)))
    (fun r => coldQ j r * coldMeanAt (j-r))

def coldGraphContribution (j : ℕ) : ℚ :=
  coldCT j * (1 + (paramsForLag j).t) *
    coldListSum ((List.range (j / 2)).map (fun i => 2 * (i + 1)))
      (fun r => coldWeight r * coldGraphAt (j-r))

def coldBadHistory (j : ℕ) : ℚ :=
  (55 / 4 : ℚ) * coldCT j * coldG1 j *
    (1 + 1 / (paramsForLag j).t) * coldHistoryAt j ^ 20 / coldXi j ^ 18

def coldNumerator (j : ℕ) : ℚ :=
  coldWeightedMeans j + coldGraphContribution j + coldBadHistory j

def coldDenominator (j : ℕ) : ℚ := 1 + coldQSum j - coldFineTail j

/-- Upward rounding on the `10^42` grid. -/
def coldRoundUp (x : ℚ) : ℚ :=
  (Int.ceil ((coldScale : ℚ) * x) : ℚ) / coldScale

/-- One exact outward lag update, including the nonincreasing cap. -/
def coldUpdate (j : ℕ) : ℚ :=
  min (coldMeanAt (j-2)) (coldRoundUp (coldNumerator j / coldDenominator j))

/-- The exact q/F/numerator/denominator transcription has positive denominators and reproduces
all 63 upward-rounded mean updates.  `coldHistoryData` and `coldGraphData` are the 1e-42
outward history/graph endpoints. -/
theorem cold_lags_kernel_replay :
    ∀ j ∈ coldUpdatedLags,
      0 < coldDenominator j ∧ coldMeanAt j = coldUpdate j := by
  decide +kernel

theorem coldD40_replay : coldMeanAt 40 = coldD40Target := by
  decide +kernel

theorem coldD128_replay : coldMeanAt 128 = coldD128Target := by
  decide +kernel

theorem coldD40_le_mainReturnInput_of_replay :
    coldMeanAt 40 ≤ (Spike.cold40Upper : ℚ) / 10 ^ 32 := by
  rw [coldD40_replay]
  exact coldD40_le_mainReturnInput

theorem coldD128_lt_oneTwoHundred_of_replay : coldMeanAt 128 < 1 / 200 := by
  rw [coldD128_replay]
  exact coldD128_lt_oneTwoHundred

end ASDExplicitGamma.Numerics.Cold
