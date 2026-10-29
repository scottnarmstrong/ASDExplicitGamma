module

public import ASDExplicitGamma.Numerics.Cold.Bounds
public import ASDExplicitGamma.Numerics.Cold.ScalarEnclosures

/-! The finite outward replay of the cold depth-history caps. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

def coldAlphaPowUpper (n : ℕ) : ℚ := coldAlphaPowerUpperData.getD n 0

def coldAlphaPowLower (n : ℕ) : ℚ := coldAlphaPowerLowerData.getD n 0

def coldBetaPowUpper (n : ℕ) : ℚ := coldBetaPowerUpperData.getD n 0

theorem cold_power_tables_check :
    coldAlphaPowUpper 0 = 1 ∧ coldAlphaPowLower 0 = 1 ∧ coldBetaPowUpper 0 = 1 ∧
    (∀ n ∈ List.range 128,
      coldAlphaPowUpper (n+1) = coldRoundUp (coldAlphaPowUpper n*coldAlphaUpper) ∧
      coldAlphaPowLower (n+1) = coldRoundDown (coldAlphaPowLower n*coldAlphaLower) ∧
      coldBetaPowUpper (n+1) = coldRoundUp (coldBetaPowUpper n*coldBetaUpper)) := by
  decide +kernel

def coldOneMinusAlphaUpper : ℚ := coldRoundUp (1-coldAlphaLower)

def coldHistoryE (k d : ℕ) : ℚ :=
  min (coldMomentAt k) (coldSqrt19Upper*coldDecay d*coldMomentAt k)

def coldHistoryOldTerm (j : ℕ) : ℚ :=
  let cutoffSum := coldListSum (List.range j) (fun r =>
    coldUpMul (coldBetaPowUpper r)
      (min 1 (coldRoundUp (2*coldSqrt19Upper*coldDecay (j-r)))) )
  let termA := coldUpMul (coldRoundUp coldA)
    (coldRoundUp (1-coldAlphaPowLower j))
  let termB := coldUpMul
    (coldUpMul coldOneMinusAlphaUpper (coldRoundUp coldR20)) cutoffSum
  let termS := coldUpMul (coldBetaPowUpper j) (coldRoundUp coldS20)
  coldUpAdd (coldUpAdd termA termB) termS

def coldHistoryChoice (j r : ℕ) : ℚ :=
  let ell := j-r
  let raw := coldUpMul (coldBetaPowUpper r) (coldRoundUp (coldMomentAt ell))
  (List.range (min ell (j-1)+1)).foldl (fun best k =>
    let transported := coldUpAdd
      (coldUpMul (coldAlphaPowUpper r) (coldRoundUp (coldMeanAt k)))
      (coldUpMul (coldBetaPowUpper r) (coldRoundUp (coldHistoryE k (ell-k))))
    min best transported) raw

def coldHistoryWeightedSum (j : ℕ) : ℚ :=
  (List.range j).foldl (fun hist r =>
    coldUpAdd hist (coldHistoryChoice j r)) 0

def coldHistoryExpected (j : ℕ) : ℚ :=
  min coldS20 (min (coldHistoryOldTerm j)
    (coldUpAdd (coldUpMul coldOneMinusAlphaUpper (coldHistoryWeightedSum j))
      (coldUpMul (coldBetaPowUpper j) (coldRoundUp coldS20))))

theorem coldOneMinusAlphaUpper_bound :
    (1-coldAlphaLower : ℚ) ≤ coldOneMinusAlphaUpper := by
  have hs : 0 < (coldScale : ℚ) := by norm_num [coldScale]
  have hceil := Int.le_ceil ((coldScale : ℚ)*(1-coldAlphaLower))
  apply (le_div_iff₀ hs).2
  simpa [coldOneMinusAlphaUpper, coldRoundUp, mul_comm] using hceil

theorem coldOneMinusAlpha_sound :
    1-coldAlphaReal ≤ (coldOneMinusAlphaUpper : ℝ) := by
  have hreal : 1-coldAlphaReal ≤ 1-(coldAlphaLower : ℝ) := by
    linarith [coldAlpha_interval_sound.1]
  have hround : 1-(coldAlphaLower : ℝ) ≤ (coldOneMinusAlphaUpper : ℝ) := by
    exact_mod_cast coldOneMinusAlphaUpper_bound
  exact hreal.trans hround

end ASDExplicitGamma.Numerics.Cold
