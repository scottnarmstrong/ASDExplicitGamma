module

public import ASDExplicitGamma.Numerics.Spike.MainCertTypes
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# Cold recurrence constants and scalar radical facts

The rational constants are the inputs of NU-CO-COLD-LAGS. The parameter rows are fixed rationals, rounded up at
precision `10⁻⁶`, one for each even lag from 4 through 40; the lag-40 row is reused for every later update.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

/-- Inputs in NU-CO-COLD-LAGS: `a`, `S`, and the root multiple
are given by the displayed rational defaults. -/
def coldA : ℚ := 3 / 50
def coldS20 : ℚ := 2379 / 2500
def coldR20 : ℚ := 2013 / 10000
def coldL0 : ℚ := 5673 / 50000
/-- The fixed outward grid. -/
def coldScale : ℕ := 10 ^ 42

/-- A per-lag tuple `(c,t,eta,lambda)` of fixed rationals, for the even lags 4 through 40. -/
structure ColdParams where
  c : ℚ
  t : ℚ
  eta : ℚ
  lambda : ℚ
  deriving DecidableEq, Repr

/-- Frozen rows for even lags 4 through 40, in file/key order; the four entries in each tuple
are precisely the source fields `c`, `t`, `eta`, and `lambda`. -/
def frozenParameterRows : List ColdParams := [
  ⟨1001/1000000, 10001/1000000, 1738945/1000000, 2007426/1000000⟩,
  ⟨132005/1000000, 514440/1000000, 510045/1000000, 1679507/1000000⟩,
  ⟨247956/1000000, 1400146/1000000, 384141/1000000, 1601016/1000000⟩,
  ⟨292799/1000000, 1684512/1000000, 342171/1000000, 1568849/1000000⟩,
  ⟨298872/1000000, 1709176/1000000, 304079/1000000, 1544213/1000000⟩,
  ⟨308635/1000000, 1652997/1000000, 274879/1000000, 1526199/1000000⟩,
  ⟨313679/1000000, 1626532/1000000, 249679/1000000, 1510003/1000000⟩,
  ⟨320555/1000000, 1615802/1000000, 229815/1000000, 1496480/1000000⟩,
  ⟨325856/1000000, 1621276/1000000, 213643/1000000, 1484897/1000000⟩,
  ⟨330958/1000000, 1629923/1000000, 200811/1000000, 1475507/1000000⟩,
  ⟨335103/1000000, 1643891/1000000, 190417/1000000, 1467805/1000000⟩,
  ⟨338938/1000000, 1660805/1000000, 182015/1000000, 1461657/1000000⟩,
  ⟨342325/1000000, 1681218/1000000, 175112/1000000, 1456663/1000000⟩,
  ⟨345477/1000000, 1703984/1000000, 169340/1000000, 1452678/1000000⟩,
  ⟨348384/1000000, 1729207/1000000, 164449/1000000, 1449454/1000000⟩,
  ⟨351156/1000000, 1756307/1000000, 160193/1000000, 1446766/1000000⟩,
  ⟨353799/1000000, 1785109/1000000, 156430/1000000, 1444550/1000000⟩,
  ⟨356361/1000000, 1815364/1000000, 153010/1000000, 1442686/1000000⟩,
  ⟨358854/1000000, 1847110/1000000, 149866/1000000, 1441070/1000000⟩
]

/-- Frozen parameters for each updating lag, with the row at 40 reused after 40. -/
def paramsForLag (j : ℕ) : ColdParams :=
  if j ≤ 40 then (frozenParameterRows.getD (j / 2 - 2) ⟨0, 1, 1, 1⟩)
  else frozenParameterRows.getD 18 ⟨0, 1, 1, 1⟩

/-- The certified lag-40 and lag-128 mean endpoints. -/
def coldD40Target : ℚ :=
  8566173929525767759063869940143157456937 /
    250000000000000000000000000000000000000000

def coldD128Target : ℚ :=
  4746175380618568409147666233793844275397 /
    1000000000000000000000000000000000000000000

/-- NU-CO-ROOT2 by exact integers. -/
theorem coldRoot2_integer_check :
    5673 ^ 19 * 50 ^ 9 * 10000 ^ 10 ≥ 50000 ^ 19 * 3 ^ 9 * 2013 ^ 10 := by
  decide +kernel

theorem coldRoot2 : coldL0 ^ 19 ≥ coldA ^ 9 * coldR20 ^ 10 := by
  norm_num [coldL0, coldA, coldR20]

/-- NU-CO-SQRT3-BOUND: the rational radical replacement used in the tail. -/
theorem sqrtThree_lt_twentySixOverFifteen : Real.sqrt 3 < (26 / 15 : ℝ) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsq : (Real.sqrt 3) ^ 2 < (26 / 15 : ℝ) ^ 2 := by rw [hs]; norm_num
  exact (sq_lt_sq₀ (Real.sqrt_nonneg 3) (by positivity)).1 hsq

/-- The D40 bridge to the fixed-point input used by N2's composition. -/
theorem coldD40_le_mainReturnInput :
    coldD40Target ≤ (Spike.cold40Upper : ℚ) / 10 ^ 32 := by
  norm_num [coldD40Target, Spike.cold40Upper]

theorem coldD128_lt_oneTwoHundred : coldD128Target < 1 / 200 := by
  norm_num [coldD128Target]

end ASDExplicitGamma.Numerics.Cold
