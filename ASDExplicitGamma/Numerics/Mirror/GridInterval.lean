module

public import ASDExplicitGamma.Numerics.QInterval
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Rat.Floor

/-!
# Grid-rounded rational intervals

Each operation is performed by the existing rational interval arithmetic and then rounded
outward to the grid `10⁻ᴳ`. Soundness is independent of the size of the integer numerators.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Mirror

open ASDExplicitGamma.Numerics

/-- The positive rational scale for a grid with `G` decimal places. -/
def gridScale (G : ℕ) : ℚ := (10 : ℚ) ^ G

theorem gridScale_pos (G : ℕ) : 0 < gridScale G := by
  unfold gridScale
  positivity

/-- Round a rational down to the grid with `G` decimal places. -/
def roundDown (G : ℕ) (q : ℚ) : ℚ :=
  (⌊gridScale G * q⌋ : ℤ) / gridScale G

/-- Round a rational up to the grid with `G` decimal places. -/
def roundUp (G : ℕ) (q : ℚ) : ℚ :=
  (⌈gridScale G * q⌉ : ℤ) / gridScale G

theorem roundDown_le (G : ℕ) (q : ℚ) : roundDown G q ≤ q := by
  have h := Int.floor_le (gridScale G * q)
  apply (div_le_iff₀ (gridScale_pos G)).2
  simpa [roundDown, mul_comm] using h

theorem le_roundUp (G : ℕ) (q : ℚ) : q ≤ roundUp G q := by
  have h := Int.le_ceil (gridScale G * q)
  apply (le_div_iff₀ (gridScale_pos G)).2
  simpa [roundUp, mul_comm] using h

/-- Outward grid rounding of a rational interval. -/
def round (G : ℕ) (i : QInterval) : QInterval :=
  ⟨roundDown G i.lo, roundUp G i.hi,
    (roundDown_le G i.lo).trans (i.valid.trans (le_roundUp G i.hi))⟩

theorem round_contains (G : ℕ) {i : QInterval} {x : ℝ}
    (hx : QInterval.Contains i x) : QInterval.Contains (round G i) x := by
  change (i.lo : ℝ) ≤ x ∧ x ≤ i.hi at hx
  change (roundDown G i.lo : ℝ) ≤ x ∧ x ≤ roundUp G i.hi
  have hlo : (roundDown G i.lo : ℝ) ≤ i.lo := by
    exact_mod_cast roundDown_le G i.lo
  have hhi : (i.hi : ℝ) ≤ roundUp G i.hi := by
    exact_mod_cast le_roundUp G i.hi
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- Grid-rounded addition. -/
def add (G : ℕ) (a b : QInterval) : QInterval :=
  round G (QInterval.add a b)

theorem add_sound (G : ℕ) {a b : QInterval} {x y : ℝ}
    (hx : QInterval.Contains a x) (hy : QInterval.Contains b y) :
    QInterval.Contains (add G a b) (x + y) :=
  round_contains G (QInterval.add_sound hx hy)

/-- The exact rational interval opposite, used before outward rounding. -/
def negRaw (a : QInterval) : QInterval :=
  ⟨-a.hi, -a.lo, neg_le_neg a.valid⟩

/-- Grid-rounded negation. -/
def neg (G : ℕ) (a : QInterval) : QInterval := round G (negRaw a)

theorem negRaw_sound {a : QInterval} {x : ℝ}
    (hx : QInterval.Contains a x) : QInterval.Contains (negRaw a) (-x) := by
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at hx
  simp only [QInterval.Contains, negRaw, Rat.cast_neg]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem neg_sound (G : ℕ) {a : QInterval} {x : ℝ}
    (hx : QInterval.Contains a x) : QInterval.Contains (neg G a) (-x) :=
  round_contains G (negRaw_sound hx)

/-- Grid-rounded subtraction. -/
def sub (G : ℕ) (a b : QInterval) : QInterval :=
  round G (QInterval.add a (negRaw b))

theorem sub_sound (G : ℕ) {a b : QInterval} {x y : ℝ}
    (hx : QInterval.Contains a x) (hy : QInterval.Contains b y) :
    QInterval.Contains (sub G a b) (x - y) := by
  have h := QInterval.add_sound hx (negRaw_sound hy)
  change QInterval.Contains (round G (QInterval.add a (negRaw b))) (x - y)
  rw [sub_eq_add_neg]
  exact round_contains G h

/-- Grid-rounded multiplication. -/
def mul (G : ℕ) (a b : QInterval) : QInterval :=
  round G (QInterval.mul a b)

theorem mul_sound (G : ℕ) {a b : QInterval} {x y : ℝ}
    (hx : QInterval.Contains a x) (hy : QInterval.Contains b y) :
    QInterval.Contains (mul G a b) (x * y) :=
  round_contains G (QInterval.mul_sound hx hy)

/-- Grid-rounded division by an interval with positive lower endpoint. -/
def divPos (G : ℕ) (a b : QInterval) (hb : 0 < b.lo) : QInterval :=
  round G (QInterval.divPos a b hb)

theorem divPos_sound (G : ℕ) {a b : QInterval} {x y : ℝ}
    (ha : QInterval.Contains a x) (hb : 0 < b.lo)
    (hy : QInterval.Contains b y) :
    QInterval.Contains (divPos G a b hb) (x / y) :=
  round_contains G (QInterval.divPos_sound ha hb hy)

/-- A rational constant rounded to the requested grid. -/
def gridConstant (G : ℕ) (q : ℚ) : QInterval := round G (QInterval.point q)

theorem gridConstant_sound (G : ℕ) (q : ℚ) :
    QInterval.Contains (gridConstant G q) (q : ℝ) := by
  apply round_contains G
  simp [QInterval.Contains, QInterval.point]

end ASDExplicitGamma.Numerics.Mirror
