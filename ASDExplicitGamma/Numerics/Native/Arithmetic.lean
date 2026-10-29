module
public import ASDExplicitGamma.Numerics.Native.Basic
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Rat.Floor

/-! Exact outward scalar operations for the native replay.
Root candidates use Newton iteration from a bit-length seed. Each consumed root is also
checked by powers; soundness uses those checks, independently of Newton convergence.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeScale : ℕ := 10^100
def nativeRootScale : ℕ := 10^90

def nativeUp (q : ℚ) : ℚ := (⌈q*(nativeScale : ℚ)⌉ : ℤ)/(nativeScale : ℚ)

/-- Fast candidate for the floor nth root. The computational witness is verified separately. -/
def nativeRootCandidate (n a : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 1 then a else
  Nat.nthRoot.go (n-2) a (a+1) (2^((a.log2+n)/n))

/-- Strict upward grid root, with the producer's exact zero branch. -/
def nativeRootUp (q : ℚ) (n : ℕ := 2) : ℚ :=
  if q = 0 then 0 else
  let m := Int.toNat ⌊q*(nativeRootScale : ℚ)^n⌋
  ((nativeRootCandidate n m+1 : ℕ) : ℚ)/(nativeRootScale : ℚ)

/-- A numeric root is usable only with this explicit outward-power certificate. -/
def nativeRootValid (q : ℚ) (n : ℕ) : Bool :=
  decide (0 < n ∧ 0 ≤ q ∧ 0 ≤ nativeRootUp q n ∧ q ≤ (nativeRootUp q n)^n)

theorem nativeUp_ge (q : ℚ) : q ≤ nativeUp q := by
  have hs : (0 : ℚ) < nativeScale := by decide +kernel
  apply (le_div_iff₀ hs).2
  exact (Int.le_ceil (q*(nativeScale : ℚ)))

/-- The real root enclosure follows from its checked powers, not from an algorithm axiom. -/
theorem nativeRoot_sound {q : ℚ} {n : ℕ} (h : nativeRootValid q n = true) :
    (q : ℝ)^((n : ℝ)⁻¹) ≤ (nativeRootUp q n : ℝ) := by
  have hs : 0 < n ∧ 0 ≤ q ∧ 0 ≤ nativeRootUp q n ∧ q ≤ (nativeRootUp q n)^n :=
    of_decide_eq_true h
  have hq : (0 : ℝ) ≤ q := by exact_mod_cast hs.2.1
  have hu : (0 : ℝ) ≤ nativeRootUp q n := by exact_mod_cast hs.2.2.1
  have hp : (q : ℝ) ≤ (nativeRootUp q n : ℝ)^n := by exact_mod_cast hs.2.2.2
  have hr := Real.rpow_le_rpow hq hp (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  simpa only [Real.pow_rpow_inv_natCast hu (Nat.ne_of_gt hs.1)] using hr

end ASDExplicitGamma.Numerics.Native
