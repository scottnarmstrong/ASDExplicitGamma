module

public import ASDExplicitGamma.Numerics.Mirror.Composition

/-! Scalar expressions use certified π and log 3 inputs and the grid mirror. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Scalar

open Mirror

/-- The two transcendental inputs of the scalar formulas. -/
noncomputable def scalarRealEnv (i : ℕ) : ℝ :=
  if i = 0 then Real.pi else Real.log 3

/-- Outward enclosures of precisely the same two inputs. -/
def scalarGridEnv (i : ℕ) : QInterval :=
  if i = 0 then
    ⟨3.14159265358979323846, 3.14159265358979323847, by norm_num⟩
  else logThreeRaw

theorem scalar_env_sound (i : ℕ) :
    QInterval.Contains (scalarGridEnv i) (scalarRealEnv i) := by
  by_cases hi : i = 0
  · simpa [scalarGridEnv, scalarRealEnv, hi, QInterval.Contains] using
      ⟨pi_enclosure.1.le, pi_enclosure.2.le⟩
  · simpa [scalarGridEnv, scalarRealEnv, hi] using logThreeRaw_sound

/-- Check a strict upper endpoint using 32 decimal digits. -/
def scalarUpperCheck (e : Expr) (u : ℚ) : Bool :=
  match evalGrid 32 25 (by decide) scalarGridEnv e with
  | none => false
  | some i => decide (i.hi < u)

/-- The Boolean checks an enclosure of the real formula, rather than supplied endpoints. -/
theorem scalar_upper_sound (e : Expr) (u : ℚ) (h : scalarUpperCheck e u = true) :
    evalReal scalarRealEnv e < (u : ℝ) := by
  unfold scalarUpperCheck at h
  cases he : evalGrid 32 25 (by decide) scalarGridEnv e with
  | none => simp only [he, Bool.false_eq_true] at h
  | some i =>
    rw [he] at h
    have hu : i.hi < u := of_decide_eq_true h
    exact (evalGrid_sound 32 25 (by decide) scalarGridEnv scalarRealEnv
      scalar_env_sound e i he).2.trans_lt (by exact_mod_cast hu)

end ASDExplicitGamma.Numerics.Scalar

namespace ASDExplicitGamma.Numerics.Scalar
open Mirror

end ASDExplicitGamma.Numerics.Scalar

namespace ASDExplicitGamma.Numerics.Scalar

/-- Pointwise soundness of a finite collection of arithmetic inputs, including unused slots. -/
theorem contains_getD {is : List QInterval} {xs : List ℝ}
    (h : List.Forall₂ QInterval.Contains is xs) (j : ℕ) :
    QInterval.Contains (is.getD j (QInterval.point 0)) (xs.getD j 0) := by
  induction h generalizing j with
  | nil => simp only [List.getD_nil]; norm_num [QInterval.Contains, QInterval.point]
  | cons h hs ih =>
    cases j with
    | zero => simpa only [List.getD_cons_zero] using h
    | succ j => simpa only [List.getD_cons_succ] using ih j

end ASDExplicitGamma.Numerics.Scalar
