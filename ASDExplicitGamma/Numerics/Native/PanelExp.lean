module
public import ASDExplicitGamma.Numerics.Native.LogThree
public import ASDExplicitGamma.Numerics.Mirror.Composition
import Mathlib.Tactic.NormNum

/-! Direct small-argument exponential mirrors for native setup graphs.
All native setup arguments lie in [-1,1]; a degree-60 Taylor enclosure avoids the
large unreduced denominators of scaling to 1/50 and raising to the fiftieth power.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.Mirror

def nativePanelExpLo (q : ℚ) : ℚ := roundDown 60 (expPolyQ q 60-expErrQ q 60)
def nativePanelExpHi (q : ℚ) : ℚ := roundUp 60 (expPolyQ q 60+expErrQ q 60)

theorem nativePanelExpPoint_sound (q : ℚ) (hq : -1 ≤ q ∧ q ≤ 1) :
    (nativePanelExpLo q : ℝ) ≤ Real.exp q ∧ Real.exp q ≤ (nativePanelExpHi q : ℝ) := by
  have hqR : |(q : ℝ)| ≤ 1 := by exact_mod_cast (abs_le.mpr hq)
  have h := exp_enclosure_rat hqR (by decide : 0 < 60)
  constructor
  · apply le_trans _ h.1
    have hl := (Rat.cast_le (K := ℝ)).2 (roundDown_le 60 (expPolyQ q 60-expErrQ q 60))
    simpa only [nativePanelExpLo, Rat.cast_sub] using hl
  · apply le_trans h.2
    have hh := (Rat.cast_le (K := ℝ)).2 (le_roundUp 60 (expPolyQ q 60+expErrQ q 60))
    simpa only [nativePanelExpHi, Rat.cast_add] using hh

def nativePanelExp (a : QInterval) (hlo : -1 ≤ a.lo) (hhi : a.hi ≤ 1) : QInterval :=
  ⟨nativePanelExpLo a.lo,nativePanelExpHi a.hi,by
    have hl := (nativePanelExpPoint_sound a.lo ⟨hlo,a.valid.trans hhi⟩).1
    have hh := (nativePanelExpPoint_sound a.hi ⟨hlo.trans a.valid,hhi⟩).2
    have hm := Real.exp_le_exp.mpr (show (a.lo : ℝ) ≤ a.hi from by exact_mod_cast a.valid)
    exact_mod_cast hl.trans (hm.trans hh)⟩

theorem nativePanelExp_sound {a : QInterval} (hlo : -1 ≤ a.lo) (hhi : a.hi ≤ 1)
    {x : ℝ} (hx : QInterval.Contains a x) :
    QInterval.Contains (nativePanelExp a hlo hhi) (Real.exp x) := by
  have hl := (nativePanelExpPoint_sound a.lo ⟨hlo,a.valid.trans hhi⟩).1
  have hh := (nativePanelExpPoint_sound a.hi ⟨hlo.trans a.valid,hhi⟩).2
  exact ⟨hl.trans (Real.exp_le_exp.mpr hx.1),(Real.exp_le_exp.mpr hx.2).trans hh⟩

def nativeInstructionGrid (env : ℕ → QInterval) (e : Expr) : Option QInterval :=
  match e with
  | .exp arg => do
    let a ← evalGrid 60 60 (by decide) env arg
    if hlo : -1 ≤ a.lo then
      if hhi : a.hi ≤ 1 then return nativePanelExp a hlo hhi else none
    else none
  | _ => evalGrid 60 60 (by decide) env e

theorem nativeInstructionGrid_sound (envI : ℕ → QInterval) (envR : ℕ → ℝ)
    (henv : ∀ i, QInterval.Contains (envI i) (envR i)) (e : Expr) (out : QInterval)
    (h : nativeInstructionGrid envI e = some out) : QInterval.Contains out (evalReal envR e) := by
  cases e with
  | exp arg =>
    cases ha : evalGrid 60 60 (by decide) envI arg with
    | none => simp [nativeInstructionGrid, ha] at h
    | some a =>
      by_cases hlo : -1 ≤ a.lo
      · by_cases hhi : a.hi ≤ 1
        · have he : nativePanelExp a hlo hhi = out := by simpa [nativeInstructionGrid, ha, hlo, hhi] using h
          rw [← he]
          exact nativePanelExp_sound hlo hhi (evalGrid_sound 60 60 (by decide) envI envR henv arg a ha)
        · simp [nativeInstructionGrid, ha, hlo, hhi] at h
      · simp [nativeInstructionGrid, ha, hlo] at h
  | const q | var i | neg arg | add a b | sub a b | mul a b | divPos a b | sqrt arg =>
    exact evalGrid_sound 60 60 (by decide) envI envR henv _ out h

end ASDExplicitGamma.Numerics.Native
