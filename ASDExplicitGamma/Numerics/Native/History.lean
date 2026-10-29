module
public import ASDExplicitGamma.Numerics.Native.Heat
public import ASDExplicitGamma.Numerics.Native.FrameTheta
import Mathlib.Tactic.NormNum

/-! Complete finite history replay and its raw-tail arithmetic. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistorySteps (offset start : ℕ) : ℕ → List ℚ → ℚ × ℚ → ℚ × ℚ
  | 0, _, state => state
  | n+1, [], state => nativeHistorySteps offset (start+1) n []
      (nativeUp (state.1*nativeHistoryRatio),state.2)
  | n+1, t::ts, state => nativeHistorySteps offset (start+1) n ts
      (nativeUp (state.1*nativeHistoryRatio),
        state.2+nativeUp (nativeC0*state.1*nativeShiftedFrame (offset+start) t))

/-- The true source frame is below its independently power-checked outward replay. -/
theorem nativeShiftedFrame_sound (h : ℕ) (t : ℚ)
    (hd : 0 ≤ (11/10)*(2*nativeGamma*h) ∧ (11/10)*(2*nativeGamma*h) < 1)
    (hr : nativeRootValid (t*(t+8)) 2 = true) :
    nativeFrameReal (((11/10)*(2*nativeGamma*h) : ℚ) : ℝ) (t : ℝ) ≤
      (nativeShiftedFrame h t : ℝ) := by
  let r := nativeE (2*nativeGamma*h)
  let c := (r+1/r)/2
  let d := (r-1/r)/2
  have hden : (0 : ℚ) < 1-(11/10)*(2*nativeGamma*h) := sub_pos.mpr hd.2
  have hr1 : (1 : ℚ) ≤ r := by
    apply (le_div_iff₀ hden).2
    linarith only [hd.1]
  have hr0 : (0 : ℚ) < r := lt_of_lt_of_le (by norm_num) hr1
  have hinv : (1 : ℚ)/r ≤ 1 := (div_le_one hr0).2 hr1
  have hd0 : (0 : ℚ) ≤ d := by dsimp only [d]; linarith only [hr1,hinv]
  have hroot := of_decide_eq_true hr
  have hs : Real.sqrt ((t*(t+8) : ℚ) : ℝ) ≤ (nativeRootUp (t*(t+8)) : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact_mod_cast hroot.2.2.1
    · exact_mod_cast hroot.2.2.2
  have he : nativeFrameReal (((11/10)*(2*nativeGamma*h) : ℚ) : ℝ) (t : ℝ) =
      ((c*t+4*(c-1) : ℚ) : ℝ)+(d : ℝ)*Real.sqrt ((t*(t+8) : ℚ) : ℝ) := by
    simp only [nativeFrameReal,c,d,r,nativeE,Rat.cast_div,Rat.cast_sub,Rat.cast_mul,
      Rat.cast_add,Rat.cast_one,Rat.cast_ofNat]
    ring
  rw [he]
  have hm := add_le_add_right (mul_le_mul_of_nonneg_left hs (by exact_mod_cast hd0 : (0 : ℝ) ≤ d))
    (((c*t+4*(c-1) : ℚ) : ℝ))
  have hu := (Rat.cast_le (K := ℝ)).2 (nativeUp_ge (c*t+d*nativeRootUp (t*(t+8))+4*(c-1)))
  apply le_trans _ hu
  simpa only [Rat.cast_add,Rat.cast_mul,add_assoc,add_comm,add_left_comm] using hm

end ASDExplicitGamma.Numerics.Native
