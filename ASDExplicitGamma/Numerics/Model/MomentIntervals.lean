module

public import ASDExplicitGamma.Numerics.Model.TightInterval
public import ASDExplicitGamma.Numerics.Model.FourierMoments

/-! A linear Fourier-moment interval recurrence with its exact integral meaning. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
open Mirror

def momentIntervals (G : ℕ) (w s c : QInterval) (hw : 0 < w.lo) : ℕ → QInterval × QInterval
  | 0 => (tightDiv G s w hw, tightDiv G (sub G (gridConstant G 1) c) w hw)
  | n+1 =>
    let p := momentIntervals G w s c hw n
    let k := gridConstant G ((n : ℚ)+1)
    (tightDiv G (sub G s (tightMul G k p.2)) w hw,
      tightDiv G (add G (neg G c) (tightMul G k p.1)) w hw)

theorem moment_intervals_sound (G : ℕ) (w s c : QInterval) (hw : 0 < w.lo)
    (z : ℝ) (hz : QInterval.Contains w z)
    (hs : QInterval.Contains s (Real.sin z)) (hc : QInterval.Contains c (Real.cos z))
    (n : ℕ) :
    QInterval.Contains (momentIntervals G w s c hw n).1 (cosineMoment z n) ∧
    QInterval.Contains (momentIntervals G w s c hw n).2 (sineMoment z n) := by
  have hzpos : 0 < z := (by exact_mod_cast hw : (0 : ℝ) < (w.lo : ℝ)).trans_le hz.1
  induction n with
  | zero =>
    constructor
    · rw [cosine_moment_zero z hzpos.ne']
      exact tightDiv_sound G hs hw hz
    · rw [sine_moment_zero z hzpos.ne']
      have h1 : QInterval.Contains (gridConstant G 1) (1 : ℝ) := by
        simpa using gridConstant_sound G 1
      exact tightDiv_sound G (sub_sound G h1 hc) hw hz
  | succ n ih =>
    have hk : QInterval.Contains (gridConstant G ((n : ℚ)+1)) ((n : ℝ)+1) := by
      simpa only [Rat.cast_add,Rat.cast_natCast,Rat.cast_one] using gridConstant_sound G ((n : ℚ)+1)
    constructor
    · rw [cosine_moment_succ z hzpos.ne' n]
      simpa only [momentIntervals] using
        tightDiv_sound G (sub_sound G hs (tightMul_sound G hk ih.2)) hw hz
    · rw [sine_moment_succ z hzpos.ne' n]
      simpa only [momentIntervals] using
        tightDiv_sound G (add_sound G (neg_sound G hc) (tightMul_sound G hk ih.1)) hw hz

end ASDExplicitGamma.Numerics.Model
