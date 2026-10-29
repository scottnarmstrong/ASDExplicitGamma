module

public import ASDExplicitGamma.Native.HeatStepPassNum
public import ASDExplicitGamma.Native.HeatVHEATNumericAdapter
public import ASDExplicitGamma.Native.HeatVHEATBounds

/-! For every `ns` carrying its pass certificates, the stable VHEAT error row at the OLD
local bank (`b = 3683/2500`, `ε = 3·10⁻⁴⁶`), at the configured frame caps `X = frames.x`,
`F = frames.raw` and at an arbitrary nonnegative average cap `y`, is bounded by the rounded
configured forcing row at the same `y`; the drift coefficient may be any `0 ≤ e ≤ old.e`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The fixed row is the vector of the `FixedAt` rows. -/
theorem nativeHeatFixedGen_getD (ns k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (nativeHeatFixedGen ns).getD (k - 1) 0 =
      nativeHeatFixedAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns) k := by
  unfold nativeHeatFixedGen
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  congr 1
  omega

/-- The frames with an updated average cap `y`: only `y` changes. -/
private theorem forcingAt_frames_y (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed : List ℚ) (y y' : ℚ) (k : ℕ) :
    nativeHeatForcingAt old { frames with y := y' } fixed y k =
      nativeHeatForcingAt old frames fixed y k := rfl

/-- The reserve change `b : 3683/2500 → nativeHeatB`, `ε : 3·10⁻⁴⁶ → nativeHeatEps`. -/
theorem nativeHeatStep_reserve_error_le_numeric (k : ℕ) (e X Y F : ℝ)
    (he : 0 ≤ e) (hX : 0 < X) (hY : 0 ≤ Y) (hF : 0 ≤ F) :
    nativeHeatVHEATErrorEk k 20 e nativeHeatK nativeHeatM nativeHeatSB nativeHeatTheta
      (3683 / 2500) X Y (3 / 10 ^ 46) F ≤
    nativeHeatVHEATErrorEk k 20 e nativeHeatK nativeHeatM nativeHeatSB nativeHeatTheta
      nativeHeatB X Y nativeHeatEps F := by
  have hb := nativeHeatVHEATErrorEk_mono_b k 20 e nativeHeatK nativeHeatM nativeHeatSB
    nativeHeatTheta (3683 / 2500) nativeHeatB X Y (3 / 10 ^ 46) F he
    (by norm_num [nativeHeatM]) (by norm_num [nativeHeatSB]) (by norm_num [nativeHeatTheta])
    (by norm_num) (by norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB])
    hX hY (by positivity) hF
  apply hb.trans
  exact nativeHeatVHEATErrorEk_mono_eps k 20 e nativeHeatK nativeHeatM nativeHeatSB
    nativeHeatTheta nativeHeatB X Y F (3 / 10 ^ 46) nativeHeatEps he
    (by norm_num [nativeHeatK]) (by norm_num [nativeHeatM]) (by norm_num [nativeHeatSB])
    (by norm_num [nativeHeatTheta])
    (by norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB])
    hX hF (by positivity)
    (by norm_num [nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeEps])

/-- Generic form: the error row at the configured numeric reserve is below the configured
forcing row at the same updated cap `y`, for any data whose fixed row is the `FixedAt` row. -/
theorem nativeHeatStep_numericError_le_forcingAt_of (old : NativeOldRow)
    (frames : NativeHeatFrameInputs) (fixed : List ℚ)
    (hfix : ∀ k, 1 ≤ k → k ≤ 20 → fixed.getD (k - 1) 0 = nativeHeatFixedAt old frames k)
    (hold0 : 0 ≤ old.e) (hx0 : 0 < frames.x) (hraw0 : 0 ≤ frames.raw)
    (root5 : nativeRootValid ((frames.raw / frames.x) ^ 5) 27 = true)
    (root10 : nativeRootValid ((frames.raw / frames.x) ^ 10) 27 = true)
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) (y : ℚ) :
    nativeHeatVHEATErrorEk k 20 (old.e : ℝ)
        (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ)
        (nativeHeatB : ℝ) (frames.x : ℝ) (y : ℝ)
        (nativeHeatEps : ℝ) (frames.raw : ℝ) ≤
      (nativeHeatForcingAt old frames fixed y k : ℚ) := by
  let framesY : NativeHeatFrameInputs := { frames with y := y }
  have hFixedAt : ∀ k', 1 ≤ k' → k' ≤ 20 →
      nativeHeatFixedAnalyticRemainder old framesY k' ≤ fixed.getD (k' - 1) 0 := by
    intro k' h1 h20
    have e1 : nativeHeatFixedAnalyticRemainder old framesY k' =
        nativeHeatFixedAnalyticRemainder old frames k' := rfl
    rw [e1, hfix k' h1 h20, nativeHeatFixedAt_eq_explicit_remainder]
    exact nativeUp_ge _
  by_cases h₁ : k = 1
  · subst k
    have hrow := nativeHeatVHEATErrorEk_one_le_fixedAt old frames hold0 hx0.le
    have hY1 : nativeHeatVHEATErrorEk 1 20 (old.e : ℝ) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
        (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ) (y : ℝ)
        (nativeHeatEps : ℝ) (frames.raw : ℝ) =
        nativeHeatVHEATErrorEk 1 20 (old.e : ℝ) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
        (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (nativeHeatB : ℝ) (frames.x : ℝ) 0
        (nativeHeatEps : ℝ) (frames.raw : ℝ) := by
      simp [nativeHeatVHEATErrorEk]
    rw [hY1]
    have hfx : nativeHeatFixedAt old frames 1 = fixed.getD 0 0 := (hfix 1 le_rfl (by norm_num)).symm
    have hle : nativeHeatFixedAt old frames 1 ≤ nativeHeatForcingAt old frames fixed y 1 := by
      rw [hfx]
      simp only [nativeHeatForcingAt]
      simpa using nativeUp_ge (fixed.getD 0 0)
    exact hrow.trans (by exact_mod_cast hle)
  · by_cases h₂₀ : k = 20
    · subst k
      have hf20 := hFixedAt 20 (by norm_num) le_rfl
      have := nativeHeatVHEATErrorEk_top_le_forcingAt old framesY fixed hold0
        (by simpa [framesY] using hx0) (by simpa [framesY] using hraw0)
        (by simpa [framesY] using root5) (by simpa [framesY] using root10)
        (by simpa [nativeHeatFixedAnalyticRemainder, nativeHeatRareJ, framesY] using hf20)
      simpa [framesY, forcingAt_frames_y] using this
    · have hk2 : 2 ≤ k := by omega
      have hkp : k < 20 := by omega
      have := nativeHeatVHEATErrorEk_le_forcingAt_of_lt old framesY fixed k hk2 hkp hold0
        (by simpa [framesY] using hx0.le)
        (by simpa [nativeHeatFixedAnalyticRemainder, nativeHeatRareJ, framesY] using
          hFixedAt k hk1 hk20)
      simpa [framesY, forcingAt_frames_y] using this

/-- The VHEAT error at the OLD local bank, the source drift `e ≤ old.e` and the configured
caps `X`, `F`, at the updated average cap `y`, is bounded by the configured forcing row. -/
theorem nativeHeatStep_vheatError_le_forcingAt (ns : ℕ) (hnum : NativeHeatStepPassNum ns)
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) (e : ℝ) (he0 : 0 ≤ e)
    (he : e ≤ ((nativeHeatOldRowGen ns).e : ℝ)) (y : ℚ) (hy : 0 ≤ y) :
    nativeHeatVHEATErrorEk k 20 e (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
        (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ) ((nativeHeatFramesGen ns).x : ℝ) (y : ℝ)
        (3 / 10 ^ 46 : ℝ) ((nativeHeatFramesGen ns).raw : ℝ) ≤
      (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
        (nativeHeatFixedGen ns) y k : ℚ) := by
  have hx0 : (0 : ℝ) < ((nativeHeatFramesGen ns).x : ℝ) := by exact_mod_cast hnum.x_pos
  have hraw0 : (0 : ℝ) ≤ ((nativeHeatFramesGen ns).raw : ℝ) := by
    exact_mod_cast hnum.raw_nonneg
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have h1 := nativeHeatVHEATErrorEk_mono_drift_remainder k 20 e ((nativeHeatOldRowGen ns).e : ℝ)
    (nativeHeatK : ℝ) (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatM : ℝ)
    (nativeHeatSB : ℝ) (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
    ((nativeHeatFramesGen ns).x : ℝ) (y : ℝ) (3 / 10 ^ 46 : ℝ)
    ((nativeHeatFramesGen ns).raw : ℝ) he0 he (by norm_num [nativeHeatK]) le_rfl
    (by norm_num [nativeHeatM]) le_rfl (by norm_num [nativeHeatSB]) le_rfl
    (by norm_num [nativeHeatTheta]) (by norm_num) hx0 hy0 (by positivity) hraw0
  have h2 := nativeHeatStep_reserve_error_le_numeric k ((nativeHeatOldRowGen ns).e : ℝ)
    ((nativeHeatFramesGen ns).x : ℝ) (y : ℝ) ((nativeHeatFramesGen ns).raw : ℝ)
    (by exact_mod_cast hnum.old_e_nonneg) hx0 hy0 hraw0
  exact h1.trans (h2.trans (nativeHeatStep_numericError_le_forcingAt_of _ _ _
    (fun k' h1' h20' => nativeHeatFixedGen_getD ns k' h1' h20') hnum.old_e_nonneg hnum.x_pos
    hnum.raw_nonneg hnum.root5 hnum.root10 k hk1 hk20 y))

end ASDExplicitGamma.Native

end
