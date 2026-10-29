module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 13, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross13Hn : ℚ := (7909871479731888315484336244264112229343436161747653472214317223218284812498171668653817231216378409/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross13Root : ℚ := (11278118561572542733735714451168398134205024360567598324025273203090849012841177448124816899/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross13U : ℚ := (131995946316786868886408043096012221227160894208991055331184802579784561569029114241819/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross13V : ℚ := (539943179880415731086173905202459818666483207293762352189164147060959743277782263239861829/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross13_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^220*500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^247 ≤ 11278118561572542733735714451168398134205024360567598324025273203090849012841177448124816899^247*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^220 := by
  decide +kernel

theorem nativeHeatCross13_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross13_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((220/247 : ℚ) : ℝ) ≤ (nativeHeatCross13Root : ℝ) := by
  rw [nativeHeatCross13_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 11278118561572542733735714451168398134205024360567598324025273203090849012841177448124816899 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 220 247 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross13_integer
  simpa only [nativeHeatCross13Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross13_hn_round : nativeUp (nativeQstar*nativeHeatCross13Root) = nativeHeatCross13Hn := by
  decide +kernel

theorem nativeHeatCross13_hn_bound : nativeHeatHnReal nativeHeatParametersData (13/2 : ℚ) ≤ (nativeHeatCross13Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((13/2 : ℚ)-1)/((13/2 : ℚ)*19)) = (220/247 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross13_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross13Root)
  rw [nativeHeatCross13_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross13_powers : 0 ≤ nativeHeatCross13U ∧ 0 ≤ nativeHeatCross13V ∧ ((13-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross13U^2 ∧ 2*(nativeHeatB*nativeHeatCross13Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross13V^2 ∧ 2*nativeHeatCross13U*nativeHeatCross13V = nativeHeatParametersData.cross.getD 13 0 := by
  decide +kernel

theorem nativeHeatCross13_bound : nativeHeatCrossReal nativeHeatParametersData 13 ≤ ((nativeHeatParametersData.cross.getD 13 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross13_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 13 nativeHeatCross13Hn nativeHeatCross13U nativeHeatCross13V nativeHeatCross13_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
