module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 16, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross16Hn : ℚ := (17592741165642130286015613556243610925383490595100437578846390123946999216941148635457625185408175989/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross16Root : ℚ := (25084228131592253865837895376651278067454152737324291909578485854151116320019948769000152429/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross16U : ℚ := (590303817437496857975806340463709741020106950966558577440569084912891798801551445438087/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross16V : ℚ := (2277587635264811937433032534248058464344284137455607868185562459183548121788891056039694047/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross16_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^35*1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^38 ≤ 25084228131592253865837895376651278067454152737324291909578485854151116320019948769000152429^38*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^35 := by
  decide +kernel

theorem nativeHeatCross16_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross16_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((35/38 : ℚ) : ℝ) ≤ (nativeHeatCross16Root : ℝ) := by
  rw [nativeHeatCross16_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 25084228131592253865837895376651278067454152737324291909578485854151116320019948769000152429 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 35 38 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross16_integer
  simpa only [nativeHeatCross16Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross16_hn_round : nativeUp (nativeQstar*nativeHeatCross16Root) = nativeHeatCross16Hn := by
  decide +kernel

theorem nativeHeatCross16_hn_bound : nativeHeatHnReal nativeHeatParametersData (16/2 : ℚ) ≤ (nativeHeatCross16Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((16/2 : ℚ)-1)/((16/2 : ℚ)*19)) = (35/38 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross16_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross16Root)
  rw [nativeHeatCross16_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross16_powers : 0 ≤ nativeHeatCross16U ∧ 0 ≤ nativeHeatCross16V ∧ ((16-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross16U^2 ∧ 2*(nativeHeatB*nativeHeatCross16Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross16V^2 ∧ 2*nativeHeatCross16U*nativeHeatCross16V = nativeHeatParametersData.cross.getD 16 0 := by
  decide +kernel

theorem nativeHeatCross16_bound : nativeHeatCrossReal nativeHeatParametersData 16 ≤ ((nativeHeatParametersData.cross.getD 16 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross16_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 16 nativeHeatCross16Hn nativeHeatCross16U nativeHeatCross16V nativeHeatCross16_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
