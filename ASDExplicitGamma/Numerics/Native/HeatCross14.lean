module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 14, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross14Hn : ℚ := (16473061292501702940477474124522519421119395316131486893951335407913850596201542263913500006520648111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross14Root : ℚ := (23487756887698885806317489986793538696629697456286027743419977106459373821809254391673966563/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross14U : ℚ := (274771473515012139393325809135078185204335968133306371948670405138482468243637436763041/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross14V : ℚ := (2203918330318917492888204775155732482713163272729216978677843476686519534484527605381185081/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross14_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^120*1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^133 ≤ 23487756887698885806317489986793538696629697456286027743419977106459373821809254391673966563^133*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^120 := by
  decide +kernel

theorem nativeHeatCross14_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross14_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((120/133 : ℚ) : ℝ) ≤ (nativeHeatCross14Root : ℝ) := by
  rw [nativeHeatCross14_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 23487756887698885806317489986793538696629697456286027743419977106459373821809254391673966563 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 120 133 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross14_integer
  simpa only [nativeHeatCross14Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross14_hn_round : nativeUp (nativeQstar*nativeHeatCross14Root) = nativeHeatCross14Hn := by
  decide +kernel

theorem nativeHeatCross14_hn_bound : nativeHeatHnReal nativeHeatParametersData (14/2 : ℚ) ≤ (nativeHeatCross14Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((14/2 : ℚ)-1)/((14/2 : ℚ)*19)) = (120/133 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross14_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross14Root)
  rw [nativeHeatCross14_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross14_powers : 0 ≤ nativeHeatCross14U ∧ 0 ≤ nativeHeatCross14V ∧ ((14-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross14U^2 ∧ 2*(nativeHeatB*nativeHeatCross14Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross14V^2 ∧ 2*nativeHeatCross14U*nativeHeatCross14V = nativeHeatParametersData.cross.getD 14 0 := by
  decide +kernel

theorem nativeHeatCross14_bound : nativeHeatCrossReal nativeHeatParametersData 14 ≤ ((nativeHeatParametersData.cross.getD 14 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross14_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 14 nativeHeatCross14Hn nativeHeatCross14U nativeHeatCross14V nativeHeatCross14_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
