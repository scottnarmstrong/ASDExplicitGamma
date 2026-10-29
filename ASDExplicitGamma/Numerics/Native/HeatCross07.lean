module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 7, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross07Hn : ℚ := (4867105141399399138596110273106771884930426215968447409456233685544513452906061719433765599978101567/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross07Root : ℚ := (13879312445719363708841115976733963520614352065044526085398672713688832351014182232400452131/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross07U : ℚ := (18667045745947097227536077386876172778280349646827237680480815174904438176019776151043/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross07V : ℚ := (1694176688909531886801389306160538705430715901145924725044123356293393358305783223179971967/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross07_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^100*1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^133 ≤ 13879312445719363708841115976733963520614352065044526085398672713688832351014182232400452131^133*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^100 := by
  decide +kernel

theorem nativeHeatCross07_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross07_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((100/133 : ℚ) : ℝ) ≤ (nativeHeatCross07Root : ℝ) := by
  rw [nativeHeatCross07_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 13879312445719363708841115976733963520614352065044526085398672713688832351014182232400452131 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 100 133 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross07_integer
  simpa only [nativeHeatCross07Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross07_hn_round : nativeUp (nativeQstar*nativeHeatCross07Root) = nativeHeatCross07Hn := by
  decide +kernel

theorem nativeHeatCross07_hn_bound : nativeHeatHnReal nativeHeatParametersData (7/2 : ℚ) ≤ (nativeHeatCross07Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((7/2 : ℚ)-1)/((7/2 : ℚ)*19)) = (100/133 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross07_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross07Root)
  rw [nativeHeatCross07_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross07_powers : 0 ≤ nativeHeatCross07U ∧ 0 ≤ nativeHeatCross07V ∧ ((7-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross07U^2 ∧ 2*(nativeHeatB*nativeHeatCross07Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross07V^2 ∧ 2*nativeHeatCross07U*nativeHeatCross07V = nativeHeatParametersData.cross.getD 7 0 := by
  decide +kernel

theorem nativeHeatCross07_bound : nativeHeatCrossReal nativeHeatParametersData 7 ≤ ((nativeHeatParametersData.cross.getD 7 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross07_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 7 nativeHeatCross07Hn nativeHeatCross07U nativeHeatCross07V nativeHeatCross07_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
