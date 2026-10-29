module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 20, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross20Hn : ℚ := (602790519397746035127506167590697913215566242018418723026517281874216661173529514358679068240294931/312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross20Root : ℚ := (13751612451311502585125943874188316192526680911516309797208732046267268299084514711759715497/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross20U : ℚ := (664365027212417855850782195375646343413657053076123294755425108696777522969540936695041/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross20V : ℚ := (596220005564548509381473300284783709983698614702996868647941924465784333794103936577595823/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross20_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^18*500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^19 ≤ 13751612451311502585125943874188316192526680911516309797208732046267268299084514711759715497^19*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^18 := by
  decide +kernel

theorem nativeHeatCross20_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross20_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((18/19 : ℚ) : ℝ) ≤ (nativeHeatCross20Root : ℝ) := by
  rw [nativeHeatCross20_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 13751612451311502585125943874188316192526680911516309797208732046267268299084514711759715497 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 18 19 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross20_integer
  simpa only [nativeHeatCross20Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross20_hn_round : nativeUp (nativeQstar*nativeHeatCross20Root) = nativeHeatCross20Hn := by
  decide +kernel

theorem nativeHeatCross20_hn_bound : nativeHeatHnReal nativeHeatParametersData (20/2 : ℚ) ≤ (nativeHeatCross20Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((20/2 : ℚ)-1)/((20/2 : ℚ)*19)) = (18/19 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross20_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross20Root)
  rw [nativeHeatCross20_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross20_powers : 0 ≤ nativeHeatCross20U ∧ 0 ≤ nativeHeatCross20V ∧ ((20-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross20U^2 ∧ 2*(nativeHeatB*nativeHeatCross20Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross20V^2 ∧ 2*nativeHeatCross20U*nativeHeatCross20V = nativeHeatParametersData.cross.getD 20 0 := by
  decide +kernel

theorem nativeHeatCross20_bound : nativeHeatCrossReal nativeHeatParametersData 20 ≤ ((nativeHeatParametersData.cross.getD 20 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross20_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 20 nativeHeatCross20Hn nativeHeatCross20U nativeHeatCross20V nativeHeatCross20_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
