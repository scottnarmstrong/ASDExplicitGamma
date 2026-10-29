module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 15, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross15Hn : ℚ := (17061055158199657461398253288427704993935588507268673258152848757005003705220818349077141189541389523/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross15Root : ℚ := (1216306758919846902495847980639472985306448681600907194159068682151379257607736654723848819/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross15U : ℚ := (285143833773353252978490224989830003182138378888791872146299761265053738477895063860449/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross15V : ℚ := (2242907087844046978614199867660028868048069562051330847683242150973596347754586632225197081/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross15_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^52*50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^57 ≤ 1216306758919846902495847980639472985306448681600907194159068682151379257607736654723848819^57*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^52 := by
  decide +kernel

theorem nativeHeatCross15_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross15_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((52/57 : ℚ) : ℝ) ≤ (nativeHeatCross15Root : ℝ) := by
  rw [nativeHeatCross15_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 1216306758919846902495847980639472985306448681600907194159068682151379257607736654723848819 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 52 57 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross15_integer
  simpa only [nativeHeatCross15Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross15_hn_round : nativeUp (nativeQstar*nativeHeatCross15Root) = nativeHeatCross15Hn := by
  decide +kernel

theorem nativeHeatCross15_hn_bound : nativeHeatHnReal nativeHeatParametersData (15/2 : ℚ) ≤ (nativeHeatCross15Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((15/2 : ℚ)-1)/((15/2 : ℚ)*19)) = (52/57 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross15_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross15Root)
  rw [nativeHeatCross15_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross15_powers : 0 ≤ nativeHeatCross15U ∧ 0 ≤ nativeHeatCross15V ∧ ((15-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross15U^2 ∧ 2*(nativeHeatB*nativeHeatCross15Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross15V^2 ∧ 2*nativeHeatCross15U*nativeHeatCross15V = nativeHeatParametersData.cross.getD 15 0 := by
  decide +kernel

theorem nativeHeatCross15_bound : nativeHeatCrossReal nativeHeatParametersData 15 ≤ ((nativeHeatParametersData.cross.getD 15 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross15_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 15 nativeHeatCross15Hn nativeHeatCross15U nativeHeatCross15V nativeHeatCross15_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
