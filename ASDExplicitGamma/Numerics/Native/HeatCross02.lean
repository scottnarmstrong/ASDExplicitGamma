module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 2, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross02Hn : ℚ := (109585425260485981721911610633/1562500000000000000000000000000 : ℚ)
def nativeHeatCross02Root : ℚ := (1/1 : ℚ)
def nativeHeatCross02U : ℚ := (152415790275872580399329370522786160646242950769699740893156531016613321140070111263527/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross02V : ℚ := (454752112789037816835807420654109990221212083320036498237346219605192361247774131309593991/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross02_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^0*1^1 ≤ 1^1*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^0 := by
  decide +kernel

theorem nativeHeatCross02_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross02_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((0/1 : ℚ) : ℝ) ≤ (nativeHeatCross02Root : ℝ) := by
  rw [nativeHeatCross02_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 1 1 0 1 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross02_integer
  simpa only [nativeHeatCross02Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross02_hn_round : nativeUp (nativeQstar*nativeHeatCross02Root) = nativeHeatCross02Hn := by
  decide +kernel

theorem nativeHeatCross02_hn_bound : nativeHeatHnReal nativeHeatParametersData (2/2 : ℚ) ≤ (nativeHeatCross02Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((2/2 : ℚ)-1)/((2/2 : ℚ)*19)) = (0/1 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross02_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross02Root)
  rw [nativeHeatCross02_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross02_powers : 0 ≤ nativeHeatCross02U ∧ 0 ≤ nativeHeatCross02V ∧ ((2-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross02U^2 ∧ 2*(nativeHeatB*nativeHeatCross02Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross02V^2 ∧ 2*nativeHeatCross02U*nativeHeatCross02V = nativeHeatParametersData.cross.getD 2 0 := by
  decide +kernel

theorem nativeHeatCross02_bound : nativeHeatCrossReal nativeHeatParametersData 2 ≤ ((nativeHeatParametersData.cross.getD 2 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross02_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 2 nativeHeatCross02Hn nativeHeatCross02U nativeHeatCross02V nativeHeatCross02_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
