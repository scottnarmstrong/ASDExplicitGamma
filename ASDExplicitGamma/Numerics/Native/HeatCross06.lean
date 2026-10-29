module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 6, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross06Hn : ℚ := (8168510287373986256130754832979262384934390910366434370083883642867272010588626286995064808936126743/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross06Root : ℚ := (2911723272890379746108750314065026903932192264368102030016300286411404749662815356373627563/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross06U : ℚ := (340812067901202514313240918873841828294561554581851200163221649963499607626551577414177/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross06V : ℚ := (155195730693238202806968022154794790784495436065402538645753180724251910638517495310720177/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross06_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^40*250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^57 ≤ 2911723272890379746108750314065026903932192264368102030016300286411404749662815356373627563^57*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^40 := by
  decide +kernel

theorem nativeHeatCross06_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross06_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((40/57 : ℚ) : ℝ) ≤ (nativeHeatCross06Root : ℝ) := by
  rw [nativeHeatCross06_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 2911723272890379746108750314065026903932192264368102030016300286411404749662815356373627563 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 40 57 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross06_integer
  simpa only [nativeHeatCross06Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross06_hn_round : nativeUp (nativeQstar*nativeHeatCross06Root) = nativeHeatCross06Hn := by
  decide +kernel

theorem nativeHeatCross06_hn_bound : nativeHeatHnReal nativeHeatParametersData (6/2 : ℚ) ≤ (nativeHeatCross06Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((6/2 : ℚ)-1)/((6/2 : ℚ)*19)) = (40/57 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross06_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross06Root)
  rw [nativeHeatCross06_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross06_powers : 0 ≤ nativeHeatCross06U ∧ 0 ≤ nativeHeatCross06V ∧ ((6-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross06U^2 ∧ 2*(nativeHeatB*nativeHeatCross06Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross06V^2 ∧ 2*nativeHeatCross06U*nativeHeatCross06V = nativeHeatParametersData.cross.getD 6 0 := by
  decide +kernel

theorem nativeHeatCross06_bound : nativeHeatCrossReal nativeHeatParametersData 6 ≤ ((nativeHeatParametersData.cross.getD 6 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross06_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 6 nativeHeatCross06Hn nativeHeatCross06U nativeHeatCross06V nativeHeatCross06_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
