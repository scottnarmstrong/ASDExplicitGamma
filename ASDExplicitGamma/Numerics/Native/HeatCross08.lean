module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 8, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross08Hn : ℚ := (11102457553262097421850396685075519374950142917212634653161886962358866706215002854402049381200317673/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross08Root : ℚ := (3957549529450786965045338207459851137063045919986451991985410781252712781792059907523903523/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross08U : ℚ := (16130171077973422286246704792801465786985271654213992869186614596561919361257635285843/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross08V : ℚ := (361866096988504501013061451628827347454141726501512524627748323845718685393330296287709887/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross08_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^15*250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^19 ≤ 3957549529450786965045338207459851137063045919986451991985410781252712781792059907523903523^19*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^15 := by
  decide +kernel

theorem nativeHeatCross08_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross08_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((15/19 : ℚ) : ℝ) ≤ (nativeHeatCross08Root : ℝ) := by
  rw [nativeHeatCross08_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 3957549529450786965045338207459851137063045919986451991985410781252712781792059907523903523 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 15 19 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross08_integer
  simpa only [nativeHeatCross08Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross08_hn_round : nativeUp (nativeQstar*nativeHeatCross08Root) = nativeHeatCross08Hn := by
  decide +kernel

theorem nativeHeatCross08_hn_bound : nativeHeatHnReal nativeHeatParametersData (8/2 : ℚ) ≤ (nativeHeatCross08Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((8/2 : ℚ)-1)/((8/2 : ℚ)*19)) = (15/19 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross08_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross08Root)
  rw [nativeHeatCross08_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross08_powers : 0 ≤ nativeHeatCross08U ∧ 0 ≤ nativeHeatCross08V ∧ ((8-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross08U^2 ∧ 2*(nativeHeatB*nativeHeatCross08Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross08V^2 ∧ 2*nativeHeatCross08U*nativeHeatCross08V = nativeHeatParametersData.cross.getD 8 0 := by
  decide +kernel

theorem nativeHeatCross08_bound : nativeHeatCrossReal nativeHeatParametersData 8 ≤ ((nativeHeatParametersData.cross.getD 8 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross08_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 8 nativeHeatCross08Hn nativeHeatCross08U nativeHeatCross08V nativeHeatCross08_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
