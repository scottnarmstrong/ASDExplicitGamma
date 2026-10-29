module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 3, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross03Hn : ℚ := (299190520168425931234505996824339904956417330272745611375660676870689598351676389977136405153599421/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross03Root : ℚ := (3412754472791958554908869357356857486647845979954038747953488745852392284424517302155185181/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross03U : ℚ := (215548477727952301295791605579896064406290485501744867120359661330701490392029727000517/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross03V : ℚ := (840092771237728228638287771911004509783643610416506986654564469587173210947646742741968867/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross03_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^20*1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^57 ≤ 3412754472791958554908869357356857486647845979954038747953488745852392284424517302155185181^57*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^20 := by
  decide +kernel

theorem nativeHeatCross03_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross03_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((20/57 : ℚ) : ℝ) ≤ (nativeHeatCross03Root : ℝ) := by
  rw [nativeHeatCross03_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 3412754472791958554908869357356857486647845979954038747953488745852392284424517302155185181 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 20 57 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross03_integer
  simpa only [nativeHeatCross03Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross03_hn_round : nativeUp (nativeQstar*nativeHeatCross03Root) = nativeHeatCross03Hn := by
  decide +kernel

theorem nativeHeatCross03_hn_bound : nativeHeatHnReal nativeHeatParametersData (3/2 : ℚ) ≤ (nativeHeatCross03Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((3/2 : ℚ)-1)/((3/2 : ℚ)*19)) = (20/57 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross03_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross03Root)
  rw [nativeHeatCross03_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross03_powers : 0 ≤ nativeHeatCross03U ∧ 0 ≤ nativeHeatCross03V ∧ ((3-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross03U^2 ∧ 2*(nativeHeatB*nativeHeatCross03Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross03V^2 ∧ 2*nativeHeatCross03U*nativeHeatCross03V = nativeHeatParametersData.cross.getD 3 0 := by
  decide +kernel

theorem nativeHeatCross03_bound : nativeHeatCrossReal nativeHeatParametersData 3 ≤ ((nativeHeatParametersData.cross.getD 3 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross03_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 3 nativeHeatCross03Hn nativeHeatCross03U nativeHeatCross03V nativeHeatCross03_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
