module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 18, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross18Hn : ℚ := (18515959549717093555069003529235268373753503369876948516351885349825676690418143141079512643904250667/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross18Root : ℚ := (13200289512799330396672531983101568818495913363074136741990458142807995186163889148521063851/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross18U : ℚ := (628426402319411758850999825632384853703276821425639450449418316277237364172781831060489/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross18V : ℚ := (2336584285248009467280128599316504271639536058436563091576727715245481930136030919797150911/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross18_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^160*500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^171 ≤ 13200289512799330396672531983101568818495913363074136741990458142807995186163889148521063851^171*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^160 := by
  decide +kernel

theorem nativeHeatCross18_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross18_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((160/171 : ℚ) : ℝ) ≤ (nativeHeatCross18Root : ℝ) := by
  rw [nativeHeatCross18_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 13200289512799330396672531983101568818495913363074136741990458142807995186163889148521063851 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 160 171 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross18_integer
  simpa only [nativeHeatCross18Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross18_hn_round : nativeUp (nativeQstar*nativeHeatCross18Root) = nativeHeatCross18Hn := by
  decide +kernel

theorem nativeHeatCross18_hn_bound : nativeHeatHnReal nativeHeatParametersData (18/2 : ℚ) ≤ (nativeHeatCross18Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((18/2 : ℚ)-1)/((18/2 : ℚ)*19)) = (160/171 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross18_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross18Root)
  rw [nativeHeatCross18_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross18_powers : 0 ≤ nativeHeatCross18U ∧ 0 ≤ nativeHeatCross18V ∧ ((18-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross18U^2 ∧ 2*(nativeHeatB*nativeHeatCross18Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross18V^2 ∧ 2*nativeHeatCross18U*nativeHeatCross18V = nativeHeatParametersData.cross.getD 18 0 := by
  decide +kernel

theorem nativeHeatCross18_bound : nativeHeatCrossReal nativeHeatParametersData 18 ≤ ((nativeHeatParametersData.cross.getD 18 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross18_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 18 nativeHeatCross18Hn nativeHeatCross18U nativeHeatCross18V nativeHeatCross18_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
