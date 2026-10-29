module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 12, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross12Hn : ℚ := (15090213439838086645991534548480752715121834953031712605515888470472755805065433248011994132952760207/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross12Root : ℚ := (172128426339183027216252335640277281089542747116659611756827904003140359803394045713929221/8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross12U : ℚ := (101101197694113697580092447391272265932848301953645895353107213720971944600184235534487/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross12V : ℚ := (2109385863334819204228886365762123007534234369544075955448790374386416066013170334095071883/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross12_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^50*8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^57 ≤ 172128426339183027216252335640277281089542747116659611756827904003140359803394045713929221^57*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^50 := by
  decide +kernel

theorem nativeHeatCross12_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross12_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((50/57 : ℚ) : ℝ) ≤ (nativeHeatCross12Root : ℝ) := by
  rw [nativeHeatCross12_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 172128426339183027216252335640277281089542747116659611756827904003140359803394045713929221 8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 50 57 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross12_integer
  simpa only [nativeHeatCross12Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross12_hn_round : nativeUp (nativeQstar*nativeHeatCross12Root) = nativeHeatCross12Hn := by
  decide +kernel

theorem nativeHeatCross12_hn_bound : nativeHeatHnReal nativeHeatParametersData (12/2 : ℚ) ≤ (nativeHeatCross12Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((12/2 : ℚ)-1)/((12/2 : ℚ)*19)) = (50/57 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross12_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross12Root)
  rw [nativeHeatCross12_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross12_powers : 0 ≤ nativeHeatCross12U ∧ 0 ≤ nativeHeatCross12V ∧ ((12-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross12U^2 ∧ 2*(nativeHeatB*nativeHeatCross12Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross12V^2 ∧ 2*nativeHeatCross12U*nativeHeatCross12V = nativeHeatParametersData.cross.getD 12 0 := by
  decide +kernel

theorem nativeHeatCross12_bound : nativeHeatCrossReal nativeHeatParametersData 12 ≤ ((nativeHeatParametersData.cross.getD 12 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross12_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 12 nativeHeatCross12Hn nativeHeatCross12U nativeHeatCross12V nativeHeatCross12_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
