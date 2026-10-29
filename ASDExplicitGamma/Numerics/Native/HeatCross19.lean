module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 19, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross19Hn : ℚ := (472975834462734534241159145888074129066710526251454712955648790971767500531897830251708625598813751/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross19Root : ℚ := (26975293095458681068220396945479972507779523824409789153282684293464032480321677018421494953/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross19U : ℚ := (646645433183856903887374816739688193218871456505234601361078983992104471176089181001549/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross19V : ℚ := (1180939953512881060377545296689867092297048271768481900949814716163867484699262010944580321/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross19_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^340*1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^361 ≤ 26975293095458681068220396945479972507779523824409789153282684293464032480321677018421494953^361*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^340 := by
  decide +kernel

theorem nativeHeatCross19_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross19_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((340/361 : ℚ) : ℝ) ≤ (nativeHeatCross19Root : ℝ) := by
  rw [nativeHeatCross19_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 26975293095458681068220396945479972507779523824409789153282684293464032480321677018421494953 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 340 361 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross19_integer
  simpa only [nativeHeatCross19Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross19_hn_round : nativeUp (nativeQstar*nativeHeatCross19Root) = nativeHeatCross19Hn := by
  decide +kernel

theorem nativeHeatCross19_hn_bound : nativeHeatHnReal nativeHeatParametersData (19/2 : ℚ) ≤ (nativeHeatCross19Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((19/2 : ℚ)-1)/((19/2 : ℚ)*19)) = (340/361 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross19_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross19Root)
  rw [nativeHeatCross19_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross19_powers : 0 ≤ nativeHeatCross19U ∧ 0 ≤ nativeHeatCross19V ∧ ((19-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross19U^2 ∧ 2*(nativeHeatB*nativeHeatCross19Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross19V^2 ∧ 2*nativeHeatCross19U*nativeHeatCross19V = nativeHeatParametersData.cross.getD 19 0 := by
  decide +kernel

theorem nativeHeatCross19_bound : nativeHeatCrossReal nativeHeatParametersData 19 ≤ ((nativeHeatParametersData.cross.getD 19 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross19_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 19 nativeHeatCross19Hn nativeHeatCross19U nativeHeatCross19V nativeHeatCross19_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
