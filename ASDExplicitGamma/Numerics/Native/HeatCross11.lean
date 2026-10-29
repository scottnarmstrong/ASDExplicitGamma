module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 11, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross11Hn : ℚ := (14271293410798317230178008639365488067912879127603652915764094119798411845128862633323046519087656697/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross11Root : ℚ := (4069682788813860026569385095915321525937184475059477654828840074331056744424517717148515063/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross11U : ℚ := (481981048646300766956088026891132225837456963774610094018824089741288589946538366307613/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross11V : ℚ := (1025675570734212212298941848056285510482337842580587940301944541193550107076116081183770819/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross11_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^180*200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^209 ≤ 4069682788813860026569385095915321525937184475059477654828840074331056744424517717148515063^209*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^180 := by
  decide +kernel

theorem nativeHeatCross11_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross11_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((180/209 : ℚ) : ℝ) ≤ (nativeHeatCross11Root : ℝ) := by
  rw [nativeHeatCross11_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 4069682788813860026569385095915321525937184475059477654828840074331056744424517717148515063 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 180 209 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross11_integer
  simpa only [nativeHeatCross11Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross11_hn_round : nativeUp (nativeQstar*nativeHeatCross11Root) = nativeHeatCross11Hn := by
  decide +kernel

theorem nativeHeatCross11_hn_bound : nativeHeatHnReal nativeHeatParametersData (11/2 : ℚ) ≤ (nativeHeatCross11Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((11/2 : ℚ)-1)/((11/2 : ℚ)*19)) = (180/209 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross11_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross11Root)
  rw [nativeHeatCross11_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross11_powers : 0 ≤ nativeHeatCross11U ∧ 0 ≤ nativeHeatCross11V ∧ ((11-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross11U^2 ∧ 2*(nativeHeatB*nativeHeatCross11Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross11V^2 ∧ 2*nativeHeatCross11U*nativeHeatCross11V = nativeHeatParametersData.cross.getD 11 0 := by
  decide +kernel

theorem nativeHeatCross11_bound : nativeHeatCrossReal nativeHeatParametersData 11 ≤ ((nativeHeatParametersData.cross.getD 11 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross11_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 11 nativeHeatCross11Hn nativeHeatCross11U nativeHeatCross11V nativeHeatCross11_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
