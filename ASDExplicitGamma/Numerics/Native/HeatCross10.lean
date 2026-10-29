module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 10, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross10Hn : ℚ := (13347037422268040934819691883851032246202736759903340552987410298705507459585215578980772470447359143/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross10Root : ℚ := (4757645901068005036175806768009900423856219750217801689303287379658761148676397437206268661/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross10U : ℚ := (457247370827617741197988111568358481938728852309099222679469593049839963420210333790581/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross10V : ℚ := (1983813214801415896166675031149301368176868197412477144806698190957042014941662128202069261/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross10_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^16*250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^19 ≤ 4757645901068005036175806768009900423856219750217801689303287379658761148676397437206268661^19*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^16 := by
  decide +kernel

theorem nativeHeatCross10_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross10_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((16/19 : ℚ) : ℝ) ≤ (nativeHeatCross10Root : ℝ) := by
  rw [nativeHeatCross10_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 4757645901068005036175806768009900423856219750217801689303287379658761148676397437206268661 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 16 19 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross10_integer
  simpa only [nativeHeatCross10Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross10_hn_round : nativeUp (nativeQstar*nativeHeatCross10Root) = nativeHeatCross10Hn := by
  decide +kernel

theorem nativeHeatCross10_hn_bound : nativeHeatHnReal nativeHeatParametersData (10/2 : ℚ) ≤ (nativeHeatCross10Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((10/2 : ℚ)-1)/((10/2 : ℚ)*19)) = (16/19 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross10_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross10Root)
  rw [nativeHeatCross10_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross10_powers : 0 ≤ nativeHeatCross10U ∧ 0 ≤ nativeHeatCross10V ∧ ((10-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross10U^2 ∧ 2*(nativeHeatB*nativeHeatCross10Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross10V^2 ∧ 2*nativeHeatCross10U*nativeHeatCross10V = nativeHeatParametersData.cross.getD 10 0 := by
  decide +kernel

theorem nativeHeatCross10_bound : nativeHeatCrossReal nativeHeatParametersData 10 ≤ ((nativeHeatParametersData.cross.getD 10 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross10_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 10 nativeHeatCross10Hn nativeHeatCross10U nativeHeatCross10V nativeHeatCross10_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
