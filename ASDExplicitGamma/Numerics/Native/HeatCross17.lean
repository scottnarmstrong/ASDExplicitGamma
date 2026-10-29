module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 17, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross17Hn : ℚ := (18075619191870043416176745799046380660780756722012889078603228690097025367293949680213958291310704333/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross17Root : ℚ := (1610795580260935472564120537914225710303674594196441820668883758726970417176964486113699957/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross17U : ℚ := (152415790275872580399329370522786160646242950769699740893156531016613321140070111263527/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross17V : ℚ := (288579146407931522766523534746050542835594163996551763744957120043965936662987951162153137/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross17_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^300*62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000^323 ≤ 1610795580260935472564120537914225710303674594196441820668883758726970417176964486113699957^323*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^300 := by
  decide +kernel

theorem nativeHeatCross17_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross17_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((300/323 : ℚ) : ℝ) ≤ (nativeHeatCross17Root : ℝ) := by
  rw [nativeHeatCross17_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 1610795580260935472564120537914225710303674594196441820668883758726970417176964486113699957 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 300 323 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross17_integer
  simpa only [nativeHeatCross17Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross17_hn_round : nativeUp (nativeQstar*nativeHeatCross17Root) = nativeHeatCross17Hn := by
  decide +kernel

theorem nativeHeatCross17_hn_bound : nativeHeatHnReal nativeHeatParametersData (17/2 : ℚ) ≤ (nativeHeatCross17Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((17/2 : ℚ)-1)/((17/2 : ℚ)*19)) = (300/323 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross17_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross17Root)
  rw [nativeHeatCross17_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross17_powers : 0 ≤ nativeHeatCross17U ∧ 0 ≤ nativeHeatCross17V ∧ ((17-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross17U^2 ∧ 2*(nativeHeatB*nativeHeatCross17Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross17V^2 ∧ 2*nativeHeatCross17U*nativeHeatCross17V = nativeHeatParametersData.cross.getD 17 0 := by
  decide +kernel

theorem nativeHeatCross17_bound : nativeHeatCrossReal nativeHeatParametersData 17 ≤ ((nativeHeatParametersData.cross.getD 17 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross17_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 17 nativeHeatCross17Hn nativeHeatCross17U nativeHeatCross17V nativeHeatCross17_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
