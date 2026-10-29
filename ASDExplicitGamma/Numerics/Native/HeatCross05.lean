module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 5, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross05Hn : ℚ := (798788611539683404442546506429265695064967437854751167524884577046458781970900000232652697401769249/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross05Root : ℚ := (4555741614595146214265338848088439968266346552168965152581765749616035269961548891984927899/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross05U : ℚ := (152415790275872580399329370522786160646242950769699740893156531016613321140070111263527/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross05V : ℚ := (1372679872022478579445179413439580812582637627850816081691707209619927097235180985465002697/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross05_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^12*500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^19 ≤ 4555741614595146214265338848088439968266346552168965152581765749616035269961548891984927899^19*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^12 := by
  decide +kernel

theorem nativeHeatCross05_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross05_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((12/19 : ℚ) : ℝ) ≤ (nativeHeatCross05Root : ℝ) := by
  rw [nativeHeatCross05_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 4555741614595146214265338848088439968266346552168965152581765749616035269961548891984927899 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 12 19 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross05_integer
  simpa only [nativeHeatCross05Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross05_hn_round : nativeUp (nativeQstar*nativeHeatCross05Root) = nativeHeatCross05Hn := by
  decide +kernel

theorem nativeHeatCross05_hn_bound : nativeHeatHnReal nativeHeatParametersData (5/2 : ℚ) ≤ (nativeHeatCross05Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((5/2 : ℚ)-1)/((5/2 : ℚ)*19)) = (12/19 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross05_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross05Root)
  rw [nativeHeatCross05_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross05_powers : 0 ≤ nativeHeatCross05U ∧ 0 ≤ nativeHeatCross05V ∧ ((5-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross05U^2 ∧ 2*(nativeHeatB*nativeHeatCross05Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross05V^2 ∧ 2*nativeHeatCross05U*nativeHeatCross05V = nativeHeatParametersData.cross.getD 5 0 := by
  decide +kernel

theorem nativeHeatCross05_bound : nativeHeatCrossReal nativeHeatParametersData 5 ≤ ((nativeHeatParametersData.cross.getD 5 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross05_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 5 nativeHeatCross05Hn nativeHeatCross05U nativeHeatCross05V nativeHeatCross05_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
