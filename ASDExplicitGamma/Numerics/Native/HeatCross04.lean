module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 4, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross04Hn : ℚ := (4421710838017846986939655451059836436120695935074501932310696495568203676881930925186403108174987539/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross04Root : ℚ := (3152300211447044902127153664713409320613818026766933391069009415103437031084095330262725849/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross04U : ℚ := (131995946316786868886408043096012221227160894208991055331184802579784561569029114241819/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross04V : ℚ := (71364713434085655146936054951833539759870855280346035314697633737312635561367746870194417/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross04_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^10*500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^19 ≤ 3152300211447044902127153664713409320613818026766933391069009415103437031084095330262725849^19*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^10 := by
  decide +kernel

theorem nativeHeatCross04_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross04_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((10/19 : ℚ) : ℝ) ≤ (nativeHeatCross04Root : ℝ) := by
  rw [nativeHeatCross04_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 3152300211447044902127153664713409320613818026766933391069009415103437031084095330262725849 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 10 19 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross04_integer
  simpa only [nativeHeatCross04Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross04_hn_round : nativeUp (nativeQstar*nativeHeatCross04Root) = nativeHeatCross04Hn := by
  decide +kernel

theorem nativeHeatCross04_hn_bound : nativeHeatHnReal nativeHeatParametersData (4/2 : ℚ) ≤ (nativeHeatCross04Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((4/2 : ℚ)-1)/((4/2 : ℚ)*19)) = (10/19 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross04_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross04Root)
  rw [nativeHeatCross04_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross04_powers : 0 ≤ nativeHeatCross04U ∧ 0 ≤ nativeHeatCross04V ∧ ((4-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross04U^2 ∧ 2*(nativeHeatB*nativeHeatCross04Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross04V^2 ∧ 2*nativeHeatCross04U*nativeHeatCross04V = nativeHeatParametersData.cross.getD 4 0 := by
  decide +kernel

theorem nativeHeatCross04_bound : nativeHeatCrossReal nativeHeatParametersData 4 ≤ ((nativeHeatParametersData.cross.getD 4 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross04_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 4 nativeHeatCross04Hn nativeHeatCross04U nativeHeatCross04V nativeHeatCross04_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
