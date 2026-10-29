module
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.RationalPowers
/-! Literal source cross coefficient 9, certified by integer root powers. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHeatCross09Hn : ℚ := (12298284679680523684010528372447604359910324585515529980569872754657148744348508606528716524376096529/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross09Root : ℚ := (17535242269967899729389148864668651963672841234643706135561792252361232126536733052978870441/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross09U : ℚ := (431096955455904602591583211159792128812580971003489734240719322661402980784059454001033/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def nativeHeatCross09V : ℚ := (1904279143075937149602042440257534552547254787034077749107318868514597146487984918092643639/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem nativeHeatCross09_integer : 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043^140*1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000^171 ≤ 17535242269967899729389148864668651963672841234643706135561792252361232126536733052978870441^171*175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000^140 := by
  decide +kernel

theorem nativeHeatCross09_ratio : (nativeHeatParametersData.hp/nativeQstar : ℚ) = (5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043/175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem nativeHeatCross09_root_real : ((nativeHeatParametersData.hp/nativeQstar : ℚ) : ℝ)^((140/171 : ℚ) : ℝ) ≤ (nativeHeatCross09Root : ℝ) := by
  rw [nativeHeatCross09_ratio]
  have h := native_real_rpow_le_of_cross 5797251703305062067612310104641034640716549911803140057258516659053710734403001891843035267592939043 175336680416777570755058577012800000000000000000000000000000000000000000000000000000000000000000000 17535242269967899729389148864668651963672841234643706135561792252361232126536733052978870441 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 140 171 (by decide +kernel) (by decide +kernel) (by decide) nativeHeatCross09_integer
  simpa only [nativeHeatCross09Root, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Nat.cast_zero, Nat.cast_one] using h

theorem nativeHeatCross09_hn_round : nativeUp (nativeQstar*nativeHeatCross09Root) = nativeHeatCross09Hn := by
  decide +kernel

theorem nativeHeatCross09_hn_bound : nativeHeatHnReal nativeHeatParametersData (9/2 : ℚ) ≤ (nativeHeatCross09Hn : ℝ) := by
  unfold nativeHeatHnReal
  have he : (20*((9/2 : ℚ)-1)/((9/2 : ℚ)*19)) = (140/171 : ℚ) := by decide +kernel
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left nativeHeatCross09_root_real (show (0 : ℝ) ≤ nativeQstar from by exact_mod_cast (show (0 : ℚ) ≤ nativeQstar by decide +kernel))
  have hround := nativeUp_ge (nativeQstar*nativeHeatCross09Root)
  rw [nativeHeatCross09_hn_round] at hround
  have hc := (Rat.cast_le (K := ℝ)).2 hround
  apply hmul.trans
  simpa only [Rat.cast_mul] using hc

theorem nativeHeatCross09_powers : 0 ≤ nativeHeatCross09U ∧ 0 ≤ nativeHeatCross09V ∧ ((9-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ nativeHeatCross09U^2 ∧ 2*(nativeHeatB*nativeHeatCross09Hn+nativeHeatEps*nativeHeatParametersData.hp) ≤ nativeHeatCross09V^2 ∧ 2*nativeHeatCross09U*nativeHeatCross09V = nativeHeatParametersData.cross.getD 9 0 := by
  decide +kernel

theorem nativeHeatCross09_bound : nativeHeatCrossReal nativeHeatParametersData 9 ≤ ((nativeHeatParametersData.cross.getD 9 0 : ℚ) : ℝ) := by
  have h := nativeHeatCross09_powers
  exact nativeHeatCross_real_bound nativeHeatParametersData 9 nativeHeatCross09Hn nativeHeatCross09U nativeHeatCross09V nativeHeatCross09_hn_bound h.1 h.2.1 h.2.2.1 h.2.2.2.1 (le_of_eq h.2.2.2.2)

end ASDExplicitGamma.Numerics.Native
