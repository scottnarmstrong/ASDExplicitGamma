module

public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Inverse.WeightedLocalizationLayerProfile

/-! The exact deterministic Li profile and the selected-height clock factor. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Algsuperdiff.Section3
noncomputable section

/-- The actual Li layer series is summable throughout the source gamma range. -/
theorem root_layer_sum_summable (γ : ℝ) (hg : γ ≤ gammaZero) :
    Summable (fun k : ℕ => bankLayerWeight k*(3:ℝ)^(2*γ*(localizationProfileDepth (k+1):ℝ))) := by
  let z := (3:ℝ)^(2*γ)
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hsmall : z^4 < 27 := by
    calc
      z^4=(3:ℝ)^((2*γ)*(4:ℕ)) := (Real.rpow_mul_natCast (by norm_num) _ _).symm
      _ < (3:ℝ)^(3:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        (by change γ ≤ 17/50000 at hg; norm_num; linarith only [hg])
      _ = 27 := by norm_num
  have hh := (localization_layer_profile_hasSum z hz hsmall).summable
  have he (k : ℕ) : z^localizationProfileDepth (k+1)=
      (3:ℝ)^(2*γ*(localizationProfileDepth (k+1):ℝ)) := (Real.rpow_mul_natCast (by norm_num) _ _).symm
  simpa only [he] using hh

/-- The exact source x_kh clock factors as the selected-height clock times
the original retained layer profile. -/
theorem root_layer_clock_factor (γ : ℝ) (r : RootRow) (H : ℕ) (hH : rootH0 r ≤ H) (k : ℕ) :
    (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℝ))=
      (3:ℝ)^(2*γ*((H:ℝ)-38))*(3:ℝ)^(2*γ*(localizationProfileDepth (k+1):ℝ)) := by
  have hH0 : 38 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hi : (localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℤ)=
      (H:ℤ)-38+(localizationProfileDepth (k+1):ℤ) := by
    unfold localizationResetAbscissa
    omega
  have hr : (localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℝ)=
      (H:ℝ)-38+(localizationProfileDepth (k+1):ℝ) := by exact_mod_cast hi
  rw [hr,← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  congr 1
  ring

/-- The actual weighted deterministic layer baseline has exactly the Li
profile factor, before any positive random error is added. -/
theorem root_clocked_layer_weights_hasSum (γ : ℝ) (hg : γ ≤ gammaZero)
    (r : RootRow) (H : ℕ) (hH : rootH0 r ≤ H) :
    HasSum (fun k : ℕ => (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38)
      (H-rootH0 r) k:ℝ))*bankLayerWeight k)
      ((3:ℝ)^(2*γ*((H:ℝ)-38))*rootLayerSum (2*γ)) := by
  have hh := (root_layer_sum_summable γ hg).hasSum.mul_left ((3:ℝ)^(2*γ*((H:ℝ)-38)))
  convert hh using 1
  · funext k
    rw [root_layer_clock_factor γ r H hH k]
    ring
  · rfl

end
end ASDExplicitGamma.Inverse
