module

public import ASDExplicitGamma.Native.ParentRowMeanClockBridge

/-! The primitive physical source slope is bounded by the exact stored parent slope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3
noncomputable section

private theorem mean_slope_scalar (v a k f B : ℝ)
    (hv : 0≤v) (hk : 0≤k) (hf : 0≤f) (hB : 0≤B) :
    2*v*(3683/2500)+2*k*((3683/2500)*(f*B))+
      (232/125)*a^2*((3683/2500)^2*(f*B))≤
    a*a*(232/125)*(f*(176338357/78125000)*B+v*52*Real.sqrt 3*(49958012987/15625000000))+
      k*2*(f*(47879/31250)*B+v*52*Real.sqrt 3*(3683/2500)*(3683/2500))+
      v*2*(Real.sqrt 3*(3/10^46)+3683/2500) := by
  have hJ : (3683/2500:ℝ)^2*(f*B)≤
      f*(176338357/78125000)*B+v*52*Real.sqrt 3*(49958012987/15625000000) := by
    have hh := mul_le_mul_of_nonneg_right
      (show (3683/2500:ℝ)^2≤176338357/78125000 by norm_num) (mul_nonneg hf hB)
    have hr : 0≤v*52*Real.sqrt 3*(49958012987/15625000000) := by positivity
    nlinarith only [hh,hr]
  have hK : (3683/2500:ℝ)*(f*B)≤
      f*(47879/31250)*B+v*52*Real.sqrt 3*(3683/2500)*(3683/2500) := by
    have hh := mul_le_mul_of_nonneg_right
      (show (3683/2500:ℝ)≤47879/31250 by norm_num) (mul_nonneg hf hB)
    have hr : 0≤v*52*Real.sqrt 3*(3683/2500)*(3683/2500) := by positivity
    nlinarith only [hh,hr]
  have ha := mul_le_mul_of_nonneg_left hJ (show 0≤(232/125:ℝ)*a^2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hK (show 0≤2*k by positivity)
  have hc : 2*v*(3683/2500)≤v*2*(Real.sqrt 3*(3/10^46)+3683/2500) := by
    have hr : 0≤v*2*(Real.sqrt 3*(3/10^46)) := by positivity
    nlinarith only [hr]
  nlinarith only [ha,hb,hc]

/-- The physical source slope fits the exact unrounded mean-slope expression. -/
theorem parent_row_mean_source_slope_le (height : ℕ) :
    parentBoundaryMeanSourceSlope gammaZero height≤parentRowMeanSlopeValue height := by
  let v := parentRowVarianceClock height
  let a2 := parentRowWeightedClock parentRowA2Weight height
  let a4 := parentRowWeightedClock parentRowA4Weight height
  let a := Real.sqrt (a2*(39/5))+Real.sqrt (a2*(156/5))*(36/25)+
    Real.sqrt (a4*(46488/25))*(57/200)
  let k := a2*(78/5)*((36/25)/Real.sqrt 2+1/4+Real.sqrt 2*(57/200))
  have hv : 0≤v := by
    unfold v parentRowVarianceClock nativeSourceShellClock
    apply Finset.sum_nonneg
    intro i _
    norm_num only [gammaZero]
    positivity
  have hw (w : ℕ → ℚ) (hw : ∀ i,0≤w i) : 0≤parentRowWeightedClock w height := by
    unfold parentRowWeightedClock
    apply Finset.sum_nonneg
    intro i _
    have hi : (0:ℝ)≤(w i:ℝ) := by exact_mod_cast hw i
    unfold nativeSourceShellClock
    norm_num only [gammaZero]
    positivity
  have ha2 : 0≤a2 := hw _ (fun i => by unfold parentRowA2Weight; positivity)
  have ha4 : 0≤a4 := hw _ (fun i => by unfold parentRowA4Weight; positivity)
  have hk : 0≤k := by dsimp only [k]; positivity
  have hA : parentBoundaryMeanAColumn a2 a4=a := by
    dsimp only [parentBoundaryMeanAColumn,a]
    rw [Real.sqrt_mul ha2,Real.sqrt_mul ha2,Real.sqrt_mul ha4]
    ring
  have hK : parentBoundaryMeanKConstant*a2=k := by
    dsimp only [parentBoundaryMeanKConstant,k]
    ring
  unfold parentBoundaryMeanSourceSlope
  rw [parent_row_mean_variance_eq,parent_row_mean_a2_eq,parent_row_mean_a4_eq,
    parent_row_mean_raw_factor_eq,parent_row_mean_raw_base_eq]
  dsimp only
  rw [hA,hK]
  exact mean_slope_scalar v a k _ _ hv hk (by positivity)
    (by unfold parentRowRawBase; positivity)

/-- Every one of the sixteen stored slope fields pays the primitive source mean return. -/
theorem parent_row_mean_source_slope_field (j : Fin 16) :
    parentBoundaryMeanSourceSlope gammaZero (j.val+1)≤(parentRowFields j).getD 11 0 := by
  rw [parent_row_mean_slope_eq]
  exact parent_row_mean_source_slope_le _

end
end ASDExplicitGamma.Native
