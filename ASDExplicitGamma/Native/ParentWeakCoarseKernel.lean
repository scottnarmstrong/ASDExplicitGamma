module

public import ASDExplicitGamma.Native.ParentWeakCoarseClocks

/-! Coarse geometric bounds reserved exclusively for the correlated rare payments. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The source covariance polynomial is uniformly small when both finite
spatial clocks are at most one. -/
theorem parent_weak_kernel_unit_cap {A2 A4 : ℝ} (h2 : A2 ≤ 1) (h4 : A4 ≤ 1) :
    parentBoundaryCommonKernelProfile A2 A4 1 ≤ 20000 := by
  apply (parent_boundary_common_kernel_profile_mono h2 h4 (by norm_num : (0:ℝ)≤1)).trans
  have h0 : Real.sqrt (39/5:ℝ) ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h1 : Real.sqrt (156/5:ℝ) ≤ 6 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h2 : Real.sqrt (78/5:ℝ) ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h3 : Real.sqrt (46488/25:ℝ) ≤ 44 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h4 : Real.sqrt (23244/25:ℝ) ≤ 31 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  let a := Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ)+(57/200:ℝ)*Real.sqrt (46488/25:ℝ)
  let b := Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (78/5:ℝ)+(57/200:ℝ)*Real.sqrt (23244/25:ℝ)
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have ha : a ≤ 25 := by dsimp only [a]; linarith only [h0,h1,h3]
  have hb : b ≤ 18 := by dsimp only [b]; linarith only [h0,h2,h4]
  have hasq := pow_le_pow_left₀ ha0 ha 2
  have hbsq := pow_le_pow_left₀ hb0 hb 2
  have he : parentBoundaryCommonKernelProfile 1 1 1=(232/125:ℝ)*a^2+38*b^2 := by
    norm_num [parentBoundaryCommonKernelProfile,a,b]
  rw [he]
  linarith only [hasq,hbsq]

/-- Uniform affine-geometric allowance inside the literal source ratios. -/
theorem parent_weak_affine_geo_cap {q U V : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 9/10) (hU0 : 0 ≤ U) (hU : U ≤ 10000)
    (hV0 : 0 ≤ V) (hV : V ≤ 12) :
    0 ≤ U/(1-q)+V*q/(1-q)^2 ∧ U/(1-q)+V*q/(1-q)^2 ≤ 200000 := by
  have hd : (1/10:ℝ) ≤ 1-q := by linarith only [hq]
  have hdpos : 0 < 1-q := lt_of_lt_of_le (by norm_num) hd
  have hdsq : (1/100:ℝ) ≤ (1-q)^2 := by
    exact (by norm_num : (1/100:ℝ)=(1/10)^2).le.trans (pow_le_pow_left₀ (by norm_num) hd 2)
  have hfirst : U/(1-q) ≤ 100000 := (div_le_iff₀ hdpos).mpr
    (hU.trans ((by norm_num : (10000:ℝ)=100000*(1/10)).le.trans
      (mul_le_mul_of_nonneg_left hd (by norm_num))))
  have hvq : V*q ≤ 12 := (mul_le_mul hV (hq.trans (by norm_num : (9/10:ℝ)≤1)) hq0 (by norm_num : (0:ℝ)≤12)).trans_eq (by norm_num)
  have hsecond : V*q/(1-q)^2 ≤ 1200 := (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
    (hvq.trans ((by norm_num : (12:ℝ)=1200*(1/100)).le.trans
      (mul_le_mul_of_nonneg_left hdsq (by norm_num))))
  exact ⟨add_nonneg (div_nonneg hU0 hdpos.le) (div_nonneg (mul_nonneg hV0 hq0) (sq_nonneg _)),by linarith only [hfirst,hsecond]⟩

/-- Every complete source geometric kernel is uniformly bounded on the
sixteen parent bands, before multiplying by the original rare reserve. -/
theorem parent_weak_kernel_geometric_cap {A2 A4 growth U V : ℝ}
    (h2 : A2 ≤ 1) (h4 : A4 ≤ 1) (hg : growth ≤ 8)
    (hU0 : 0 ≤ U) (hU : U ≤ 10000) (hV0 : 0 ≤ V) (hV : V ≤ 12) :
    0 ≤ parentBoundaryCommonKernelGeometric A2 A4 gammaZero growth U V ∧
      parentBoundaryCommonKernelGeometric A2 A4 gammaZero growth U V ≤ 4000000000 := by
  let c := parentBoundaryCommonKernelCoefficients A2 A4
  let q := parentBoundaryCommonHistoryRatio gammaZero growth
  have hc (i : Fin 5) : 0 ≤ c i := parent_boundary_common_kernel_coefficients_nonneg A2 A4 i
  have hq0 (i : Fin 5) : 0 ≤ q i :=
    (parent_boundary_common_history_ratio_range (by norm_num [gammaZero]) le_rfl growth hg i).1
  have hgeo (i : Fin 5) : 0 ≤ U/(1-q i)+V*q i/(1-q i)^2 ∧
      U/(1-q i)+V*q i/(1-q i)^2 ≤ 200000 :=
    parent_weak_affine_geo_cap (hq0 i) (parent_weak_common_ratio_le growth hg i) hU0 hU hV0 hV
  have hsum : (∑ i : Fin 5,c i) ≤ 20000 := by
    have he := parent_boundary_common_kernel_profile_polynomial A2 A4 1
    simp only [one_pow,mul_one] at he
    exact he.symm.le.trans (parent_weak_kernel_unit_cap h2 h4)
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (hgeo i).1),?_⟩
  calc
    _ ≤ ∑ i : Fin 5,c i*200000 := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hgeo i).2 (hc i))
    _ = (∑ i : Fin 5,c i)*200000 := (Finset.sum_mul _ _ _).symm
    _ ≤ 20000*200000 := mul_le_mul_of_nonneg_right hsum (by norm_num)
    _ = _ := by norm_num

end
end ASDExplicitGamma.Native
