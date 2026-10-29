module

public import ASDExplicitGamma.Native.ParentWeakFieldClocks
public import ASDExplicitGamma.Native.ParentBoundaryWeakMeanSum

/-! Readable exact stored weak slope and its literal source interpretation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Cold Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

/-- The actual unrounded weak-slope formula, retaining all positive Young,
center-variance and original rare allowances of the source program. -/
def parentWeakFieldSlopeValue (height : ℕ) : ℝ :=
  let b : ℝ := 3683/2500
  let g := gammaZero
  let D := 1-inverseHistoryDiscount^2
  let v := parentBoundaryCommonSourceVariance g height
  let F := parentBoundaryCommonRawFactor g height 5
  let U := parentBoundaryCommonRawBase g height 5
  let V := 32474*g
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock g height 5 2
  let qr := inverseHistoryDiscount^2*(3:ℝ)^(4*g+1/64)
  D*((∑ i : Fin 3,parentBoundaryWeakMeanCoefficients g height i*
        ((26/25:ℝ)*b^3*F*parentBoundaryWeakGeo g 10 (i.val+2) U V+
          52*v*Real.sqrt 3*b^4/(1-parentBoundaryWeakRatio g 8 (i.val+2))))+
    2*K*((26/25:ℝ)*b^2*F*parentBoundaryWeakGeo g 8 2 U V+
      52*v*Real.sqrt 3*b^3/(1-parentBoundaryWeakRatio g 6 2))+
    2*v*b^2/(1-parentBoundaryWeakRatio g 4 0)+
    2*v*b*Real.sqrt 3*(3/10^46)/(1-qr))

/-- The kernel-identified expression denotes exactly the readable source
formula, including its complete depth-geometric denominators. -/
theorem parent_weak_field_expr_eval (env : ℕ → ℝ) (hlog : env 2=Real.log 3)
    (height : ℕ) :
    evalReal env (parentWeakFieldSlopeExpr height)=parentWeakFieldSlopeValue height := by
  simp only [parentWeakFieldSlopeExpr,evalReal,
    parent_row_variance_expr_eval env hlog,parent_row_weighted_expr_eval env hlog,
    hlog,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,
    Rat.cast_zero,Rat.cast_one,one_mul,mul_one,zero_add]
  rw [←parent_weak_field_variance_eq,←parent_weak_field_a2_eq,←parent_weak_field_a4_eq,
    ←parent_weak_field_raw_factor_eq,←parent_weak_field_raw_base_eq]
  simp only [parentWeakFieldSlopeValue,parentBoundaryWeakGeo,parentBoundaryWeakRatio,
    parentBoundaryWeakMeanCoefficients,parentBoundaryMeanKConstant,Fin.sum_univ_three,
    Fin.val_zero,Fin.val_one,Fin.val_two,parent_weak_field_discount_root,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3),
    Real.sqrt_mul' _ (by norm_num : (0:ℝ)≤39/5),
    Real.sqrt_mul' _ (by norm_num : (0:ℝ)≤156/5),
    Real.sqrt_mul' _ (by norm_num : (0:ℝ)≤46488/25)]
  have ha2 : (1/Real.sqrt (Real.sqrt (3:ℝ)))^2=1/Real.sqrt (3:ℝ) := by
    rw [div_pow,one_pow,Real.sq_sqrt (Real.sqrt_nonneg (3:ℝ))]
  have ha2prod : (1/Real.sqrt (Real.sqrt (3:ℝ)))*(1/Real.sqrt (Real.sqrt (3:ℝ)))=1/Real.sqrt (3:ℝ) := by
    rw [←pow_two,ha2]
  simp only [ha2,ha2prod]
  norm_num [gammaZero]
  ring

end
end ASDExplicitGamma.Native
