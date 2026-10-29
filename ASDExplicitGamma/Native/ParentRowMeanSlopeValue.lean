module

public import ASDExplicitGamma.Native.ParentRowMeanSlopeFields

/-! Readable real interpretation of the exact parent mean slope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The source parent mean slope, retaining the full Young and variance allowances. -/
def parentRowMeanSlopeValue (height : ℕ) : ℝ :=
  let v := parentRowVarianceClock height
  let a2 := parentRowWeightedClock parentRowA2Weight height
  let a4 := parentRowWeightedClock parentRowA4Weight height
  let a := Real.sqrt (a2*(39/5)) + Real.sqrt (a2*(156/5))*(36/25)+
    Real.sqrt (a4*(46488/25))*(57/200)
  let f := Real.exp (Real.log 3*((17/50000)*(2*(height:ℝ)+24)))*4
  let j := f*(176338357/78125000)*(parentRowRawBase height:ℝ)+
    v*52*Real.sqrt 3*(49958012987/15625000000)
  let kj := f*(47879/31250)*(parentRowRawBase height:ℝ)+
    v*52*Real.sqrt 3*(3683/2500)*(3683/2500)
  let k := a2*(78/5)*((36/25)/Real.sqrt 2+1/4+Real.sqrt 2*(57/200))
  a*a*(232/125)*j+k*2*kj+v*2*(Real.sqrt 3*(3/10^46)+3683/2500)

/-- The symbolic source program has exactly the readable real meaning. -/
theorem parent_row_mean_slope_expr_eval (env : ℕ → ℝ)
    (hlog : env 2=Real.log 3) (height : ℕ) :
    evalReal env (parentRowMeanSlopeExpr height)=parentRowMeanSlopeValue height := by
  simp only [parentRowMeanSlopeExpr,evalReal,
    parent_row_variance_expr_eval env hlog,parent_row_weighted_expr_eval env hlog,
    hlog,parentRowMeanSlopeValue,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,zero_add,one_mul]

/-- Every selected parent mean-slope field is its exact readable source formula. -/
theorem parent_row_mean_slope_eq (j : Fin 16) :
    (parentRowFields j).getD 11 0=parentRowMeanSlopeValue (j.val+1) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,
    nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,
    nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,
    nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,
    nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,
    nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_mean_slope_001.trans (parent_row_mean_slope_expr_eval _ (by rfl) 1)
  · exact parent_row_mean_slope_002.trans (parent_row_mean_slope_expr_eval _ (by rfl) 2)
  · exact parent_row_mean_slope_003.trans (parent_row_mean_slope_expr_eval _ (by rfl) 3)
  · exact parent_row_mean_slope_004.trans (parent_row_mean_slope_expr_eval _ (by rfl) 4)
  · exact parent_row_mean_slope_005.trans (parent_row_mean_slope_expr_eval _ (by rfl) 5)
  · exact parent_row_mean_slope_006.trans (parent_row_mean_slope_expr_eval _ (by rfl) 6)
  · exact parent_row_mean_slope_007.trans (parent_row_mean_slope_expr_eval _ (by rfl) 7)
  · exact parent_row_mean_slope_008.trans (parent_row_mean_slope_expr_eval _ (by rfl) 8)
  · exact parent_row_mean_slope_009.trans (parent_row_mean_slope_expr_eval _ (by rfl) 9)
  · exact parent_row_mean_slope_010.trans (parent_row_mean_slope_expr_eval _ (by rfl) 10)
  · exact parent_row_mean_slope_011.trans (parent_row_mean_slope_expr_eval _ (by rfl) 11)
  · exact parent_row_mean_slope_012.trans (parent_row_mean_slope_expr_eval _ (by rfl) 12)
  · exact parent_row_mean_slope_013.trans (parent_row_mean_slope_expr_eval _ (by rfl) 13)
  · exact parent_row_mean_slope_014.trans (parent_row_mean_slope_expr_eval _ (by rfl) 14)
  · exact parent_row_mean_slope_015.trans (parent_row_mean_slope_expr_eval _ (by rfl) 15)
  · exact parent_row_mean_slope_016.trans (parent_row_mean_slope_expr_eval _ (by rfl) 16)

end
end ASDExplicitGamma.Native
