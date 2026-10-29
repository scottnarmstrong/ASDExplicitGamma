module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalScales
public import ASDExplicitGamma.Main.Q3RemainderCaps

/-! The centered fine row retains its original smaller remainder coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- Exact physical derivative root factorization, with positive shell length. -/
theorem old_hessian_derivative_root_factor (C b : ℝ) (hC : 0≤C)
    (L : {l : ℝ // 0<l}) (p : ℕ) :
    Real.sqrt (C*b^2/(L.val^p)^2)=Real.sqrt C*|b|/L.val^p := by
  calc
    _ = Real.sqrt (C*b^2)/Real.sqrt ((L.val^p)^2) := Real.sqrt_div (mul_nonneg hC (sq_nonneg b)) _
    _ = _ := by rw [Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,Real.sqrt_sq (pow_nonneg L.property.le p)]

/-- The actual centered residual uses the fine kr, with the full derivative
traces unchanged and no coarse radius substituted into feedback. -/
theorem old_hessian_physical_centered_remainder (m : ℤ) (b : ℝ) :
    mainQ3RemainderExact (diagMeshRadius (originCube 2 (m+129)) 134) b (q3ModelLength (m+1)).val≤
      evalReal scalarRealEnv lowerKrExpr*|b| := by
  apply (mainQ3RemainderExact_le (diagMeshRadius_pos _ _).le).trans_eq
  let L := q3ModelLength (m+1)
  let r := diagMeshRadius (originCube 2 (m+129)) 134
  have hs1 := old_hessian_derivative_root_factor (156/5) b (by norm_num) L 1
  have hs2 := old_hessian_derivative_root_factor (46488/25) b (by norm_num) L 2
  simp only [pow_one] at hs1
  have he : (L.val^2)^2=L.val^4 := by ring
  rw [he] at hs2
  unfold mainQ3RemainderConstant
  rw [hs1,hs2]
  have hfactor : (2018/1000:ℝ)*r*(Real.sqrt (156/5)*|b|/L.val)+
      (285/1000:ℝ)*r^2*(Real.sqrt (46488/25)*|b|/L.val^2)=
      ((2018/1000:ℝ)*Real.sqrt (156/5)*(r/L.val)+
        (285/1000:ℝ)*Real.sqrt (46488/25)*(r/L.val)^2)*|b| := by ring
  change (2018/1000:ℝ)*r*(Real.sqrt (156/5)*|b|/L.val)+
      (285/1000:ℝ)*r^2*(Real.sqrt (46488/25)*|b|/L.val^2)=_
  rw [hfactor]
  have hratio := old_hessian_physical_mesh_ratio m 5
  change r/L.val=1/(3:ℝ)^6 at hratio
  rw [hratio]
  apply congrArg (fun x : ℝ => x*|b|)
  norm_num [evalReal,lowerKrExpr,lowerS1Expr,lowerS2Expr,sc]
  ring

end
end ASDExplicitGamma.Scalar
