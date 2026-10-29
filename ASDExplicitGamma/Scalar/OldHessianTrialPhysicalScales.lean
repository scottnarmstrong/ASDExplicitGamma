module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceEnvelopeMoment

/-! Exact physical mesh ratios and source coefficients on the OLD parent. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section

/-- Parent depth129+r has precisely the original physical ratio3^(-r-1). -/
theorem old_hessian_physical_mesh_ratio (m : ℤ) (r : ℕ) :
    (cubeScaleFactor (originCube 2 (m+129))/(3:ℝ)^(129+r))/(q3ModelLength (m+1)).val=
      1/(3:ℝ)^(r+1) := by
  rw [cubeScaleFactor_originCube]
  change (3:ℝ)^(m+129)/(3:ℝ)^(129+r)/(3:ℝ)^(m+1)=_
  rw [←zpow_natCast,←zpow_sub₀ (by norm_num : (3:ℝ)≠0),
    ←zpow_sub₀ (by norm_num : (3:ℝ)≠0)]
  have he : m+129-((129+r:ℕ):ℤ)-(m+1)=-((r+1:ℕ):ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,one_div]

/-- The complete uncentered row coefficient retains the exact two full
Gaussian derivative traces, before its physical mesh is substituted. -/
theorem old_hessian_source_multiplier_factor (Q : TriadicCube 2) (r : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    oldSignedSourceMultiplier Q r b L=
      (1+(36/25:ℝ)*Real.sqrt (156/5)*(diagMeshRadius Q r/L.val)+
        (57/200:ℝ)*Real.sqrt (46488/25)*(diagMeshRadius Q r/L.val)^2)*|b| := by
  have hL : 0≤L.val := L.property.le
  have he : L.val^4=(L.val^2)^2 := by ring
  have hroot (C : ℝ) (hC : 0≤C) (p : ℕ) :
      Real.sqrt (C*b^2/(L.val^p)^2)=Real.sqrt C*|b|/L.val^p := by
    calc
      _ = Real.sqrt (C*b^2)/Real.sqrt ((L.val^p)^2) := Real.sqrt_div (mul_nonneg hC (sq_nonneg b)) _
      _ = _ := by rw [Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,Real.sqrt_sq (pow_nonneg hL p)]
  have hfirst := hroot (156/5) (by norm_num) 1
  have hsecond := hroot (46488/25) (by norm_num) 2
  simp only [pow_one] at hfirst
  rw [←he] at hsecond
  unfold oldSignedSourceMultiplier
  rw [Real.sqrt_sq_eq_abs,hfirst,hsecond]
  ring

/-- The actual depth134 row multiplier is exactly the frozen A times |b|. -/
theorem old_hessian_physical_source_multiplier (m : ℤ) (b : ℝ) :
    oldSignedSourceMultiplier (originCube 2 (m+129)) 134 b (q3ModelLength (m+1))=
      Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerAExpr*|b| := by
  rw [old_hessian_source_multiplier_factor]
  have hh := old_hessian_physical_mesh_ratio m 5
  change (cubeScaleFactor (originCube 2 (m+129))/(3:ℝ)^134)/(q3ModelLength (m+1)).val=1/(3:ℝ)^6 at hh
  unfold diagMeshRadius
  rw [hh]
  apply congrArg (fun x : ℝ => x*|b|)
  norm_num [Numerics.Mirror.evalReal,Numerics.Scalar.lowerAExpr,Numerics.Scalar.lowerS1Expr,
    Numerics.Scalar.lowerS2Expr,Numerics.Scalar.sc]
  ring

/-- The genuine coarse-column coefficient retains its full sqrt2 trace
and the radius three times the fine radius. -/
theorem old_hessian_physical_coarse_column (m : ℤ) (b : ℝ) :
    oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b (q3ModelLength (m+1))=
      Real.sqrt 2*(205069/19683000:ℝ)*|b| := by
  unfold oldHessianCoarseColumnCoefficient
  have hh := old_hessian_physical_mesh_ratio m 4
  change (cubeScaleFactor (originCube 2 (m+129))/(3:ℝ)^133)/(q3ModelLength (m+1)).val=1/(3:ℝ)^5 at hh
  rw [hh]
  norm_num

end
end ASDExplicitGamma.Scalar
