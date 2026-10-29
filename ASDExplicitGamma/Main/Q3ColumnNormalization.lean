module

public import ASDExplicitGamma.Main.Q3ColumnHilbertSchmidt
public import ASDExplicitGamma.Main.ErrorCoefficients
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Literal source normalization and the planar quarter turn for actual columns. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian
open scoped BigOperators

/-- Moving physical scale factors inside a covariance square root. -/
theorem main_mul_sqrt_scale {r a : ℝ} (hr : 0 ≤ r) :
    r*Real.sqrt a = Real.sqrt (r^2*a) := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr]

/-- With the source shell-to-cell length ratio, the actual full-column
coefficient is exactly the literal main-return kd, without a frame substitution. -/
theorem mainQ3ColumnConstant_source {R b : ℝ} (hR : 0 < R) :
    mainQ3ColumnConstant R b (R*3^6) = mainKd (b^2) := by
  have h2 : R^2*((156/5:ℝ)*b^2/(R*3^6)^2) = (156/5)*mainA2 (b^2) := by
    unfold mainA2
    norm_num
    field_simp
    ring
  have h4 : (R^2)^2*((46488/25:ℝ)*b^2/(R*3^6)^4) = (46488/25)*mainA4 (b^2) := by
    unfold mainA4
    norm_num
    field_simp
    ring
  unfold mainQ3ColumnConstant mainKd
  have h2' := main_mul_sqrt_scale (a := (156/5:ℝ)*b^2/(R*3^6)^2) hR.le
  have h4' := main_mul_sqrt_scale (a := (46488/25:ℝ)*b^2/(R*3^6)^4) (sq_nonneg R)
  rw [h2] at h2'
  rw [h4] at h4'
  calc
    _ = (637/1000)*(R*Real.sqrt ((156/5)*b^2/(R*3^6)^2))+
        (440/1000)*(304/1000)*(R^2*Real.sqrt ((46488/25)*b^2/(R*3^6)^4)) := by ring
    _ = _ := by rw [h2', h4']

end ASDExplicitGamma.Main
