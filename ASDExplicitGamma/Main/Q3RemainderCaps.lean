module

public import ASDExplicitGamma.Main.Q3ResidualHilbertSchmidt
public import ASDExplicitGamma.Main.Q3ColumnNormalization
public import ASDExplicitGamma.Numerics.Joint.LocalCaps
public import ASDExplicitGamma.Variational.LemmaVH2Constants

/-! Exact source decimal coefficients for the actual covariance residual. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational

/-- The held conservative source coefficient, with no row/column exchange. -/
noncomputable def mainQ3RemainderConstant (r b L : ℝ) : ℝ :=
  (2018/1000)*r*Real.sqrt ((156/5)*b^2/L^2)+
    (285/1000)*r^2*Real.sqrt ((46488/25)*b^2/L^4)

/-- Certified source decimal rounding of the actual residual coefficient. -/
theorem mainQ3RemainderExact_le {r b L : ℝ} (hr : 0 ≤ r) :
    mainQ3RemainderExact r b L ≤ mainQ3RemainderConstant r b L := by
  have h := Numerics.Joint.local_caps
  have hA : 1/Real.sqrt 3+planarC1+2/Real.pi+1/2 ≤ (2018/1000:ℝ) := by
    have hp := h.2.2.2.2.2.1
    change 1/Real.sqrt 3+planarC1+(2/Real.pi+1/2) < (2018/1000:ℝ) at hp
    linarith only [hp]
  have hB : planarC1*(planarC0+1/2) ≤ (285/1000:ℝ) := by
    convert lemmaVH2C2_outward using 1; norm_num [lemmaVH2C2]
  have h1 := mul_le_mul_of_nonneg_right hA
    (mul_nonneg hr (Real.sqrt_nonneg ((156/5)*b^2/L^2)))
  have h2 := mul_le_mul_of_nonneg_right hB
    (mul_nonneg (sq_nonneg r) (Real.sqrt_nonneg ((46488/25)*b^2/L^4)))
  unfold mainQ3RemainderExact mainQ3RemainderConstant
  convert add_le_add h1 h2 using 1 <;> ring

/-- The physical shell-to-cell length substitution gives exactly mainKrem. -/
theorem mainQ3RemainderConstant_source {r b : ℝ} (hr : 0 < r) :
    mainQ3RemainderConstant r b (r*3^6) = mainKrem (b^2) := by
  have h2 : r^2*((156/5:ℝ)*b^2/(r*3^6)^2) = (156/5)*mainA2 (b^2) := by
    unfold mainA2
    norm_num
    field_simp
    ring
  have h4 : (r^2)^2*((46488/25:ℝ)*b^2/(r*3^6)^4) = (46488/25)*mainA4 (b^2) := by
    unfold mainA4
    norm_num
    field_simp
    ring
  unfold mainQ3RemainderConstant mainKrem
  have h2' := main_mul_sqrt_scale (a := (156/5:ℝ)*b^2/(r*3^6)^2) hr.le
  have h4' := main_mul_sqrt_scale (a := (46488/25:ℝ)*b^2/(r*3^6)^4) (sq_nonneg r)
  rw [h2] at h2'
  rw [h4] at h4'
  calc
    _ = (2018/1000)*(r*Real.sqrt ((156/5)*b^2/(r*3^6)^2))+
        (285/1000)*(r^2*Real.sqrt ((46488/25)*b^2/(r*3^6)^4)) := by ring
    _ = _ := by rw [h2', h4']

end ASDExplicitGamma.Main
