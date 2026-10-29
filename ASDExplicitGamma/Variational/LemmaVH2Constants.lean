module

public import ASDExplicitGamma.Triadic.HilbertPoincareNumerics
public import ASDExplicitGamma.Model.Q3DerivativeMoments

/-! Exact source constants for the three Lemma V H2 routes. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Model
noncomputable section

 def lemmaVH2R1 : ℝ := 78/5
 def lemmaVH2A2 : ℝ := 3432/5+lemmaVH2R1^2
 def lemmaVH2C1 : ℝ := 36/25
 def lemmaVH2C2 : ℝ := 57/200

/-- Outward 340 coefficient for given value, gradient, and Hessian caps. -/
def lemmaVH2RowConstant (r A G H : ℝ) : ℝ := A+r*lemmaVH2C1*G+r^2*lemmaVH2C2*H

/-- Source B_n for the common-center nonstationary remainder. -/
def lemmaVH2Bn (ρ δ : ℝ) : ℝ := Real.sqrt (lemmaVH2R1/2)*ρ+
  lemmaVH2C1*Real.sqrt lemmaVH2R1*δ+lemmaVH2C2*Real.sqrt lemmaVH2A2*δ^2

/-- Source k_n for the deterministic covariance-defect direction. -/
def lemmaVH2kn (ρ δ : ℝ) : ℝ := (lemmaVH2R1/4)*ρ^2+
  lemmaVH2C1*(lemmaVH2R1/Real.sqrt 2)*ρ*δ+lemmaVH2C2*lemmaVH2R1*Real.sqrt 2*δ^2

/-- Stationary-band feedback constant: the planar 340 refinement of DIAG15. -/
def lemmaVH2BandConstant (r V0 V2 V4 : ℝ) : ℝ := Real.sqrt V0+
  lemmaVH2C1*r*Real.sqrt (lemmaVH2R1*V2)+lemmaVH2C2*r^2*Real.sqrt (lemmaVH2A2*V4)

 theorem lemmaVH2C1_outward : planarC1+2/Real.pi+1/2 ≤ lemmaVH2C1 := by
  have hp : 2/Real.pi < (0.636620:ℝ) := (div_lt_iff₀ Real.pi_pos).2 (by nlinarith only [Real.pi_gt_d6])
  have hc := planarC1_decimal_bounds.2
  unfold lemmaVH2C1
  linarith only [hp,hc]

 theorem lemmaVH2C2_outward : planarC1*(planarC0+1/2) ≤ lemmaVH2C2 := by
  have h := mul_le_mul planarC1_decimal_bounds.2.le (add_le_add planarC0_decimal_bounds.2.le (le_refl (1/2:ℝ)))
    (add_nonneg (show 0 ≤ planarC0 from Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)) (by norm_num : (0:ℝ) ≤ 0.3030651876)
  unfold lemmaVH2C2
  linarith only [h]

 theorem lemmaVH2RowConstant_nonneg {r A G H : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H) :
    0 ≤ lemmaVH2RowConstant r A G H := by unfold lemmaVH2RowConstant lemmaVH2C1 lemmaVH2C2; positivity

 theorem lemmaVH2RowConstant_scale (r A G H c : ℝ) :
    lemmaVH2RowConstant r (A*c) (G*c) (H*c) = lemmaVH2RowConstant r A G H*c := by
  unfold lemmaVH2RowConstant
  ring

end
end ASDExplicitGamma.Variational
