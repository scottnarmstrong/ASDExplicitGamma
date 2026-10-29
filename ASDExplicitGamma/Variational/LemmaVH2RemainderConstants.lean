module

public import ASDExplicitGamma.Variational.LemmaVH2Constants

/-! Exact conversion of the common-center covariance caps to the source B_n. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
noncomputable section

 theorem lemmaVH2RowConstant_remainder {v L S : ℝ} (hv : 0 ≤ v) (hL : 0 < L) (hS : 0 ≤ S) (r : ℝ) :
    lemmaVH2RowConstant r (Real.sqrt (v*(lemmaVH2R1/2)*(S/L)^2))
      (Real.sqrt (lemmaVH2R1*(v/L^2))) (Real.sqrt (lemmaVH2A2*(v/L^4))) =
        Real.sqrt v*lemmaVH2Bn (S/L) (r/L) := by
  have hr1 : 0 ≤ lemmaVH2R1 := by norm_num [lemmaVH2R1]
  have ha2 : 0 ≤ lemmaVH2A2 := by norm_num [lemmaVH2A2, lemmaVH2R1]
  have hA : Real.sqrt (v*(lemmaVH2R1/2)*(S/L)^2) = Real.sqrt v*Real.sqrt (lemmaVH2R1/2)*(S/L) := by
    rw [Real.sqrt_mul (mul_nonneg hv (div_nonneg hr1 (by norm_num))),
      Real.sqrt_mul hv, Real.sqrt_sq (div_nonneg hS hL.le)]
  have hG : Real.sqrt (lemmaVH2R1*(v/L^2)) = Real.sqrt v*Real.sqrt lemmaVH2R1/L := by
    rw [Real.sqrt_mul hr1, Real.sqrt_div hv, Real.sqrt_sq hL.le]
    ring
  have hH : Real.sqrt (lemmaVH2A2*(v/L^4)) = Real.sqrt v*Real.sqrt lemmaVH2A2/L^2 := by
    rw [Real.sqrt_mul ha2, Real.sqrt_div hv, show L^4=(L^2)^2 by ring, Real.sqrt_sq (sq_nonneg L)]
    ring
  unfold lemmaVH2RowConstant lemmaVH2Bn
  rw [hA,hG,hH]
  field_simp

end
end ASDExplicitGamma.Variational
