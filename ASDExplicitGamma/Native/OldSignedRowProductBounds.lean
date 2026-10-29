module

public import ASDExplicitGamma.Native.OldSignedRowMultiplier

/-! Sharp OLD quarter-order contraction estimates from the existing
Hilbert Poincare and product theorems. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Genuine Hilbert H1 input has the sharp uncentered positive-Haar bound. -/
theorem old_signed_hilbert_h1_positive_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (u : HilbertH1Function (openCubeSet Q) E) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) u.toFun)) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) u.toFun ≤
      hilbertL2Norm Q u.toFun+cubeScaleFactor Q*planarC1*Real.sqrt (hilbertGradientEnergy Q u.grad) := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hp := hilbert_positive_poincare_of_weight Q hq hq9 u
  have hc : haarPoincareM2 (Real.sqrt 3)=planarC1^2 := by
    rw [planarC1_sq]
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
  have hE := hilbertEnergy_nonneg Q u.toFun
  have hG : 0≤hilbertGradientEnergy Q u.grad :=
    Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg Q _)
  refine ⟨hp.1,?_⟩
  change Real.sqrt (hilbertPrimalEnergy Q (Real.sqrt 3) u.toFun) ≤
    Real.sqrt (hilbertEnergy Q u.toFun)+cubeScaleFactor Q*planarC1*Real.sqrt (hilbertGradientEnergy Q u.grad)
  have hC : 0≤cubeScaleFactor Q*planarC1 :=
    mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _)),?_⟩
  have hs : (Real.sqrt (hilbertEnergy Q u.toFun)+
      cubeScaleFactor Q*planarC1*Real.sqrt (hilbertGradientEnergy Q u.grad))^2=
      hilbertEnergy Q u.toFun+cubeScaleFactor Q^2*planarC1^2*hilbertGradientEnergy Q u.grad+
        2*Real.sqrt (hilbertEnergy Q u.toFun)*(cubeScaleFactor Q*planarC1)*Real.sqrt (hilbertGradientEnergy Q u.grad) := by
    rw [add_sq,mul_pow,mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hG]
    ring
  rw [hs]
  rw [hc] at hp
  exact hp.2.1.trans (le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hC) (Real.sqrt_nonneg _)))


/-- A literal smooth white-row contraction of an actual Hilbert H1 field
has the full sharp AN (2.6) one-cell bill, retaining the same kernel. -/
theorem old_signed_row_h1_product_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (u : HilbertH1Function (openCubeSet Q) E) {M D : ℝ} (hM : 0≤M) (hD : 0≤D)
    (hm : ∀ᵐ x ∂normalizedCubeMeasure Q,‖b x‖≤M)
    (hd : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i,‖(fderiv ℝ b x) (basisVec i)‖^2)≤D^2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => inner ℝ (b x) (u.toFun x)))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => inner ℝ (b x) (u.toFun x)) ≤
      (M+cubeScaleFactor Q*planarC1*D)*hilbertL2Norm Q u.toFun+
        cubeScaleFactor Q*planarC1*M*Real.sqrt (hilbertGradientEnergy Q u.grad) := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hp := old_signed_hilbert_h1_positive_bound Q u
  have hm' : ∀ᵐ x ∂normalizedCubeMeasure Q,‖(oldSignedRowMultiplier Q b hb).toFun x‖≤M := by
    simpa only [old_signed_row_multiplier_norm] using hm
  have hd' : ∀ᵐ x ∂normalizedCubeMeasure Q,(∑ i,‖(oldSignedRowMultiplier Q b hb).grad x i‖^2)≤D^2 := by
    simpa only [old_signed_row_multiplier_gradient_norm] using hd
  have ht := hilbert_positive_product_of_bounds (oldSignedRowMultiplier Q b hb) hq hq9
    (u.memL2_normalized Q) hp.1 hM hD hm' hd'
  have hc : Real.sqrt (haarPoincareM2 (Real.sqrt 3))=planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  refine ⟨ht.1,?_⟩
  have hh := ht.2.trans (add_le_add (mul_le_mul_of_nonneg_left hp.2 hM) le_rfl)
  rw [hc] at hh
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
