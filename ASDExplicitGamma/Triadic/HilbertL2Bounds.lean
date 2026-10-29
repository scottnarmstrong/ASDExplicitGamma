module

public import ASDExplicitGamma.Triadic.HilbertPoincareNorms

/-! Actual Hilbert L2 bounds used by the operator-valued multiplier argument. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
noncomputable section

 theorem hilbertEnergy_norm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (F : Vec d → E) : energy Q (fun x => ‖F x‖) = hilbertEnergy Q F := by
  rw [energy_eq_integral_sq]; rfl

 theorem hilbertEnergy_residual_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) ≤ hilbertEnergy Q F := by
  have hp := hilbert_haar_parseval Q hF
  rw [hp.2.2 j]
  have h := hp.1.sum_add_tsum_nat_add (j+1)
  rw [hp.2.1] at h
  have hn : 0 ≤ ∑ n ∈ Finset.range (j+1), hilbertEnergy Q (hilbertCubeIncrement Q n F) :=
    Finset.sum_nonneg fun _ _ => hilbertEnergy_nonneg Q _
  simp only [← Nat.add_assoc] at h
  linarith only [h, hn]

/-- Minkowski for the literal normalized Hilbert-valued L2 norm. -/
theorem hilbertL2Norm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {F G : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    hilbertL2Norm Q (fun x => F x+G x) ≤ hilbertL2Norm Q F+hilbertL2Norm Q G := by
  let μ := normalizedCubeMeasure Q
  have hpoint (x : Vec d) : ‖F x+G x‖^2 ≤ (‖F x‖+‖G x‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have hupper : hilbertEnergy Q (fun x => F x+G x) ≤ energy Q (fun x => ‖F x‖+‖G x‖) := by
    rw [energy_eq_integral_sq]
    exact integral_mono_ae ((hF.add hG).integrable_norm_pow (by norm_num))
      (by simpa only [Real.norm_eq_abs, sq_abs, Pi.add_apply] using (hF.norm.add hG.norm).integrable_norm_pow (by norm_num : 2 ≠ 0))
      (Filter.Eventually.of_forall hpoint)
  have hfg := abs_pairing_le Q hF.norm hG.norm
  simp only [l2Norm, hilbertEnergy_norm] at hfg
  have hneg : energy Q (-fun x => ‖G x‖) = hilbertEnergy Q G := by
    rw [energy_eq_integral_sq]
    simp only [Pi.neg_apply, neg_sq]
    rfl
  have hpneg : pairing Q (fun x => ‖F x‖) (-fun x => ‖G x‖) = -pairing Q (fun x => ‖F x‖) (fun x => ‖G x‖) := by
    simp only [pairing, cubeAverage_eq_integral_normalizedCubeMeasure, Pi.neg_apply, mul_neg, integral_neg]
  have hsub := energy_sub Q hF.norm hG.norm.neg
  have hadd : energy Q (fun x => ‖F x‖+‖G x‖) = hilbertEnergy Q F+2*pairing Q (fun x => ‖F x‖) (fun x => ‖G x‖)+hilbertEnergy Q G := by
    simpa only [Pi.neg_apply, sub_neg_eq_add, hneg, hpneg,
      hilbertEnergy_norm, mul_neg] using hsub
  rw [hadd] at hupper
  apply (Real.sqrt_le_iff).2
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have hsF := Real.sq_sqrt (hilbertEnergy_nonneg Q F)
  have hsG := Real.sq_sqrt (hilbertEnergy_nonneg Q G)
  change hilbertEnergy Q (fun x => F x+G x) ≤ (Real.sqrt (hilbertEnergy Q F)+Real.sqrt (hilbertEnergy Q G))^2
  nlinarith only [hupper, (le_abs_self _).trans hfg, hsF, hsG]

end
end ASDExplicitGamma.Triadic
