module

public import ASDExplicitGamma.Triadic.HilbertSensitivityTail
public import ASDExplicitGamma.Triadic.HilbertCellPoincare

/-! Exact general-weight positive Haar Poincare constants for real Hilbert fields. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

/-- Weighted residual summability implies actual positive increment summability. -/
theorem hilbert_positive_summable_of_residual {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (q : ℝ)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j => q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x))) :
    Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F)) := by
  let a : ℕ → ℝ := fun n => hilbertEnergy Q (hilbertCubeIncrement Q n F)
  have haa : Summable a := (hilbert_haar_parseval Q hF).1
  have hr (j : ℕ) : hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) = haarEnergyTail a j :=
    (hilbert_haar_parseval Q hF).2.2 j
  have ht : Summable (fun j => q^j*haarEnergyTail a j) := by simpa only [hr] using hs
  have hd := summable_weighted_differences (haarEnergyTail a) q ht
  have he (k : ℕ) : haarEnergyTail a (k+1)-haarEnergyTail a k = -a (k+1) := by
    rw [haarEnergyTail_eq_succ haa k]; ring
  simpa only [he, mul_neg, summable_neg_iff] using hd

/-- The source constant M_s squared, expressed in its geometric Haar weight. -/
def haarPoincareM2 (q : ℝ) : ℝ := (q-1)/((1-q/9)*Real.pi^2)

/-- The source constant C_s squared for the mean-zero positive norm. -/
def haarPoincareC2 (q : ℝ) : ℝ := 8*q/((9-q)*Real.pi^2)

/-- Full general-weight Hilbert-valued cell estimates with proved P membership. -/
theorem hilbert_positive_poincare_of_weight {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) {q : ℝ}
    (hq : 1 < q) (hq9 : q < 9) (u : HilbertH1Function (openCubeSet Q) E) :
    Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) u.toFun)) ∧
    hilbertPrimalEnergy Q q u.toFun ≤ hilbertEnergy Q u.toFun+
      cubeScaleFactor Q^2*haarPoincareM2 q*hilbertGradientEnergy Q u.grad ∧
    hilbertPrimalCircEnergy Q q u.toFun ≤
      cubeScaleFactor Q^2*haarPoincareC2 q*hilbertGradientEnergy Q u.grad := by
  let C := cubeScaleFactor Q^2/Real.pi^2*hilbertGradientEnergy Q u.grad
  have hq0 : 0 ≤ q := zero_le_one.trans hq.le
  have hratio : q/9 < 1 := (div_lt_one (by norm_num)).2 hq9
  have hratio0 : 0 ≤ q/9 := div_nonneg hq0 (by norm_num)
  have hg : Summable (fun j : ℕ => (q/9)^j*C) :=
    (summable_geometric_of_lt_one hratio0 hratio).mul_right C
  have hb (j : ℕ) : q^j*hilbertEnergy Q (fun x => u.toFun x-hilbertCubeProjection Q j u.toFun x) ≤ (q/9)^j*C := by
    have h := mul_le_mul_of_nonneg_left (hilbert_cell_poincare Q j u) (pow_nonneg hq0 j)
    refine h.trans_eq ?_
    dsimp [C]
    rw [div_pow]
    ring
  have ht : Summable (fun j => q^j*hilbertEnergy Q (fun x => u.toFun x-hilbertCubeProjection Q j u.toFun x)) :=
    hg.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hq0 j) (hilbertEnergy_nonneg Q _)) hb
  have hP := hilbert_positive_summable_of_residual Q q (u.memL2_normalized Q) ht
  have hid := hilbert_sensitivity_tail_of_weight Q hq (u.memL2_normalized Q) hP
  have hsum := ht.tsum_le_tsum hb hg
  rw [tsum_mul_right, tsum_geometric_of_lt_one hratio0 hratio] at hsum
  have hmult := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hq.le)
  have hzero := hilbert_cell_poincare Q 0 u
  simp only [pow_zero, one_mul] at hzero
  have hc : C+(q-1)*((1-q/9)⁻¹*C) = cubeScaleFactor Q^2*haarPoincareC2 q*hilbertGradientEnergy Q u.grad := by
    dsimp [C, haarPoincareC2]
    field_simp [ne_of_gt (sub_pos.mpr hq9), ne_of_gt (sub_pos.mpr hratio), Real.pi_ne_zero]
    ring
  have hm : (q-1)*((1-q/9)⁻¹*C) = cubeScaleFactor Q^2*haarPoincareM2 q*hilbertGradientEnergy Q u.grad := by
    dsimp [C, haarPoincareM2]
    field_simp [ne_of_gt (sub_pos.mpr hratio), Real.pi_ne_zero]
  refine ⟨hP, ?_, ?_⟩
  · rw [hid.2.1, ← hm]
    exact add_le_add le_rfl hmult
  · rw [hid.2.2, ← hc]
    exact add_le_add hzero hmult

/-- TR-POINCARE-CELL-CONSTANTS at the exact source weight, for every 0<s<1. -/
theorem hilbert_positive_poincare {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (u : HilbertH1Function (openCubeSet Q) E) :
    let q := (3:ℝ)^(2*s)
    Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) u.toFun)) ∧
    hilbertPrimalEnergy Q q u.toFun ≤ hilbertEnergy Q u.toFun+
      cubeScaleFactor Q^2*haarPoincareM2 q*hilbertGradientEnergy Q u.grad ∧
    hilbertPrimalCircEnergy Q q u.toFun ≤ cubeScaleFactor Q^2*haarPoincareC2 q*hilbertGradientEnergy Q u.grad := by
  have hq : 1 < (3:ℝ)^(2*s) := Real.one_lt_rpow (by norm_num : (1:ℝ)<3) (mul_pos (by norm_num) hs.1)
  have hq9 : (3:ℝ)^(2*s) < 9 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<3) (show 2*s < 2 by linarith only [hs.2])
    norm_num at h ⊢
    exact h
  exact hilbert_positive_poincare_of_weight Q hq hq9 u

end
end ASDExplicitGamma.Triadic
