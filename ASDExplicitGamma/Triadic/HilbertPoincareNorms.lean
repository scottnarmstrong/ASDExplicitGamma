module

public import ASDExplicitGamma.Triadic.HilbertPoincareConstants
public import ASDExplicitGamma.Triadic.PlanarConstants

/-! Source norm notation and sharp quarter-order identifications. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
noncomputable section

/-- The actual normalized Hilbert-valued L2 norm. -/
def hilbertL2Norm {d : ℕ} {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d) (F : Vec d → E) : ℝ :=
  Real.sqrt (hilbertEnergy Q F)

/-- The positive Hilbert-valued Haar norm at weight q; membership is explicit at uses. -/
def hilbertPositiveHaarNorm {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (q : ℝ) (F : Vec d → E) : ℝ := Real.sqrt (hilbertPrimalEnergy Q q F)

/-- The mean-zero positive Hilbert-valued Haar norm. -/
def hilbertPositiveCircHaarNorm {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (q : ℝ) (F : Vec d → E) : ℝ := Real.sqrt (hilbertPrimalCircEnergy Q q F)

 theorem hilbert_cube_poincare_norm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d)
    (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertL2Norm Q (fun x => u.toFun x-hilbertCubeAverage Q u.toFun) ≤
      cubeScaleFactor Q/Real.pi*Real.sqrt (hilbertGradientEnergy Q u.grad) := by
  have h := Real.sqrt_le_sqrt (hilbert_cube_poincare Q u)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (cubeScaleFactor_pos' Q).le Real.pi_pos.le)] at h
  exact h

 theorem hilbert_positive_circ_poincare_norm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertPositiveCircHaarNorm Q ((3:ℝ)^(2*s)) u.toFun ≤
      cubeScaleFactor Q*Real.sqrt (haarPoincareC2 ((3:ℝ)^(2*s)))*Real.sqrt (hilbertGradientEnergy Q u.grad) := by
  have h := Real.sqrt_le_sqrt (hilbert_positive_poincare Q s hs u).2.2
  have hgrad : 0 ≤ hilbertGradientEnergy Q u.grad := Finset.sum_nonneg fun _ _ => hilbertEnergy_nonneg Q _
  rw [Real.sqrt_mul' _ hgrad,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (cubeScaleFactor_pos' Q).le] at h
  exact h

 theorem haarPoincareM2_quarter : haarPoincareM2 ((3:ℝ)^(2*(1/4:ℝ))) = planarC1^2 := by
  rw [planarC1_sq]
  norm_num only [show 2*(1/4:ℝ) = 1/2 by norm_num]
  rw [← Real.sqrt_eq_rpow]
  unfold haarPoincareM2
  rw [mul_comm (1-Real.sqrt 3/9)]

 theorem haarPoincareC2_quarter : haarPoincareC2 ((3:ℝ)^(2*(1/4:ℝ))) = planarC0^2 := by
  rw [planarC0_sq]
  norm_num only [show 2*(1/4:ℝ) = 1/2 by norm_num]
  rw [← Real.sqrt_eq_rpow]
  rfl

end
end ASDExplicitGamma.Triadic
