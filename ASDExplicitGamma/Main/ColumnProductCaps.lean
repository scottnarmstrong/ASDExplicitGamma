module

public import ASDExplicitGamma.Main.HilbertColumnProduct
public import ASDExplicitGamma.Triadic.HilbertPoincareNumerics

/-! Source decimal majorants for the actual Hilbert column product. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

/-- The sharp Dirichlet L2 bridge is below the source's conservative c0 cap. -/
theorem main_planarCD_lt : planarCD < (440/1000:ℝ) := by
  have hc := planarC1_decimal_bounds.2
  have hc0 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hp : (9:ℝ) < Real.pi^2 := by nlinarith only [hpi]
  have hi : 1/(2*Real.pi^2) < (1/18:ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    linarith only [hp]
  have hs := planarCD_sq
  have hcd0 : 0 ≤ planarCD := Real.sqrt_nonneg _
  nlinarith only [hc, hc0, hi, hs, hcd0]

/-- The source column constants .637 and .440*.304 bound the exact
Hilbert product with its internally proved zero-trace bridges. -/
theorem main_hilbert_column_decimal {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    (b : Vec 2 → F) (hb : ContDiff ℝ 1 b)
    (u : H10Function (openCubeSet Q)) {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hm : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b x‖ ≤ M)
    (hd : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i, ‖(fderiv ℝ b x) (basisVec i)‖^2) ≤ D^2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => u.toH1Function.toFun x • b x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => u.toH1Function.toFun x • b x) ≤
      (cubeScaleFactor Q*(637/1000)*M +
        cubeScaleFactor Q^2*(440/1000)*(304/1000)*D)*
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  obtain ⟨hs, he⟩ := main_hilbert_column_dirichlet Q b hb u hM hD hm hd
  refine ⟨hs, he.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))⟩
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ hM
    apply mul_le_mul_of_nonneg_left _ (cubeScaleFactor_pos' Q).le
    linarith only [planarFD_lt_decimal]
  · apply mul_le_mul_of_nonneg_right _ hD
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left main_planarCD_lt.le (sq_nonneg _)
    · linarith only [planarC1_decimal_bounds.2]
    · exact Real.sqrt_nonneg _
    · positivity

end ASDExplicitGamma.Main
