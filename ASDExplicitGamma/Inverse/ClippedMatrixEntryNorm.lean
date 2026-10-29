module

public import ASDExplicitGamma.Inverse.ClippedMatrixOperatorSum
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-! Extended Lp operator norm from actual scalar matrix entries. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- Entry norm bounds pay exactly n squared for the Euclidean operator norm. -/
theorem clipped_matrix_Lp_of_entries {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] (μ : Measure Ω) (F : Ω → Matrix n n ℝ)
    (hm : ∀ i j, Measurable (fun ω => F ω i j))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ i j, eLpNorm (fun ω => F ω i j) p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (F ω)‖) p μ ≤
      ENNReal.ofReal ((Fintype.card n:ℝ)^2*B) := by
  let L : Matrix n n ℝ →ₗ[ℝ] (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
    { toFun := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A B
      map_smul' := fun r A => map_smul (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) r A }
  have hF : Measurable F := Measurable.of_eval_matrix F hm
  have hmeas : Measurable (fun ω => ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (F ω)‖) :=
    L.continuous_of_finiteDimensional.norm.measurable.comp hF
  have hs := finite_density_sum_Lp μ p hp
    (fun ij : n × n => fun ω => |F ω ij.1 ij.2|) (fun _ => 1) (fun _ => B)
    (fun _ => by norm_num) (fun _ => hB) (fun ij => by
      have hnorm := eLpNorm_norm (p := p) (μ := μ) (fun ω => F ω ij.1 ij.2) (hm ij.1 ij.2).aestronglyMeasurable
      simpa only [Real.norm_eq_abs] using hnorm.le.trans (hb ij.1 ij.2))
  simp only [one_mul] at hs
  have ht : (fun ω => ∑ ij : n × n, |F ω ij.1 ij.2|) = fun ω => ∑ i, ∑ j, |F ω i j| := by
    funext ω
    exact Fintype.sum_prod_type _
  rw [ht] at hs
  have hn := eLpNorm_mono_real (p := p) (μ := μ) hmeas.aestronglyMeasurable
    (fun ω => (norm_norm _).le.trans (clipped_matrix_operator_norm_le_sum (F ω)))
  apply (hn.trans hs).trans_eq
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

end
end ASDExplicitGamma.Inverse
