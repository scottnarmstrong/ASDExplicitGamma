module

public import ASDExplicitGamma.Triadic.HilbertOperatorSobolev

/-! Literal essential supremum and spatial Frobenius derivative norms of operator fields. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

 def operatorSpatialFrobenius {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Fin d → E →L[ℝ] F) : ℝ := Real.sqrt (∑ i, ‖G i‖^2)

 def HilbertOperatorW1Infinity.valueLInf {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) : ℝ := lpNorm b.toFun ⊤ (normalizedCubeMeasure Q)

 def HilbertOperatorW1Infinity.derivativeFrobeniusLInf {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) : ℝ := lpNorm (fun x => operatorSpatialFrobenius (b.grad x)) ⊤ (normalizedCubeMeasure Q)

 theorem HilbertOperatorW1Infinity.frobenius_memLp_top {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) : MemLp (fun x => operatorSpatialFrobenius (b.grad x)) ⊤ (normalizedCubeMeasure Q) := by
  have hs : MemLp (fun x => ∑ i, ‖b.grad x i‖) ⊤ (normalizedCubeMeasure Q) :=
    memLp_finsetSum Finset.univ fun i _ => (b.gradMemLp_top i).norm
  have hmeas : AEStronglyMeasurable (fun x => operatorSpatialFrobenius (b.grad x)) (normalizedCubeMeasure Q) := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => ((b.gradMemLp_top i).aestronglyMeasurable.norm).pow 2) using 1
    funext x
    simp only [Finset.sum_apply, Pi.pow_apply]
  apply hs.mono' hmeas
  apply Filter.Eventually.of_forall
  intro x
  change |Real.sqrt (∑ i, ‖b.grad x i‖^2)| ≤ _
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_iff).2 ⟨Finset.sum_nonneg fun _ _ => norm_nonneg _,
    Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _⟩

 theorem HilbertOperatorW1Infinity.ae_value_le {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b.toFun x‖ ≤ b.valueLInf :=
  ae_le_lpNorm_exponent_top b.memLp_top

 theorem HilbertOperatorW1Infinity.ae_gradient_sq_le {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖b.grad x i‖^2) ≤ b.derivativeFrobeniusLInf^2 := by
  have h := ae_le_lpNorm_exponent_top b.frobenius_memLp_top
  filter_upwards [h] with x hx
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hx 2
  simpa only [Real.norm_eq_abs, sq_abs, HilbertOperatorW1Infinity.derivativeFrobeniusLInf, operatorSpatialFrobenius,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using hsq

end
end ASDExplicitGamma.Triadic
