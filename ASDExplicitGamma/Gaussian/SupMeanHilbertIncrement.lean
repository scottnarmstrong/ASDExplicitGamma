module

public import ASDExplicitGamma.Gaussian.SupMeanHilbertTensor
public import Mathlib.Analysis.Calculus.MeanValue

/-! Mean-square tensor increments from genuine scalar weak derivatives of a Hilbert kernel. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- A Hilbert-valued curve needs only its genuine scalar weak derivative identities
for this exact finite-tensor increment bound. -/
theorem supMean_hilbert_tensor_increment_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι]
    (K D : ι → ℝ → H) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ i u t, HasDerivAt (fun s => ⟪u,K i s⟫) ⟪u,D i t⟫ t)
    (hb : ∀ t, (∑ i, ‖D i t‖^2) ≤ C^2) :
    (∑ i, ‖K i 1-K i 0‖^2) ≤ C^2 := by
  let u : ι → H := fun i => K i 1-K i 0
  let U : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 u
  let F : ℝ → ℝ := fun t => ∑ i, ⟪u i,K i t⟫
  have hd (t : ℝ) : HasDerivAt F (∑ i, ⟪u i,D i t⟫) t := by
    have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ => hD i (u i) t)
    have heq : (∑ i, fun s => ⟪u i,K i s⟫) = F := by
      funext s
      simp only [Finset.sum_apply, F]
    rw [heq] at hh
    exact hh
  have hb' (t : ℝ) : ‖∑ i, ⟪u i,D i t⟫‖ ≤ ‖U‖*C := by
    let V : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 (fun i => D i t)
    have hV : ‖V‖ ≤ C := by
      apply (sq_le_sq₀ (norm_nonneg _) hC).mp
      rw [PiLp.norm_sq_eq_of_L2]
      exact hb t
    have he : (∑ i, ⟪u i,D i t⟫) = ⟪U,V⟫ := by rw [PiLp.inner_apply]
    rw [he]
    exact (norm_inner_le_norm U V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb' t)
  have he : F 1-F 0 = ‖U‖^2 := by
    simp only [F, ← Finset.sum_sub_distrib, ← inner_sub_right, U, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_self_eq_norm_sq (u i)
  rw [he, Real.norm_of_nonneg (sq_nonneg _)] at hm
  have hU : ‖U‖ ≤ C := by
    by_cases hzero : ‖U‖ = 0
    · rw [hzero]
      exact hC
    · have hp : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg U) (Ne.symm hzero)
      nlinarith only [hm,hp]
  have hh := pow_le_pow_left₀ (norm_nonneg U) hU 2
  simpa only [U, PiLp.norm_sq_eq_of_L2, u] using hh

end
end ASDExplicitGamma.Gaussian
