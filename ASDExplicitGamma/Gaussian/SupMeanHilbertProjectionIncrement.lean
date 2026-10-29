module

public import ASDExplicitGamma.Gaussian.SupMeanHilbertIncrement

/-! Sharp kernel projection increments from genuine weak derivatives and pointwise operator bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- A uniform operator bound on the weak derivative tensor gives the same
operator constant for every finite kernel projection increment. -/
theorem supMean_hilbert_kernel_projection_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K D : ι → ℝ → H) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ i u t, HasDerivAt (fun s => ⟪u,K i s⟫) ⟪u,D i t⟫ t)
    (hB : ∀ u t, (∑ i, ⟪u,D i t⟫^2) ≤ M*‖u‖^2) (a : ι → ℝ) :
    ‖∑ i, a i • (K i 1-K i 0)‖^2 ≤ M*(∑ i, a i^2) := by
  let F : ℝ → H := fun t => ∑ i, a i • K i t
  let G : ℝ → H := fun t => ∑ i, a i • D i t
  let C := Real.sqrt (M*(∑ i, a i^2))
  have hCsq : C^2 = M*(∑ i, a i^2) := Real.sq_sqrt (by positivity)
  have hd (u : H) (t : ℝ) : HasDerivAt (fun s => ⟪u,F s⟫) ⟪u,G t⟫ t := by
    have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hD i u t).const_mul (a i))
    have hf : (∑ i, fun s => a i*⟪u,K i s⟫) = (fun s => ⟪u,F s⟫) := by
      funext s
      simp only [Finset.sum_apply, F, inner_sum, real_inner_smul_right]
    have hg : (∑ i, a i*⟪u,D i t⟫) = ⟪u,G t⟫ := by
      simp only [G, inner_sum, real_inner_smul_right]
    rw [hf,hg] at hh
    exact hh
  have hb (t : ℝ) : ‖G t‖^2 ≤ C^2 := by
    rw [hCsq]
    exact supMean_hilbert_combination_sq_bound (fun i => D i t) M hM (fun u => hB u t) a
  have hh := supMean_hilbert_tensor_increment_sq (fun _ : Unit => F) (fun _ : Unit => G)
    C (Real.sqrt_nonneg _) (fun _ u t => hd u t) (fun t => by simpa using hb t)
  have he : F 1-F 0 = ∑ i, a i • (K i 1-K i 0) := by
    simp only [F, Finset.sum_sub_distrib, smul_sub]
  simpa only [Fintype.sum_unique, he, hCsq] using hh

end
end ASDExplicitGamma.Gaussian
