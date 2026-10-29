module

public import ASDExplicitGamma.Gaussian.SupMeanGaussianMoments

/-! Actual Gaussian difference moments agree with differences of a genuine covariance kernel. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- Differences of two observations retain their full joint Gaussian law. -/
theorem supMean_gaussian_difference_family {Ω I J : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) (p q : J → I) :
    IsCenteredGaussianFamily μ (fun j ω => X (p j) ω-X (q j) ω) := by
  have hh := hX.finite_linear_image
    (fun j (a : Fin 2) => if a=0 then p j else q j)
    (fun (_ : J) (a : Fin 2) => if a=0 then (1:ℝ) else -1)
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using! hh

/-- A covariance kernel's Hilbert distance is the actual second moment of the
corresponding centered Gaussian observation difference. -/
theorem supMean_gaussian_kernel_difference_sq {Ω I H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (μ : Measure Ω)
    (X : I → Ω → ℝ) (hX : IsCenteredGaussianFamily μ X) (K : I → H)
    (hcov : ∀ i j, (∫ ω, X i ω*X j ω ∂μ) = ⟪K i,K j⟫) (i j : I) :
    (∫ ω, (X i ω-X j ω)^2 ∂μ) = ‖K i-K j‖^2 := by
  have hi (k : I) : Integrable (fun ω => (X k ω)^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hX.memLp k 2 (by simp)).integrable_norm_pow (by decide : 2 ≠ 0)
  have hij : Integrable (fun ω => X i ω*X j ω) μ :=
    (hX.memLp i 2 (by simp)).integrable_mul (hX.memLp j 2 (by simp))
  have hdiag (k : I) : (∫ ω, (X k ω)^2 ∂μ) = ⟪K k,K k⟫ := by
    simpa only [pow_two] using hcov k k
  have heq : (fun ω => (X i ω-X j ω)^2) =
      (fun ω => (X i ω)^2-2*(X i ω*X j ω)+(X j ω)^2) := by funext ω; ring
  have hs : Integrable (fun ω => (X i ω)^2-2*(X i ω*X j ω)) μ := by
    simpa only [Pi.sub_apply] using! (hi i).sub (hij.const_mul 2)
  rw [heq, integral_add (f := fun ω => (X i ω)^2-2*(X i ω*X j ω))
      (g := fun ω => (X j ω)^2) hs (hi j),
    integral_sub (f := fun ω => (X i ω)^2) (g := fun ω => 2*(X i ω*X j ω))
      (hi i) (hij.const_mul 2), integral_const_mul, hdiag, hdiag, hcov,
    norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

end ASDExplicitGamma.Gaussian
