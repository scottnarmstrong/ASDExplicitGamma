module

public import ASDExplicitGamma.Gaussian.DerivativeLawFamilies
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Pathwise differentiation preserves joint Gaussianity, including the original values. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section

/-- A value or an evaluated actual first derivative, retaining the auxiliary field index. -/
def derivativeAugment {Ω A V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : A → Ω → V → ℝ) (D : A → Ω → V → V →L[ℝ] ℝ) :
    Sum (A × V) ((A × V) × V) → Ω → ℝ :=
  Sum.elim (fun p ω => f p.1 ω p.2) (fun p ω => D p.1.1 ω p.1.2 p.2)

/-- Joint Gaussianity of genuine values and derivatives of any differentiable Gaussian family. -/
theorem isCenteredGaussianFamily_derivativeAugment {Ω A V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : A → Ω → V → ℝ) (D : A → Ω → V → V →L[ℝ] ℝ)
    (hfg : IsCenteredGaussianFamily μ (fun p : A × V => fun ω => f p.1 ω p.2))
    (hD : ∀ a x v, AEMeasurable (fun ω => D a ω x v) μ)
    (hderiv : ∀ a ω x, HasFDerivAt (f a ω) (D a ω x) x) :
    IsCenteredGaussianFamily μ (derivativeAugment f D) := by
  classical
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  let point : ℕ → Sum (A × V) ((A × V) × V) → Fin 2 → A × V := fun n o k =>
    o.elim (fun p => p) (fun p => if k=0 then p.1 else (p.1.1,p.1.2+ε n • p.2))
  let coeff : ℕ → Sum (A × V) ((A × V) × V) → Fin 2 → ℝ := fun n o k =>
    o.elim (fun _ => if k=0 then 1 else 0) (fun _ => if k=0 then -(ε n)⁻¹ else (ε n)⁻¹)
  let X := fun n o ω => ∑ k : Fin 2, coeff n o k*f (point n o k).1 ω (point n o k).2
  have hX (n : ℕ) : IsCenteredGaussianFamily μ (X n) := hfg.finite_linear_image (point n) (coeff n)
  have hmeas (o) : AEMeasurable (derivativeAugment f D o) μ := by
    cases o with
    | inl p => exact hfg.1 p
    | inr p => exact hD p.1.1 p.1.2 p.2
  have hε : Tendsto ε atTop (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall ?_⟩
    intro n
    change 1/((n:ℝ)+1) ≠ 0
    positivity
  apply isCenteredGaussianFamily_ae_limit μ X (derivativeAugment f D) hX hmeas
  intro o
  apply Filter.Eventually.of_forall
  intro ω
  cases o with
  | inl p =>
      have he : (fun n => X n (.inl p) ω) = fun _ => f p.1 ω p.2 := by
        funext n
        simp only [X, point, coeff, Sum.elim_inl, Fin.sum_univ_two,
          ite_true, one_mul, zero_mul, add_zero, show (1:Fin 2)≠0 by decide, ite_false]
      rw [he]
      exact tendsto_const_nhds
  | inr p =>
      have hl : HasDerivAt (fun t : ℝ => p.1.2+t • p.2) p.2 0 := by
        simpa only [id_eq, one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const p.2).const_add p.1.2
      have hd : HasDerivAt (fun t : ℝ => f p.1.1 ω (p.1.2+t • p.2)) (D p.1.1 ω p.1.2 p.2) 0 := by
        simpa only [zero_smul, add_zero, Function.comp_def] using (hderiv p.1.1 ω (p.1.2+(0:ℝ) • p.2)).comp_hasDerivAt 0 hl
      have ht := hd.tendsto_slope_zero.comp hε
      have he : (fun n => X n (.inr p) ω) =
          fun n => (ε n)⁻¹*(f p.1.1 ω (p.1.2+ε n • p.2)-f p.1.1 ω p.1.2) := by
        funext n
        simp only [X, point, coeff, Sum.elim_inr, Fin.sum_univ_two, ite_true,
          show (1:Fin 2)≠0 by decide, ite_false]
        ring
      rw [he]
      simpa only [derivativeAugment, Sum.elim_inr, Function.comp_def, zero_add, zero_smul, add_zero, smul_eq_mul] using ht

end
end ASDExplicitGamma.Gaussian
