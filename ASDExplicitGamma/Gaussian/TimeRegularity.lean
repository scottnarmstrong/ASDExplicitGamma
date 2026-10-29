module

public import ASDExplicitGamma.Gaussian.MappedHeat
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! # The precise time-dependent test class (8.8) -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- A time C¹, field C² test with joint operator-norm continuity and one
polynomial bound. `D` is its actual time derivative, including the one-sided endpoints. -/
structure TimeRegularity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G D : ℝ → E → ℝ) : Prop where
  continuous_value : ContinuousOn (Function.uncurry G) (Icc (0 : ℝ) 1 ×ˢ univ)
  continuous_time : ContinuousOn (Function.uncurry D) (Icc (0 : ℝ) 1 ×ˢ univ)
  field_c2 : ∀ t ∈ Icc (0 : ℝ) 1, ContDiff ℝ 2 (G t)
  time_derivative : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    HasDerivWithinAt (fun s => G s x) (D t x) (Icc 0 1) t
  continuous_field_derivative : ContinuousOn (fun p : ℝ × E => fderiv ℝ (G p.1) p.2)
    (Icc (0 : ℝ) 1 ×ˢ univ)
  continuous_field_hessian : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (G p.1)) p.2)
    (Icc (0 : ℝ) 1 ×ˢ univ)
  polynomial_bound : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    |G t x| + |D t x| + ‖fderiv ℝ (G t) x‖ + ‖fderiv ℝ (fderiv ℝ (G t)) x‖ ≤
      C * (1 + ‖x‖) ^ d

/-- Joint differentiability is a consequence of the source's continuous partial derivatives. -/
theorem TimeRegularity.hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (x : E) :
    HasFDerivAt (Function.uncurry G)
      (((D t x) • ContinuousLinearMap.id ℝ ℝ).coprod (fderiv ℝ (G t) x)) (t, x) := by
  have hnhds : Icc (0 : ℝ) 1 ×ˢ (univ : Set E) ∈ 𝓝 (t, x) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (by simp)
  apply (hasStrictFDerivAt_uncurry_coprod (f := G) (u := (t, x))
    (f₁ := fun t x => (D t x) • ContinuousLinearMap.id ℝ ℝ)
    (f₂ := fun t x => fderiv ℝ (G t) x) ?_ ?_ ?_ ?_).hasFDerivAt
  · have hopen : Ioo (0 : ℝ) 1 ×ˢ (univ : Set E) ∈ 𝓝 (t, x) :=
      prod_mem_nhds (Ioo_mem_nhds ht.1 ht.2) (by simp)
    filter_upwards [hopen] with p hp
    have hd := (hG.time_derivative p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
    have hc : ContinuousLinearMap.toSpanSingleton ℝ (D p.1 p.2) =
        (D p.1 p.2) • ContinuousLinearMap.id ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro a
      change a * D p.1 p.2 = D p.1 p.2 * a
      exact mul_comm _ _
    change HasFDerivAt (fun s => G s p.2) ((D p.1 p.2) • ContinuousLinearMap.id ℝ ℝ) p.1
    rw [← hc]
    exact hd.hasFDerivAt
  · filter_upwards [hnhds] with p hp
    exact ((hG.field_c2 p.1 hp.1).differentiable (by norm_num) p.2).hasFDerivAt
  · exact ((hG.continuous_time (t, x) ⟨⟨ht.1.le, ht.2.le⟩, mem_univ x⟩).continuousAt hnhds).smul continuousAt_const
  · exact (hG.continuous_field_derivative (t, x) ⟨⟨ht.1.le, ht.2.le⟩, mem_univ x⟩).continuousAt hnhds

/-- The directional second derivative is evaluation of the bounded Hessian. -/
theorem second_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x u w : E) :
    fderiv ℝ (fun z => fderiv ℝ f z w) x u = fderiv ℝ (fderiv ℝ f) x u w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one x
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

/-- Each time slice belongs to the already proved polynomial C² heat-test class. -/
theorem TimeRegularity.field_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasPolynomiallyBoundedC2Derivatives (G t) := by
  obtain ⟨C, hC, d, hb⟩ := hG.polynomial_bound
  refine ⟨hG.field_c2 t ht, C, hC, d, ?_, ?_, ?_⟩
  · intro x
    have h := hb t ht x
    linarith [abs_nonneg (D t x), norm_nonneg (fderiv ℝ (G t) x), norm_nonneg (fderiv ℝ (fderiv ℝ (G t)) x)]
  · intro x
    have h := hb t ht x
    linarith [abs_nonneg (G t x), abs_nonneg (D t x), norm_nonneg (fderiv ℝ (fderiv ℝ (G t)) x)]
  · intro x u w
    rw [second_fderiv_eq (hG.field_c2 t ht)]
    have hnorm : ‖fderiv ℝ (fderiv ℝ (G t)) x‖ ≤ C * (1 + ‖x‖) ^ d := by
      have h := hb t ht x
      linarith [abs_nonneg (G t x), abs_nonneg (D t x), norm_nonneg (fderiv ℝ (G t) x)]
    exact ((fderiv ℝ (fderiv ℝ (G t)) x).le_opNorm₂ u w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)) (norm_nonneg w))

/-- The source's time/field partial derivatives imply the ordinary chain rule along insertion. -/
theorem TimeRegularity.hasDerivAt_path {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D) (x z : E)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => G s (x + Real.sqrt s • z))
      (D t (x + Real.sqrt t • z) + (1 / (2 * Real.sqrt t)) *
        fderiv ℝ (G t) (x + Real.sqrt t • z) z) t := by
  have hp := (hasDerivAt_id t).prodMk
    (((Real.hasDerivAt_sqrt ht.1.ne').smul_const z).const_add x)
  have h := (hG.hasFDerivAt ht (x + Real.sqrt t • z)).comp_hasDerivAt t hp
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq,
    ContinuousLinearMap.coprod_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one, map_smul] using h

end ASDExplicitGamma.Gaussian
