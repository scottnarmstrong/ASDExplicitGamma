module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

open MeasureTheory
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

section
variable {X W : Type*} [MeasurableSpace X]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (μ : Measure X)

/-- The Hilbert-valued L² kernel, paired with an input vector. -/
noncomputable def hilbertKernel (F : Lp W 2 μ) : W →L[ℝ] Lp ℝ 2 μ :=
  ((innerSL ℝ).compLpL₂ 2 μ).flip F

theorem hilbertKernel_ae (F : Lp W 2 μ) (u : W) :
    hilbertKernel μ F u =ᵐ[μ] fun x => ⟪u, F x⟫ :=
  (innerSL ℝ u).coeFn_compLp F

/-- L² uses the ordinary integral normalization, with no probability-measure factor. -/
theorem l2_norm_sq (F : Lp W 2 μ) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Finite Bessel bound for a Hilbert-valued L² kernel. -/
theorem hilbertKernel_sum_le {ι : Type*} (F : Lp W 2 μ) (e : ι → W)
    (he : Orthonormal ℝ e) (s : Finset ι) :
    (∑ i ∈ s, ‖hilbertKernel μ F (e i)‖ ^ 2) ≤ ‖F‖ ^ 2 := by
  classical
  have hnorm (i : ι) : ‖hilbertKernel μ F (e i)‖ ^ 2 = ∫ x, ⟪e i, F x⟫ ^ 2 ∂μ := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hilbertKernel_ae μ F (e i)] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs]
  have hint (i : ι) : Integrable (fun x => ⟪e i, F x⟫ ^ 2) μ :=
    ((Lp.memLp F).continuousLinearMap_comp (innerSL ℝ (e i))).integrable_sq
  simp_rw [hnorm]
  rw [← integral_finsetSum _ (fun i _ => hint i), l2_norm_sq μ F]
  apply integral_mono (integrable_finsetSum _ fun i _ => hint i) ((Lp.memLp F).integrable_norm_pow (by norm_num))
  intro x
  simpa only [Real.norm_eq_abs, sq_abs] using he.sum_inner_products_le (s := s) (x := F x)

/-- Every orthonormal input family has a summable squared image norm. -/
theorem hilbertKernel_summable {ι : Type*} (F : Lp W 2 μ) (e : ι → W)
    (he : Orthonormal ℝ e) : Summable (fun i => ‖hilbertKernel μ F (e i)‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (hilbertKernel_sum_le μ F e he)

/-- A full Hilbert basis gives the exact Hilbert–Schmidt norm, by Parseval and absolute
integral/sum exchange. -/
theorem hilbertKernel_basis_tsum_eq {ι : Type*} [Countable ι]
    (F : Lp W 2 μ) (e : HilbertBasis ι ℝ W) :
    (∑' i, ‖hilbertKernel μ F (e i)‖ ^ 2) = ‖F‖ ^ 2 := by
  have hnorm (i : ι) : ‖hilbertKernel μ F (e i)‖ ^ 2 = ∫ x, ⟪e i, F x⟫ ^ 2 ∂μ := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hilbertKernel_ae μ F (e i)] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs]
  have hint (i : ι) : Integrable (fun x => ⟪e i, F x⟫ ^ 2) μ :=
    ((Lp.memLp F).continuousLinearMap_comp (innerSL ℝ (e i))).integrable_sq
  have hs : Summable (fun i => ∫ x, ‖⟪e i, F x⟫ ^ 2‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs, ← hnorm] using
      hilbertKernel_summable μ F e e.orthonormal
  simp_rw [hnorm]
  rw [integral_tsum_of_summable_integral_norm hint hs, l2_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hh := (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (e.repr (F x))).tsum_eq
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, e.repr_apply_apply,
      Real.norm_eq_abs, sq_abs, LinearIsometryEquiv.norm_map] using hh

end
end ASDExplicitGamma.Gaussian
