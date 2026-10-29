module

public import ASDExplicitGamma.Triadic.PlanarMultiplier
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry
public import Homogenization.Sobolev.H1.Algebra.H1Function

/-! Literal negation, restriction, and L-infinity bounds of planar Sobolev directions. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

 def PlanarW1Infinity.neg {Q : TriadicCube 2} (b : PlanarW1Infinity Q) : PlanarW1Infinity Q where
  component i := -(b.component i)
  component_memLp_top i := by
    have he : (-(b.component i).toFun) =ᵐ[normalizedCubeMeasure Q] (fun x => -(b.component i).toFun x) := Filter.Eventually.of_forall fun _ => rfl
    simpa only [H1Function.neg_toFun] using (memLp_congr_ae he).mp (b.component_memLp_top i).neg
  derivative_memLp_top i j := by
    have he : (-(fun x => (b.component i).grad x j)) =ᵐ[normalizedCubeMeasure Q] (fun x => -(b.component i).grad x j) := Filter.Eventually.of_forall fun _ => rfl
    simpa only [H1Function.neg_grad, Pi.neg_apply] using (memLp_congr_ae he).mp (b.derivative_memLp_top i j).neg

 def PlanarW1Infinity.restrict {Q R : TriadicCube 2} {j : ℕ} (b : PlanarW1Infinity Q)
    (hR : R ∈ descendantsAtDepth Q j) : PlanarW1Infinity R where
  component i := (b.component i).restrictToOpenSubcube hR
  component_memLp_top i := hilbert_memLp_descendant hR (b.component_memLp_top i)
  derivative_memLp_top i a := hilbert_memLp_descendant hR (b.derivative_memLp_top i a)

 def PlanarW2Infinity.restrict {Q R : TriadicCube 2} {j : ℕ} (b : PlanarW2Infinity Q)
    (hR : R ∈ descendantsAtDepth Q j) : PlanarW2Infinity R where
  value := b.value.restrictToOpenSubcube hR
  value_memLp_top := b.value_memLp_top.mono_measure
    (Measure.restrict_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) le_rfl)
  gradient := b.gradient.restrict hR
  gradient_eq i := b.gradient_eq i

 theorem PlanarW1Infinity.valueNorm_aestronglyMeasurable {Q : TriadicCube 2} (b : PlanarW1Infinity Q) :
    AEStronglyMeasurable (fun x => planarEuclideanNorm (planarW1Value b x)) (normalizedCubeMeasure Q) := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (b.component_memLp_top i).aestronglyMeasurable.pow 2) using 1
  funext x
  simp only [planarW1Value, Finset.sum_apply, Pi.pow_apply]

 theorem PlanarW1Infinity.derivativeNorm_aestronglyMeasurable {Q : TriadicCube 2} (b : PlanarW1Infinity Q) :
    AEStronglyMeasurable (fun x => planarFrobeniusNorm (planarW1Derivative b x)) (normalizedCubeMeasure Q) := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => Finset.aestronglyMeasurable_sum Finset.univ
    (fun j _ => (b.derivative_memLp_top i j).aestronglyMeasurable.pow 2)) using 1
  funext x
  simp only [planarW1Derivative, Finset.sum_apply, Pi.pow_apply]

 theorem planarW1ValueLInf_le_of_bound {Q : TriadicCube 2} (b : PlanarW1Infinity Q) {G : ℝ} (hG : 0 ≤ G)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value b x) ≤ G) : planarW1ValueLInf b ≤ G := by
  have hnorm : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖planarEuclideanNorm (planarW1Value b x)‖ ≤ G := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ planarEuclideanNorm (planarW1Value b x) from Real.sqrt_nonneg _)]
    exact hx
  have h := eLpNormEssSup_le_of_ae_bound hnorm
  unfold planarW1ValueLInf
  rw [eLpNorm_exponent_top b.valueNorm_aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hG)

 theorem planarW1DerivativeFrobeniusLInf_le_of_bound {Q : TriadicCube 2} (b : PlanarW1Infinity Q) {H : ℝ} (hH : 0 ≤ H)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative b x) ≤ H) : planarW1DerivativeFrobeniusLInf b ≤ H := by
  have hnorm : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖planarFrobeniusNorm (planarW1Derivative b x)‖ ≤ H := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ planarFrobeniusNorm (planarW1Derivative b x) from Real.sqrt_nonneg _)]
    exact hx
  have h := eLpNormEssSup_le_of_ae_bound hnorm
  unfold planarW1DerivativeFrobeniusLInf
  rw [eLpNorm_exponent_top b.derivativeNorm_aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hH)

 theorem PlanarW2Infinity.value_memLp_top_normalized {Q : TriadicCube 2} (b : PlanarW2Infinity Q) :
    MemLp b.value.toFun ⊤ (normalizedCubeMeasure Q) := by
  have h := b.value_memLp_top
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h
  exact h.smul_measure ENNReal.ofReal_ne_top

 theorem PlanarW2Infinity.grad_memLp_top_normalized {Q : TriadicCube 2} (b : PlanarW2Infinity Q) (i : Fin 2) :
    MemLp (fun x => b.value.grad x i) ⊤ (normalizedCubeMeasure Q) := by
  rw [← b.gradient_eq i]
  exact b.gradient.component_memLp_top i

end
end ASDExplicitGamma.Triadic
