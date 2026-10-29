module

public import ASDExplicitGamma.Triadic.PlanarSobolev
public import Homogenization.Sobolev.H1.BasicLemmas
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual C2 scalar fields yield the weak Sobolev witness consumed by the
coarse-sensitivity theorem, with their unchanged spatial values. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

local instance smoothVolumeFinite (Q : TriadicCube 2) :
    IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Continuity on the compact closure gives the actual finite essential
supremum on either the normalized or unnormalized cube measure. -/
theorem continuous_memLp_top_cube (Q : TriadicCube 2) (μ : Measure (Vec 2)) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ cubeSet Q) (f : Vec 2 → ℝ) (hf : Continuous f) : MemLp f ⊤ μ := by
  obtain ⟨C,hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (hsupp.mono (fun x hx => hC x (subset_closure hx)))

theorem normalized_cube_support (Q : TriadicCube 2) :
    ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
  unfold normalizedCubeMeasure cubeMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cubeSet Q)) _

/-- The literal coordinate first derivative of the actual scalar field. -/
def smoothScalarDerivative (f : Vec 2 → ℝ) (i : Fin 2) (x : Vec 2) : ℝ :=
  (fderiv ℝ f x) (basisVec i)

theorem smooth_scalar_derivative_contDiff {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 2) :
    ContDiff ℝ 1 (smoothScalarDerivative f i) := by
  have hh := hf.contDiff_fderiv_apply (m := 1) (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)
  exact hh.comp (contDiff_id.prodMk contDiff_const)

/-- One canonical Sobolev realization of the actual C2 field and its actual
first derivatives. No derivative-domain identification is a premise. -/
def smoothW2 (Q : TriadicCube 2) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) : PlanarW2Infinity Q where
  value := H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (hf.of_le (by norm_num))
  value_memLp_top := continuous_memLp_top_cube Q _
    ((ae_restrict_mem (measurableSet_openCubeSet Q)).mono (fun _ hx => openCubeSet_subset_cubeSet Q hx)) f hf.continuous
  gradient :=
    { component := fun i => H1Function.ofContDiffOnIsOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_openCubeSet Q) (smooth_scalar_derivative_contDiff hf i)
      component_memLp_top := fun i => continuous_memLp_top_cube Q _ (normalized_cube_support Q)
        (smoothScalarDerivative f i) (smooth_scalar_derivative_contDiff hf i).continuous
      derivative_memLp_top := fun i j => continuous_memLp_top_cube Q _ (normalized_cube_support Q)
        (fun x => (fderiv ℝ (smoothScalarDerivative f i) x) (basisVec j))
        (((smooth_scalar_derivative_contDiff hf i).continuous_fderiv (by norm_num)).clm_apply continuous_const) }
  gradient_eq := fun _ => rfl

/-- Its weak gradient representatives are the genuine coordinate derivatives. -/
theorem smooth_w2_gradient (Q : TriadicCube 2) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin 2) :
    ((smoothW2 Q f hf).gradient.component i).toFun = smoothScalarDerivative f i := rfl

end
end ASDExplicitGamma.Inverse
