module

public import Homogenization.Sobolev.Foundations.H10Graph
public import Homogenization.Sobolev.PotentialSolenoidal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The local H10-gradient projection on a bounded open convex square. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization

/-- The closed subspace of actual H10 gradients on a bounded convex domain. -/
noncomputable def lambda8H10GradientRange {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    ClosedSubmodule ℝ (HilbertVectorL2 U) where
  toSubmodule :=
    LinearMap.range (H10GraphClosed.gradientCLM (d := d) (U := U)).toLinearMap
  isClosed' := H10GraphClosed.isClosed_range_gradientCLM (U := U) hU

/-- The actual local Dirichlet projection of a Hilbert-vector L2 load. -/
noncomputable def lambda8DirichletProjection {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (F : HilbertVectorL2 U) : HilbertVectorL2 U :=
  (lambda8H10GradientRange hU).toSubmodule.starProjection F

/-- The local projection is the gradient of an honest H10 function. -/
theorem lambda8DirichletProjection_isPotentialZeroTrace
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (F : HilbertVectorL2 U) :
    ∃ u : H10Function U,
      u.toH1Function.gradToHilbertVectorL2 = lambda8DirichletProjection hU F := by
  have hmem : lambda8DirichletProjection hU F ∈
      (lambda8H10GradientRange hU).toSubmodule :=
    (lambda8H10GradientRange hU).toSubmodule.starProjection_apply_mem F
  rcases hmem with ⟨z, hz⟩
  change H10GraphClosed.gradientCLM (U := U) z =
      lambda8DirichletProjection hU F at hz
  obtain ⟨u, huval, hugrad⟩ :=
    exists_h10Function_of_mem_h10GraphClosedSubmodule
      (U := U) hU (z := z.1) z.2
  refine ⟨u, ?_⟩
  have hgrad : u.toH1Function.gradToHilbertVectorL2 =
      H10GraphClosed.gradientCLM (U := U) z := by
    simpa [H10GraphClosed.gradientCLM] using hugrad
  exact hgrad.trans hz

/-- The projection residual is orthogonal to every actual H10 gradient. -/
theorem lambda8DirichletProjection_residual_orthogonal
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (F : HilbertVectorL2 U)
    (u : H10Function U) :
    inner ℝ (F - lambda8DirichletProjection hU F)
      u.toH1Function.gradToHilbertVectorL2 = 0 := by
  let K := lambda8H10GradientRange hU
  have horth := K.toSubmodule.sub_starProjection_mem_orthogonal F
  have hgrad :
      u.toH1Function.gradToHilbertVectorL2 ∈
        K.toSubmodule := by
    refine ⟨⟨(u.toH1Function.toScalarL2,
      u.toH1Function.gradToHilbertVectorL2),
      (Submodule.le_topologicalClosure _)
        (h10_pair_mem_h10GraphSubmodule (U := U) u)⟩, ?_⟩
    simp [H10GraphClosed.gradientCLM]
  exact (Submodule.mem_orthogonal' _ _).mp horth _ hgrad

/-- Orthogonal changes to the source do not change its local Dirichlet
projection. This is the comparison principle used against a whole-space
solenoidal residual. -/
theorem lambda8DirichletProjection_eq_of_orthogonal
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (F H : HilbertVectorL2 U)
    (hFH : ∀ y ∈ (lambda8H10GradientRange hU).toSubmodule,
      inner ℝ (F - H) y = 0) :
    lambda8DirichletProjection hU F = lambda8DirichletProjection hU H := by
  let K := lambda8H10GradientRange hU
  have hFmem : K.toSubmodule.starProjection F ∈ K.toSubmodule :=
    K.toSubmodule.starProjection_apply_mem F
  have hForth : F - K.toSubmodule.starProjection F ∈ K.toSubmoduleᗮ :=
    K.toSubmodule.sub_starProjection_mem_orthogonal F
  have hdiff : F - H ∈ K.toSubmoduleᗮ :=
    (Submodule.mem_orthogonal' _ _).2 hFH
  have hHorth : H - K.toSubmodule.starProjection F ∈ K.toSubmoduleᗮ := by
    convert K.toSubmoduleᗮ.sub_mem hForth hdiff using 1
    abel_nf
  change K.toSubmodule.starProjection F = K.toSubmodule.starProjection H
  exact (K.toSubmodule.eq_starProjection_of_mem_orthogonal hFmem hHorth).symm

/-- The local Dirichlet projection is bounded by any source with the same
pairings against zero-trace gradients. -/
theorem lambda8DirichletProjection_norm_le_of_orthogonal
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (F H : HilbertVectorL2 U)
    (hFH : ∀ y ∈ (lambda8H10GradientRange hU).toSubmodule,
      inner ℝ (F - H) y = 0) :
    ‖lambda8DirichletProjection hU F‖ ≤ ‖H‖ := by
  rw [lambda8DirichletProjection_eq_of_orthogonal hU F H hFH]
  exact (lambda8H10GradientRange hU).toSubmodule.norm_orthogonalProjectionOnto_apply_le H

/-- A physical solenoidal residual makes the local Dirichlet projection
orthogonal to the stationary comparison field. -/
theorem lambda8DirichletProjection_norm_le_of_solenoidalResidual
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {F H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hH : MemVectorL2 U H)
    (hsol : IsSolenoidalOn U (fun x => F x - H x)) :
    ‖lambda8DirichletProjection hU (toHilbertVectorL2OfVecField hF)‖ ≤
      ‖toHilbertVectorL2OfVecField hH‖ := by
  apply lambda8DirichletProjection_norm_le_of_orthogonal hU _ _
  intro y hy
  rcases hy with ⟨z, hz⟩
  change H10GraphClosed.gradientCLM (U := U) z = y at hz
  obtain ⟨u, huval, hugrad⟩ :=
    exists_h10Function_of_mem_h10GraphClosedSubmodule
      (U := U) hU (z := z.1) z.2
  have hgrad : u.toH1Function.gradToHilbertVectorL2 =
      H10GraphClosed.gradientCLM (U := U) z := by
    simpa [H10GraphClosed.gradientCLM] using hugrad
  have hygrad : u.toH1Function.gradToHilbertVectorL2 = y := hgrad.trans hz
  have hres : MemVectorL2 U (fun x => F x - H x) := hF.sub hH
  have hsub := toHilbertVectorL2OfVecField_sub hF hH
  rw [← hsub, ← hygrad]
  exact (inner_toHilbertVectorL2OfVecField_eq_integral hres
    u.toH1Function.grad_memVectorL2).trans (hsol u)

end ASDExplicitGamma.Scalar
