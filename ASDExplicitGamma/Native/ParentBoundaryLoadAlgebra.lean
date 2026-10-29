module

public import ASDExplicitGamma.Native.ParentBoundaryLoadTrace
public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget

/-! Exact load-vector algebra and complete mixed Gram summability. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- The actual raw source is linear in its physical load vector. -/
theorem parent_boundary_raw_load_add (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v u : Vec 2) (w : WhiteNoise) :
    parentBoundaryRawLoadOperator Q b L (v+u) w =
      parentBoundaryRawLoadOperator Q b L v w + parentBoundaryRawLoadOperator Q b L u w := by
  apply Lp.ext
  filter_upwards [parent_boundary_raw_load_operator_coeFn Q b L (v+u) w,
    parent_boundary_raw_load_operator_coeFn Q b L v w,
    parent_boundary_raw_load_operator_coeFn Q b L u w,
    Lp.coeFn_add (parentBoundaryRawLoadOperator Q b L v w)
      (parentBoundaryRawLoadOperator Q b L u w)] with x ha hv hu hh
  simp only [Pi.add_apply] at hh
  rw [ha,hh,hv,hu]
  ext k
  change _*(v k+u k)=_*v k+_*u k
  ring

/-- The actual raw source retains physical scalar multiples of a load. -/
theorem parent_boundary_raw_load_smul (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (t : ℝ) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryRawLoadOperator Q b L (t • v) w =
      t • parentBoundaryRawLoadOperator Q b L v w := by
  apply Lp.ext
  filter_upwards [parent_boundary_raw_load_operator_coeFn Q b L (t • v) w,
    parent_boundary_raw_load_operator_coeFn Q b L v w,
    Lp.coeFn_smul t (parentBoundaryRawLoadOperator Q b L v w)] with x ht hv hh
  simp only [Pi.smul_apply] at hh
  rw [ht,hh,hv]
  ext k
  simp only [Pi.smul_apply,smul_eq_mul,PiLp.smul_apply]
  ring

/-- The actual projected load retains sums of load vectors. -/
theorem parent_boundary_dirichlet_load_add (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v u : Vec 2) (w : WhiteNoise) :
    parentBoundaryDirichletLoadOperator Q b L (v+u) w =
      parentBoundaryDirichletLoadOperator Q b L v w + parentBoundaryDirichletLoadOperator Q b L u w := by
  change lambda8DirichletProjection _ (parentBoundaryRawLoadOperator Q b L (v+u) w)=_
  rw [parent_boundary_raw_load_add]
  exact map_add (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet Q)).toSubmodule.starProjection _ _

/-- The actual projected load retains scalar multiples of load vectors. -/
theorem parent_boundary_dirichlet_load_smul (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (t : ℝ) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryDirichletLoadOperator Q b L (t • v) w =
      t • parentBoundaryDirichletLoadOperator Q b L v w := by
  change lambda8DirichletProjection _ (parentBoundaryRawLoadOperator Q b L (t • v) w)=_
  rw [parent_boundary_raw_load_smul]
  exact map_smul (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet Q)).toSubmodule.starProjection _ _

/-- Complete mixed Gram sums converge for the actual parent projection,
with no new norm-membership premise. -/
theorem parent_boundary_dirichlet_mixed_summable {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v u : Vec 2) :
    Summable (fun n => inner ℝ (parentBoundaryDirichletLoadOperator Q b L v (e n))
      (parentBoundaryDirichletLoadOperator Q b L u (e n))) :=
  (old_signed_series_pairing_budget
    (fun n => ‖parentBoundaryDirichletLoadOperator Q b L v (e n)‖)
    (fun n => ‖parentBoundaryDirichletLoadOperator Q b L u (e n)‖) _
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (parent_boundary_dirichlet_load_trace_summable e Q b L v)
    (parent_boundary_dirichlet_load_trace_summable e Q b L u)
    (fun _ => abs_real_inner_le_norm _ _)).1

/-- Exact complete quadratic expansion in the true projected load fields. -/
theorem parent_boundary_dirichlet_trace_add {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v u : Vec 2) :
    (∑' n, ‖parentBoundaryDirichletLoadOperator Q b L (v+u) (e n)‖^2) =
      (∑' n, ‖parentBoundaryDirichletLoadOperator Q b L v (e n)‖^2) +
      2*(∑' n, inner ℝ (parentBoundaryDirichletLoadOperator Q b L v (e n))
        (parentBoundaryDirichletLoadOperator Q b L u (e n))) +
      ∑' n, ‖parentBoundaryDirichletLoadOperator Q b L u (e n)‖^2 := by
  simp_rw [parent_boundary_dirichlet_load_add,norm_add_sq_real]
  rw [((parent_boundary_dirichlet_load_trace_summable e Q b L v).add
    ((parent_boundary_dirichlet_mixed_summable e Q b L v u).mul_left 2)).tsum_add
      (parent_boundary_dirichlet_load_trace_summable e Q b L u),
    (parent_boundary_dirichlet_load_trace_summable e Q b L v).tsum_add
      ((parent_boundary_dirichlet_mixed_summable e Q b L v u).mul_left 2),
    ←tsum_mul_left]

end
end ASDExplicitGamma.Native
