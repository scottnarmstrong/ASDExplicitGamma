module

public import ASDExplicitGamma.Native.ParentBoundaryLoadOperator
public import ASDExplicitGamma.Native.ParentBoundaryTraceBasis

/-! Genuine complete trace summability for every physical parent load and
every complete white basis. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

local instance parentBoundaryTraceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The physical scalar load has its literal convolution representative. -/
theorem parent_boundary_scalar_load_coeFn (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (w : WhiteNoise) :
    hilbertKernel (volume.restrict (openCubeSet Q))
      (q3SpatialKernel (openCubeSet Q) b L h3Zero) w
      =ᵐ[volume.restrict (openCubeSet Q)] q3Convolution b L h3Zero w := by
  filter_upwards [hilbertKernel_ae (volume.restrict (openCubeSet Q))
    (q3SpatialKernel (openCubeSet Q) b L h3Zero) w,
    (q3Section_memLp (openCubeSet Q) b L h3Zero).coeFn_toLp] with x ht hk
  exact ht.trans (congrArg (inner ℝ w) hk)

/-- Exact norm of the physical vector load, with its load-vector factor. -/
theorem parent_boundary_raw_load_norm_sq (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    ‖parentBoundaryRawLoadOperator Q b L v w‖^2 =
      vecDot v v * ‖hilbertKernel (volume.restrict (openCubeSet Q))
        (q3SpatialKernel (openCubeSet Q) b L h3Zero) w‖^2 := by
  rw [l2_norm_sq,l2_norm_sq,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [parent_boundary_raw_load_operator_coeFn Q b L v w,
    parent_boundary_scalar_load_coeFn Q b L w] with x hx ht
  rw [hx,ht,HilbertVec.norm_sq_ofVec,Real.norm_eq_abs,sq_abs]
  simp only [vecDot,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  ring

/-- Genuine complete summability of the raw physical vector loads, for
any complete white basis rather than a specially symmetric truncation. -/
theorem parent_boundary_raw_load_trace_summable {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) :
    Summable (fun n => ‖parentBoundaryRawLoadOperator Q b L v (e n)‖^2) := by
  have hs := (hilbertKernel_summable (volume.restrict (openCubeSet Q))
    (q3SpatialKernel (openCubeSet Q) b L h3Zero) e e.orthonormal).mul_left (vecDot v v)
  simpa only [parent_boundary_raw_load_norm_sq] using hs

/-- Contracting by the ACTUAL parent Dirichlet projection preserves
complete square summability, without any source norm bound as a premise. -/
theorem parent_boundary_dirichlet_load_trace_summable {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) :
    Summable (fun n => ‖parentBoundaryDirichletLoadOperator Q b L v (e n)‖^2) := by
  apply (parent_boundary_raw_load_trace_summable e Q b L v).of_nonneg_of_le
    (fun _ => sq_nonneg _)
  intro n
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  exact (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet Q)).toSubmodule.norm_starProjection_apply_le _

/-- Basis independence now holds for the actual complete projected q3
load, with both convergence statements discharged internally. -/
theorem parent_boundary_dirichlet_load_trace_basis {I J : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (e' : HilbertBasis J ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) (v : Vec 2) :
    (∑' n, ‖parentBoundaryDirichletLoadOperator Q b L v (e n)‖^2) =
      ∑' n, ‖parentBoundaryDirichletLoadOperator Q b L v (e' n)‖^2 :=
  parent_boundary_operator_sq_trace_basis _ e e'
    (parent_boundary_dirichlet_load_trace_summable e Q b L v)
    (parent_boundary_dirichlet_load_trace_summable e' Q b L v)

end
end ASDExplicitGamma.Native
