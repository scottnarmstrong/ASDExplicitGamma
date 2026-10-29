module

public import ASDExplicitGamma.Native.ParentBoundaryCommonResponseDirections
public import ASDExplicitGamma.Native.ParentBoundaryCommonSquareBracket
public import ASDExplicitGamma.Gaussian.Q3Directions

/-! Exact full white-noise covariance of actual common-center descendant directions. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic
open scoped RealInnerProductSpace
noncomputable section

/-- Every actual weak jet retains the same original source center. -/
theorem parent_boundary_common_q3_direction_jet
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (o : Q3SpatialJet) (x : Vec 2) :
    q3DirectionJet (parentBoundaryCommonQ3Direction P Q b L u) o x =
      q3Convolution b L (supMeanKernelJetIndex o) u x -
        (if o=.value then q3Convolution b L h3Zero u (cubeCenter P) else 0) := by
  cases o with
  | value => exact parent_boundary_common_q3_direction_value P Q b L u x
  | first i =>
    have hidx : mainQ3JetIndex (.first i)=supMeanKernelJetIndex (.first i) := by
      fin_cases i <;> rfl
    simp only [q3DirectionJet,reduceCtorEq,ite_false,sub_zero]
    rw [←hidx]
    exact parent_boundary_common_q3_direction_grad P Q b L u x i
  | second i j =>
    simp only [reduceCtorEq,ite_false,sub_zero]
    change q3DirectionJet (mainQ3DirectionW2 Q b L u) (.second i j) x = _
    rw [mainQ3DirectionW2_jet]
    rfl

/-- The full physical white-noise section for a common-center jet. -/
def parentBoundaryCommonJetKernel (b : ℝ) (L : {l : ℝ // 0 < l})
    (z : Vec 2) (o : Q3SpatialJet) (x : Vec 2) : WhiteNoise :=
  q3Section b L (supMeanKernelJetIndex o) x -
    (if o=.value then q3Section b L h3Zero z else 0)

private theorem parent_common_kernel_value_index : supMeanKernelJetIndex Q3SpatialJet.value=h3Zero := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

/-- Every cross-point and cross-jet covariance is the literal common-center
remainder kernel, including observation points outside the source center. -/
theorem parent_boundary_common_jet_kernel_covariance
    (b : ℝ) (L : {l : ℝ // 0 < l}) (z : Vec 2)
    (o p : Q3SpatialJet) (x y : Vec 2) :
    ⟪parentBoundaryCommonJetKernel b L z o x,parentBoundaryCommonJetKernel b L z p y⟫ =
      q3RemainderJetCovariance (b^2) L.val z o p x y := by
  cases o <;> cases p <;>
    (simp [parentBoundaryCommonJetKernel,q3RemainderJetCovariance,inner_sub_left,inner_sub_right] <;>
      simp only [←parent_common_kernel_value_index,←real_inner_self_eq_norm_sq,
        supMean_kernel_jet_covariance,q3ScaledJetCovariance_value_diagonal] <;> ring)

/-- The actual common-center descendant directions represent the COMPLETE
white-noise remainder law. No covariance estimate or representation is assumed. -/
theorem parent_boundary_common_q3_directions_represent
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    RepresentsQ3Remainder
      (fun n => parentBoundaryCommonQ3Direction P Q b L (gaussEnumerated whiteBasis n))
      (b^2) L.val (cubeCenter P) := by
  intro o p x y
  let X := parentBoundaryCommonJetKernel b L (cubeCenter P) o x
  let Y := parentBoundaryCommonJetKernel b L (cubeCenter P) p y
  let f : WhiteNoise → ℝ := fun u => ⟪X,u⟫*⟪u,Y⟫
  have hf : f 0=0 := by simp [f]
  have hs := whiteBasis.summable_inner_mul_inner X Y
  have ht := whiteBasis.tsum_inner_mul_inner X Y
  have hse := enumerated_summable_apply whiteBasis f hf hs
  have hte := enumerated_tsum_apply whiteBasis f hf
  have hjet (u : WhiteNoise) (o : Q3SpatialJet) (x : Vec 2) :
      q3DirectionJet (parentBoundaryCommonQ3Direction P Q b L u) o x =
        ⟪u,parentBoundaryCommonJetKernel b L (cubeCenter P) o x⟫ := by
    rw [parent_boundary_common_q3_direction_jet]
    by_cases ho : o=.value <;>
      simp [parentBoundaryCommonJetKernel,q3Convolution,ho,inner_sub_right]
  have hterm (n : ℕ) :
      q3DirectionJet (parentBoundaryCommonQ3Direction P Q b L (gaussEnumerated whiteBasis n)) o x *
        q3DirectionJet (parentBoundaryCommonQ3Direction P Q b L (gaussEnumerated whiteBasis n)) p y =
        f (gaussEnumerated whiteBasis n) := by
    rw [hjet,hjet]
    exact congrArg (fun a : ℝ => a*⟪gaussEnumerated whiteBasis n,Y⟫)
      (real_inner_comm (gaussEnumerated whiteBasis n) X).symm
  refine ⟨hse.congr (fun n => (hterm n).symm),?_⟩
  calc
    _ = ∑' n,f (gaussEnumerated whiteBasis n) := tsum_congr hterm
    _ = ∑' l,f (whiteBasis l) := hte
    _ = ⟪X,Y⟫ := ht
    _ = _ := parent_boundary_common_jet_kernel_covariance b L (cubeCenter P) o p x y

/-- Exact true-frame link for every index of the actual global direction family. -/
theorem parent_boundary_common_response_direction_frame_all
    (P Q : TriadicCube 2) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (n : ℕ) :
    (parentBoundaryCommonQ3Direction P Q (b/σ) L (gaussEnumerated whiteBasis n)).value.toFun =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseCoefficientExtension
        (parentBoundaryCommonResponseDirections P Q b L n) x / σ := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  rw [parent_boundary_common_response_direction_value P Q b L n hx,
    parent_boundary_common_q3_direction_value,q3_convolution_div_frame,q3_convolution_div_frame]
  ring

/-- Complete physical common-center bracket on every observation cube, with
all representation and frame links discharged and the exact parent radius. -/
theorem parent_boundary_common_response_trace_bracket
    (P Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P) (j : ℕ)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet Q)) :
    let κ := Real.sqrt ((b/σ)^2)*lemmaVH2Bn (cubeScaleFactor P/L.val) (diagMeshRadius Q j/L.val)
    Summable (fun n => (fderiv ℝ (squareTrace Q ν σ) k
      (parentBoundaryCommonResponseDirections P Q b L n))^2) ∧
    (∑' n,(fderiv ℝ (squareTrace Q ν σ) k (parentBoundaryCommonResponseDirections P Q b L n))^2) ≤
      4*κ^2*(lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k))^2*
        squareTrace Q ν σ k*(squareTrace Q ν σ k+4) := by
  exact (parent_boundary_common_square_trace_bracket Q j ν σ hν hσ k
    (parentBoundaryCommonResponseDirections P Q b L)
    (fun n => parentBoundaryCommonQ3Direction P Q (b/σ) L (gaussEnumerated whiteBasis n))
    ((b/σ)^2) L.val (cubeScaleFactor P) (cubeCenter P)
    (parent_boundary_common_q3_directions_represent P Q (b/σ) L)
    (sq_nonneg _) L.property (Homogenization.cubeScaleFactor_pos' P).le
    (fun x hx => planar_cube_center_distance_sq P (hQP hx))
    (fun n => parent_boundary_common_response_direction_frame_all P Q b σ L n)).2

end
end ASDExplicitGamma.Native
