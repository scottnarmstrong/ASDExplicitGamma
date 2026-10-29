module

public import ASDExplicitGamma.Native.ParentBoundaryMinusKernel

/-! The literal complete full-minus covariance field, identified with the
existing signed full-flat contraction before centering. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- Actual full covariance with the source output quarter turn. -/
def parentBoundaryMinusFullCovariance (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (x : Vec 2) : Vec 2 :=
  planarQuarterTurn (fun k => parentBoundaryMinusCovarianceH1 Q b L (i,k) x)

/-- Every output coordinate has an honest H1 representative. -/
def parentBoundaryMinusFullCovarianceH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) : H1Function (openCubeSet Q) :=
  ∑ l : Fin 2,responsePlanarJ k l • parentBoundaryMinusCovarianceH1 Q b L (i,l)

/-- The representative is the actual physical quarter-turn contraction. -/
theorem parent_boundary_full_covariance_h1_toFun (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    (parentBoundaryMinusFullCovarianceH1 Q b L i k).toFun =
      fun x => parentBoundaryMinusFullCovariance Q b L i x k := by
  funext x
  fin_cases k <;> simp [parentBoundaryMinusFullCovarianceH1,
    parentBoundaryMinusFullCovariance,planarQuarterTurn,responsePlanarJ,Fin.sum_univ_two]

/-- Complete scalar covariance series recovers the actual full flat-minus
coordinate, on the same parent square and complete white realization. -/
theorem parent_boundary_minus_scalar_covariance_hasSum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,HasSum (fun n : whiteBasisIndex =>
      q3Convolution b L h3Zero (whiteBasis n) x*mainFlatMinusCoordinate Q b L n a x)
      (parentBoundaryMinusCovarianceH1 Q b L a x) := by
  have hc : ∀ᵐ x ∂normalizedCubeMeasure Q,∀ n : whiteBasisIndex,
      inner ℝ (whiteBasis n) ((parentBoundaryMinusKernel Q b L a).toFun x)=
        mainFlatMinusCoordinate Q b L n a x := by
    rw [ae_all_iff]
    exact parent_boundary_minus_kernel_coefficient Q b L a
  filter_upwards [hc] with x hx
  have hs := whiteBasis.hasSum_inner_mul_inner (q3Section b L h3Zero x)
    ((parentBoundaryMinusKernel Q b L a).toFun x)
  apply hs.congr_fun
  intro n
  rw [real_inner_comm (whiteBasis n),hx n]
  rfl

/-- Complete output-rotated covariance series on the actual parent. -/
theorem parent_boundary_minus_full_covariance_hasSum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,HasSum (fun n : whiteBasisIndex =>
      q3Convolution b L h3Zero (whiteBasis n) x *
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) k)
      (parentBoundaryMinusFullCovariance Q b L i x k) := by
  filter_upwards [parent_boundary_minus_scalar_covariance_hasSum Q b L (i,0),
    parent_boundary_minus_scalar_covariance_hasSum Q b L (i,1)] with x h0 h1
  fin_cases k
  · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,
      parentBoundaryMinusFullCovariance,planarQuarterTurn] using h1.neg
  · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,
      parentBoundaryMinusFullCovariance,planarQuarterTurn] using h0

/-- The actual whole-plane covariance has its complete signed constant
value pointwise, independently of any finite truncation. -/
theorem parent_boundary_whole_plane_covariance_hasSum (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) (x : Vec 2) :
    HasSum (fun n : whiteBasisIndex =>
      q3Convolution b L h3Zero (whiteBasis n) x *
        inner ℝ (whiteBasis n) (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i))
      (-(b^2/2)*(if k=i then 1 else 0)) := by
  have hp := old_signed_rotated_white_point_covariance b L (L.1⁻¹ • x) k i
  rw [smul_smul,mul_inv_cancel₀ L.2.ne',one_smul] at hp
  have hs := whiteBasis.hasSum_inner_mul_inner (q3Section b L h3Zero x)
    (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i)
  rw [hp] at hs
  apply hs.congr_fun
  intro n
  rw [real_inner_comm (whiteBasis n)]
  rfl

/-- The complete full-minus contraction is the SAME bulk plus harmonic
field used in AN, almost everywhere on the physical parent square. -/
theorem parent_boundary_full_covariance_eq_bulk_remainder (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    (fun x => parentBoundaryMinusFullCovariance Q b L i x k) =ᵐ[normalizedCubeMeasure Q]
      fun x => -(b^2/2)*(if k=i then 1 else 0)+oldSignedRemainderCovarianceField Q b L false i x k := by
  filter_upwards [parent_boundary_minus_full_covariance_hasSum Q b L i k,
    old_signed_remainder_vector_covariance_hasSum Q b L false i k] with x hf hr
  have hb := parent_boundary_whole_plane_covariance_hasSum b L i k x
  have hs := (hb.add hr).congr_fun (fun n => by
    exact (congrArg (fun z : ℝ => q3Convolution b L h3Zero (whiteBasis n) x*z)
      (old_signed_flat_output_decomposition Q b L false n i k x)).trans (by ring))
  exact hf.unique hs

end
end ASDExplicitGamma.Native
