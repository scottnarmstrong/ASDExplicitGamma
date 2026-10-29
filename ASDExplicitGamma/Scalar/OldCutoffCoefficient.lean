module

public import ASDExplicitGamma.Scalar.DualityStep
public import Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import Algsuperdiff.Section3.Cutoff.Limit

/-! The literal OLD cutoff skew coefficient on a square, in its actual running frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response
open Algsuperdiff.Section3

/-- Every actual planar skew matrix is its (1,0) entry times the fixed quarter turn. -/
theorem planar_skew_eq_scalar_quarter_turn (A : Mat 2) (hA : A.transpose= -A) :
    A=A 1 0 • responsePlanarJ := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  simp only [Matrix.transpose_apply,Matrix.neg_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,responsePlanarJ] <;> linarith

/-- The actual OLD skew stream, restricted to the compact closure of the observation square. -/
noncomputable def oldCutoffSkewCoefficient (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet Q) := by
  letI compactOldCutoffSquare : CompactSpace (closure (openCubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Cutoff.cutoff n ω x.1 1 0,(Cutoff.continuous_cutoffValue_entry n ω 1 0).comp continuous_subtype_val⟩

/-- The coefficient extension agrees with the literal OLD stream everywhere on the observation square. -/
theorem old_cutoff_skew_coefficient_value (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2)
    {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (oldCutoffSkewCoefficient n Q ω) x=Cutoff.cutoff n ω x 1 0 := by
  rw [responseCoefficientExtension_eq _ hx]
  rfl

/-- The genuine cutoff coefficient is exactly nu I plus this literal scalar skew stream. -/
theorem old_cutoff_coefficient_planar (ν : ℝ) (n : ℤ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    responsePlanarCoefficient ν (Cutoff.cutoff n ω x 1 0)=Cutoff.coefficientCutoff ν n ω x := by
  conv_rhs => rw [Cutoff.coefficientCutoff_apply,planar_skew_eq_scalar_quarter_turn _ (Cutoff.cutoff_skew n ω x)]
  rfl

end ASDExplicitGamma.Scalar
