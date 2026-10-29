module

public import ASDExplicitGamma.Inverse.BandCoefficient
public import ASDExplicitGamma.Triadic.SensitivityODEPath

/-! The exact old coefficient and actual later band as bounded continuous
sensitivity coefficients on the same physical closed cube. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open scoped Matrix.Norms.Elementwise
noncomputable section

local instance responseCubeCompact (Q : TriadicCube 2) : CompactSpace (closure (openCubeSet Q)) :=
  isCompact_iff_compactSpace.mp ((isBounded_cubeSet Q).subset (openCubeSet_subset_cubeSet Q)).isCompact_closure

/-- The actual old scalar skew entry on the physical closed cube. -/
def oldResponseCoefficient (Q : TriadicCube 2) (n : ℤ) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet Q) :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => Cutoff.cutoff n ω x.val 1 0,
    (Cutoff.continuous_cutoff_entry n ω 1 0).comp continuous_subtype_val⟩

/-- The actual later scalar band on exactly the same closed cube. -/
def laterResponseCoefficient (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet Q) :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => laterScalarBand n J weights ω x.val,
    (later_scalar_band_contDiff n J weights ω).continuous.comp continuous_subtype_val⟩

/-- Off-cube Tietze choices do not change the actual old field on the cube. -/
theorem old_response_coefficient_extension (Q : TriadicCube 2) (n : ℤ) (ω : Cutoff.CutoffSample 2)
    {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (oldResponseCoefficient Q n ω) x=Cutoff.cutoff n ω x 1 0 := by
  rw [responseCoefficientExtension_eq _ hx]
  rfl

/-- The later coefficient and the Sobolev direction are the same actual
function on the cube, rather than separately chosen representatives. -/
theorem later_response_coefficient_represents (Q : TriadicCube 2) (n J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    responseCoefficientExtension (laterResponseCoefficient Q n J weights ω) =ᵐ[
      volume.restrict (openCubeSet Q)] (laterBandW2 Q n J weights ω).value.toFun := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  rw [responseCoefficientExtension_eq _ hx]
  rfl

/-- Scalar reconstruction of any planar coefficient with the source symmetric part. -/
theorem planar_coefficient_eq_of_symmPart (ν : ℝ) (A : Mat 2)
    (hA : symmPart A=ν • (1:Mat 2)) : responsePlanarCoefficient ν (A 1 0)=A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  norm_num [symmPart,Matrix.smul_apply,Matrix.one_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [responsePlanarCoefficient,responsePlanarJ] <;> linarith

/-- The initial sensitivity coefficient is the literal completed cutoff on
the entire physical root, in the true molecular coefficient nu I+k. -/
theorem old_response_coefficient_represents (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    sensitivityBaseRegField M.nu (oldResponseCoefficient Q n ω) x=Cutoff.coefficientCutoff M.nu n ω x := by
  have he : Cutoff.coefficientCutoff M.nu n ω x 1 0=Cutoff.cutoff n ω x 1 0 := by
    simp only [Cutoff.coefficientCutoff_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
      show (1:Fin 2)≠0 by decide,ite_false,smul_eq_mul,mul_zero,zero_add]
  change responsePlanarCoefficient (M.nu/1)
    (responseCoefficientExtension (oldResponseCoefficient Q n ω) x/1)=_
  rw [div_one,div_one,old_response_coefficient_extension Q n ω hx,← he]
  exact planar_coefficient_eq_of_symmPart M.nu _ (Cutoff.symmPart_coefficientCutoff M.nu n ω x)

end
end ASDExplicitGamma.Inverse
