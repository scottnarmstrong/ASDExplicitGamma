module

public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Response.CoefficientFamily
public import ASDExplicitGamma.Scalar.OldCutoffCoefficient

/-! The actual child shear moments from the state-driven local inverse profile. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal

local instance nativeHeatCubeClosureCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The actual OLD scalar skew coefficient restricted to a closed child cube. -/
noncomputable def nativeHeatOldResponseCoefficient (Q : TriadicCube 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (cubeSet Q) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Cutoff.cutoff m ω x.1 1 0,
      (Cutoff.continuous_cutoffValue_entry m ω 1 0).comp continuous_subtype_val⟩

/-- The response coefficient reconstructs the literal completed cutoff field
on the child cube. -/
theorem nativeHeat_oldResponseField_eq_cutoff
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    responsePlanarCoefficientField M.nu (nativeHeatOldResponseCoefficient Q m ω) =ᵐ[
      volume.restrict (cubeSet Q)] (Cutoff.coefficientCutoff M.nu m ω).toFun := by
  filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  have hscalar : responseCoefficientExtension
      (nativeHeatOldResponseCoefficient Q m ω) x = Cutoff.cutoff m ω x 1 0 := by
    rw [responseCoefficientExtension_eq _ hx]
    rfl
  change responsePlanarCoefficient M.nu
    (responseCoefficientExtension (nativeHeatOldResponseCoefficient Q m ω) x) = _
  rw [hscalar]
  exact Scalar.old_cutoff_coefficient_planar M.nu m ω x

/-- Equality of the actual child coarse matrices for the cutoff and its
bounded-continuous response presentation. -/
theorem nativeHeat_oldResponseCoarse_eq_cutoff
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField M.nu (nativeHeatOldResponseCoefficient Q m ω)) =
      coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun :=
  coarseBlockMatrix_congr_of_ae_eq (nativeHeat_oldResponseField_eq_cutoff M Q m ω)

end ASDExplicitGamma.Native
