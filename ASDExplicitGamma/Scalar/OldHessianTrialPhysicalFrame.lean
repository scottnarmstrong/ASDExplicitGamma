module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalLocal
public import ASDExplicitGamma.Inverse.ResponseCoefficients
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Main.InverseHessianSourceComponents
public import ASDExplicitGamma.Main.PartialInsertion
public import ASDExplicitGamma.Main.Q3HeatIdentity
public import ASDExplicitGamma.Response.Analytic

/-! The arbitrary physical parent uses cutoff m and true frame sigmaBar_m,
even when its geometric scale is m+129. These labels remain independent. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

local instance instOldHessianCompactCube (Q : TriadicCube 2) : CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The actual OLD coefficient on the open physical parent, with completed
cutoff m independent of the parent geometric scale n. -/
def oldHessianOldOpenCoefficient (n m : ℤ) (omega : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet (originCube 2 n)) :=
  pureFluxOpenResponseRestriction n
    (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m 0 omega)

/-- Zero partial insertion is exactly the original completed cutoff. -/
theorem old_hessian_partial_zero (M : ABKModel 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) (x : Vec 2) :
    Model.partialInsertedCoefficient M m 0 omega x=Cutoff.coefficientCutoff M.nu m omega x := by
  simp only [Model.partialInsertedCoefficient,RegCoeffField.add_apply,RegCoeffField.smul_apply,
    Real.sqrt_zero,zero_smul,add_zero]

/-- Literal pointwise equality of the open response scalar and actual
completed cutoff entry on the whole parent. -/
theorem old_hessian_old_open_coefficient_value (M : ABKModel 2) (n m : ℤ)
    (omega : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ openCubeSet (originCube 2 n)) :
    responseCoefficientExtension (oldHessianOldOpenCoefficient n m omega) x=
      Cutoff.coefficientCutoff M.nu m omega x 1 0 := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet (originCube 2 n)))
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  rw [oldHessianOldOpenCoefficient,pureFluxOpenResponseRestriction_value n _ hx]
  exact (modelInsertedScalar_apply _ M ell m hK 0 omega
    ⟨x,subset_closure (openCubeSet_subset_cubeSet _ hx)⟩).trans
      (congrArg (fun A : Mat 2 => A 1 0) (old_hessian_partial_zero M m omega x))

/-- The same completed scalar as a response coefficient on a closed-cell
carrier, for the proved fixed-frame coarse-matrix adapter. -/
def oldHessianOldClosedCoefficient (Q : TriadicCube 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) : ResponseCoefficient (cubeSet Q) :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => Cutoff.cutoff m omega x.val 1 0,
    (Cutoff.continuous_cutoff_entry m omega 1 0).comp continuous_subtype_val⟩

theorem old_hessian_old_closed_coefficient_value (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    responseCoefficientExtension (oldHessianOldClosedCoefficient Q m omega) x=
      Cutoff.coefficientCutoff M.nu m omega x 1 0 := by
  rw [responseCoefficientExtension_eq _ hx]
  change Cutoff.cutoff m omega x 1 0=_
  simp only [Cutoff.coefficientCutoff_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
    show (1:Fin 2)≠0 by decide,ite_false,smul_eq_mul,mul_zero,zero_add]

/-- Every actual descendant retains the true completed frame m, regardless
of the physical parent scale. This is the matrix interface for source rows. -/
theorem old_hessian_old_open_coarse_frame (M : ABKModel 2) (n m : ℤ)
    (omega : Cutoff.CutoffSample 2) (U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet (originCube 2 n)) :
    coarseBlockMatrix (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient n m omega)) =
      frameMatrix (Annealed.sigmaBar M m)
        (coarseBlockMatrix (cubeSet U) (Cutoff.coefficientCutoff M.nu m omega).toFun) := by
  let k := oldHessianOldOpenCoefficient n m omega
  let kU := oldHessianOldClosedCoefficient U m omega
  have hvalue {x : Vec 2} (hx : x ∈ openCubeSet U) :
      responseCoefficientExtension k x=responseCoefficientExtension kU x := by
    rw [old_hessian_old_open_coefficient_value M n m omega (hU hx),
      old_hessian_old_closed_coefficient_value M U m omega (openCubeSet_subset_cubeSet U hx)]
  have hframe : responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) kU := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
    change responsePlanarCoefficient (M.nu/(Annealed.sigmaBar M m))
      (responseCoefficientExtension k x/(Annealed.sigmaBar M m))=_
    rw [hvalue hx]
    rfl
  have hphys : responsePlanarCoefficientField M.nu kU =ᵐ[volumeMeasureOn (openCubeSet U)]
      (Cutoff.coefficientCutoff M.nu m omega).toFun := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
    change responsePlanarCoefficient M.nu (responseCoefficientExtension kU x)=_
    rw [old_hessian_old_closed_coefficient_value M U m omega (openCubeSet_subset_cubeSet U hx)]
    exact planar_coefficient_eq_of_symmPart M.nu _ (Cutoff.symmPart_coefficientCutoff M.nu m omega x)
  calc
    _ = coarseBlockMatrix (cubeSet U)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) kU) := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U]
      exact coarseBlockMatrix_congr_of_ae_eq hframe
    _ = frameMatrix (Annealed.sigmaBar M m)
        (coarseBlockMatrix (cubeSet U) (responsePlanarCoefficientField M.nu kU)) :=
      response_coarseMatrix_frame_eq (measurableSet_cubeSet U) M.nu (Annealed.sigmaBar M m)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1 kU
    _ = _ := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
        coarseBlockMatrix_congr_of_ae_eq hphys]

/-- The literal framed trace on each descendant is the original completed
OLD four-load trace, with no change of cutoff or frame. -/
theorem old_hessian_old_open_trace_eq (M : ABKModel 2) (n m : ℤ)
    (omega : Cutoff.CutoffSample 2) (U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet (originCube 2 n)) :
    traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient n m omega)) 1=rawCubeFourLoadTrace M m U 0 omega := by
  have he : (Model.partialInsertedCoefficient M m 0 omega).toFun=
      (Cutoff.coefficientCutoff M.nu m omega).toFun := by
    funext x
    exact old_hessian_partial_zero M m omega x
  unfold rawCubeFourLoadTrace traceDefect
  rw [he,old_hessian_old_open_coarse_frame M n m omega U hU]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

/-- The actual parent partition trace is exactly the common-tiling OLD
trace sequence consumed by the proved source and rare moment interfaces. -/
theorem old_hessian_old_open_trace_sequence (M : ABKModel 2) (n m : ℤ)
    (omega : Cutoff.CutoffSample 2) (depth : ℕ) :
    descendantsAverage (originCube 2 n) depth (fun U => traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient n m omega)) 1)=
      rawWeakTraceSequence M m (originCube 2 n) 0 omega depth := by
  change _=oldSignedCellAverage (originCube 2 n) depth (fun U => rawCubeFourLoadTrace M m U.val 0 omega)
  rw [old_signed_cell_average_eq_descendantsAverage (originCube 2 n) depth
    (fun U => rawCubeFourLoadTrace M m U 0 omega)]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  exact old_hessian_old_open_trace_eq M n m omega U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)

end
end ASDExplicitGamma.Scalar
