module

public import ASDExplicitGamma.Native.OldSignedPureSecondSharp
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedOldErrorPotentialSeries

/-! Actual localized OLD-error sources supply both sharp pure-source
projection budgets with no regularity or potential premise. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Both sharp bounds for the actual localized OLD source and its actual
constructed first potential, in the same old medium on the DIAG cell. -/
theorem old_signed_actual_old_source_sharp (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P
    let R := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P)
    let v := oldSignedCellErrorPotential Q U hsub mesh nu sigma hnu hsigma k b L n P
    oldSignedEnergyPairing U nu sigma kU R R ≤
        oldSignedInverseHistory U a*vectorPositiveHaarNorm U (fun x => (F x).2)^2 ∧
    vectorWeakHaarNorm U v.toH1Function.grad ≤
      (1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        vectorPositiveHaarNorm U (fun x => (F x).2) := by
  intro Q hsub a kU F R v
  let g := fun x => (F x).2
  have hFparent := old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P
  have hF : MemBlockL2 (openCubeSet U) (fun x => (0,g x)) :=
    hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  have hp : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => g x i))) :=
    old_signed_old_error_source_positive m mesh a
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        nu sigma hnu hsigma k) P b L U hU n
  have he := old_signed_pure_second_sharp_energy U nu sigma hnu hsigma kU g hF hp
  have hv : (fun x => (scalarResidualField U nu sigma hnu hsigma kU
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet U)] v.toH1Function.grad := by
    have hgrad := old_signed_cell_error_potential_grad Q U hsub mesh nu sigma hnu hsigma k b L n P
    exact Filter.Eventually.of_forall (fun x => (congrFun hgrad x).symm)
  have hf := old_signed_pure_second_sharp_first U nu sigma hnu hsigma kU g hF hp v hv
  have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
  dsimp only at he
  rw [hs.1] at he hf
  exact ⟨he,hf⟩

end
end ASDExplicitGamma.Native
