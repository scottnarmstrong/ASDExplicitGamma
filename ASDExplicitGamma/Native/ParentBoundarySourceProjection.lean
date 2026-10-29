module

public import ASDExplicitGamma.Native.ParentBoundarySourceMembership
public import ASDExplicitGamma.Native.OldSignedPureSecondSharp
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedCellPotentials

/-! Actual sharp weighted projection and derivative-feedback potential
bounds for the whole-parent source on independent fine cells. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The genuine zero-cell-boundary first potential of the projected parent
source, selected from its proved weighted variation. -/
def parentBoundaryCellSourcePotential (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (P : BlockVec 2) : H10Function (openCubeSet U) :=
  oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
    (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P)
    (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P)

/-- Its gradient is the entire first block of the actual source residual;
the parent source has identically zero first block. -/
theorem parent_boundary_cell_source_potential_grad (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (P : BlockVec 2) :
    (parentBoundaryCellSourcePotential Q U hU nu sigma hnu hsigma k b L n P).toH1Function.grad =
      fun x => (oldSignedCellResidual Q U hU nu sigma hnu hsigma k
        (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P)
        (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P) x).1 := by
  rw [parentBoundaryCellSourcePotential,old_signed_cell_first_corrector_grad]
  funext x
  exact sub_zero _

/-- Both physical pure-source projection bounds, on actual cells and
actual canonical parent minimizers, with every membership discharged. -/
theorem parent_boundary_actual_source_sharp (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P
    let R := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F
      (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P)
    let v := parentBoundaryCellSourcePotential Q U hsub nu sigma hnu hsigma k b L n P
    oldSignedEnergyPairing U nu sigma kU R R ≤
      oldSignedInverseHistory U a*vectorPositiveHaarNorm U (fun x => (F x).2)^2 ∧
    vectorWeakHaarNorm U v.toH1Function.grad ≤
      (1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        vectorPositiveHaarNorm U (fun x => (F x).2) := by
  intro hsub a kU F R v
  let g := fun x => (F x).2
  have hF : MemBlockL2 (openCubeSet U) (fun x => (0,g x)) :=
    (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P).mono_measure
      (Measure.restrict_mono_set volume hsub)
  have hp := parent_boundary_actual_source_positive Q U depth hU nu sigma hnu hsigma k P b L n
  have he := old_signed_pure_second_sharp_energy U nu sigma hnu hsigma kU g hF hp
  have hv : (fun x => (scalarResidualField U nu sigma hnu hsigma kU
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet U)] v.toH1Function.grad := by
    exact Filter.Eventually.of_forall (fun x =>
      (congrFun (parent_boundary_cell_source_potential_grad Q U hsub nu sigma hnu hsigma k b L n P) x).symm)
  have hf := old_signed_pure_second_sharp_first U nu sigma hnu hsigma kU g hF hp v hv
  have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
  dsimp only at he
  rw [hs.1] at he hf
  exact ⟨he,hf⟩

end
end ASDExplicitGamma.Native
