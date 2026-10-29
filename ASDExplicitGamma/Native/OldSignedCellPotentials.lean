module

public import ASDExplicitGamma.Native.OldSignedCellProjection

/-! Actual zero-trace first-potential corrections of the cellwise weighted
minimizers. These give the potentials used in every derivative-only feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Response
noncomputable section

/-- The actual cell residual differs from its input in the first block by
the gradient of a genuine H10 potential, with the physical sign retained. -/
theorem old_signed_cell_first_corrector_exists (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    ∃ phi : H10Function (openCubeSet U),phi.toH1Function.grad=
      fun x => (oldSignedCellResidual Q U hU nu sigma hnu hsigma k F hF x).1-(F x).1 := by
  have hv := old_signed_cell_removed_variation Q U hU nu sigma hnu hsigma k F hF
  obtain ⟨phi,hphi⟩ := hv.2.1
  refine ⟨-phi,?_⟩
  change (-phi.toH1Function).grad=_
  rw [H1Function.neg_grad,hphi]
  funext x j
  simp only [Pi.neg_apply,Prod.fst_sub,Pi.sub_apply]
  ring

/-- Select the actual cell first-corrector potential from the proved
zero-trace variation, rather than asking for a potential witness. -/
def oldSignedCellFirstCorrector (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) : H10Function (openCubeSet U) :=
  (old_signed_cell_first_corrector_exists Q U hU nu sigma hnu hsigma k F hF).choose

/-- The chosen genuine potential has exactly the actual first correction. -/
theorem old_signed_cell_first_corrector_grad (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    (oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k F hF).toH1Function.grad=
      fun x => (oldSignedCellResidual Q U hU nu sigma hnu hsigma k F hF x).1-(F x).1 :=
  (old_signed_cell_first_corrector_exists Q U hU nu sigma hnu hsigma k F hF).choose_spec

end
end ASDExplicitGamma.Native
