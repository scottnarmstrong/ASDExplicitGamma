module

public import ASDExplicitGamma.Scalar.RefCheckVstar

/-! Reference check (i): at the zero old stream, `δ_j = (σ/ν² - σ)·(0, F(H_j))`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace Cfg''

variable (C : Cfg'')

theorem Cload (hQ : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d) (j : ℕ) :
      pureFluxBlockOperator 0 (C.Vm (C.Hs j)) C.load =
      inr'' (Y := C.Ys) (X := C.Xs) (C.σ⁻¹ • C.Fl (C.Hs j)) := by
  have hV := ref_Vstar C.Q C.hab C.hcd hQ C.hQcl C.σ C.hσ C.e (C.Hs j)
  apply WithLp.ofLp_injective 2
  have hVm : C.Vm (C.Hs j) = physicalProjectedInsertion C.Q C.σ C.hσ (C.Rest (C.Hs j)) :=
    C.Vm_apply (C.Hs j)
  have hV' : (physicalProjectedInsertion C.Q C.σ C.hσ (C.Rest (C.Hs j))).adjoint
      (physicalConstantLoad C.Q C.e) = (-C.σ⁻¹) • C.Fl (C.Hs j) := hV
  rw [pureFluxBlockOperator_apply, hVm, inr_apply']
  simp only [Cfg''.load, pureFluxLoad, WithLp.ofLp_toLp]
  refine Prod.ext ?_ ?_
  · simp
  · simp [hV']
    module

end Cfg''

end

end ASDExplicitGamma.Scalar
