module

public import ASDExplicitGamma.Scalar.DefectFinalPhys
public import ASDExplicitGamma.Scalar.SmoothFeedbackNode

/-! The forced (flat-load) part of the first-response defect and the statement `T4 INTERFACE`
that the F_w identification must deliver. `δ_j = B_old C_{H_j} u₀ − σ(0, F H_j)` splits exactly
(by linearity) as `forced_j + B_old C_{H_j}(u₀ − load)`, with `forced_j := delta' … load …`
(the defect with `u₀` replaced by the flat load `(e,0)`). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open scoped InnerProductSpace BigOperators

noncomputable section

namespace Cfg''

variable (C : Cfg'')

/-- The forced part `B_old C_{H_j} (e,0) − σ(0, F H_j)` of the defect of mode `j`. -/
def forced (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Pr :=
  delta' C.Vm C.Fl (C.Bop old) C.load C.σ (C.Hs j)

/-- The tiled depth-134 weak energies of the two components of the forced parts, `j < n`. -/
def forcedLam (n : ℕ) (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : ℝ :=
  ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
      (rep'' C.nQ (potMap C.Q ((C.forced old j).ofLp.2 : HilbertVectorL2
        (openCubeSet C.Q)))).toH1Function.grad +
    ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.forced old j).ofLp.1).1

/-- The inner part `B_old C_{H_j}(u₀ − (e,0))`. -/
def inner (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Pr :=
  C.Bop old (pureFluxBlockOperator 0 (C.Vm (C.Hs j)) (C.U old - C.load))

end Cfg''

end

end ASDExplicitGamma.Scalar
