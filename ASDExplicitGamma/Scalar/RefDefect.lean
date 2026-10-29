module

public import ASDExplicitGamma.Scalar.DefectFinalPhys
public import ASDExplicitGamma.Scalar.PairLamSplit
public import ASDExplicitGamma.Scalar.RefLoad

/-! Successor defect data with the corrected flat reference (single change: `Fl ↦ FlR`). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

namespace Cfg''

variable (C : Cfg'')

/-- The corrected flat-reference carrier `σ⁻² F`: with the unchanged reference coefficient `σ` of
`delta'`, `σ • FlR H = σ⁻¹ • F H` is the exact flat first response of the σ̄-frame. -/
def FlR : C(closedRectangle C.a C.b C.c C.d, ℝ) →L[ℝ] C.Xs := ((C.σ ^ 2)⁻¹ : ℝ) • C.Fl

/-- The first-response defect of mode `j`. -/
def deltaR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Pr :=
  delta' C.Vm C.FlR (C.Bop old) (C.U old) C.σ (C.Hs j)

def dxR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Xs :=
  (C.deltaR old j).ofLp.2

def dyR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Ys :=
  (C.deltaR old j).ofLp.1

/-- The closed-graph potential of the `X`-component of the defect of mode `j`. -/
def zpotR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    H10GraphClosedSpace (openCubeSet C.Q) :=
  potMap C.Q (C.dxR old j : HilbertVectorL2 (openCubeSet C.Q))

theorem dyR_mem_flux (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    C.dyR old j ∈ (physicalFluxSpace C.Q).toSubmodule := by
  unfold dyR deltaR
  refine delta_fst_mem _ C.Vm C.FlR C.hα (C.Aold old) (C.U old) C.σ
    (physicalFluxSpace C.Q).toSubmodule (fun x => ?_) (fun H x => ?_) (C.Hs j)
  · exact vmap_mem_flux C.Q C.σ C.hσ _ x
  · exact vmap_mem_flux C.Q C.σ C.hσ _ x


theorem fslot_term_genR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (i j : ℕ)
    (o : Option whiteBasisIndex) (hio : eOpt i = o)
    (hF : MemVectorL2 (openCubeSet C.Q) (fun p => -((rowEltOpt C.Q 134 C.amp C.L o
      (rep'' C.nQ (C.zpotR old j))).1 p))) :
    C.Vm (C.Hs i) (C.dxR old j) = fluxSource C.Q hF :=
  C.fslot_gen i o hio (C.dxR old j) hF

theorem gslot_term_genR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (i j : ℕ)
    (o : Option whiteBasisIndex) (hio : eOpt i = o)
    (hG : MemVectorL2 (openCubeSet C.Q)
      (gSlotOpt C.nQ 134 C.amp C.L o (rep2 C.nQ 134 (C.dyR old j))).1) :
    -(ContinuousLinearMap.adjoint (C.Vm (C.Hs i))) (C.dyR old j) = potSource C.Q hG :=
  C.gslot_gen i o hio (C.dyR old j) (C.dyR_mem_flux old j) hG

end Cfg''

end

end ASDExplicitGamma.Scalar
