module

public import ASDExplicitGamma.Scalar.DefectModes
public import ASDExplicitGamma.Scalar.DefectVmap
public import ASDExplicitGamma.Scalar.DefectPairFlux
public import ASDExplicitGamma.Scalar.DefectPairCont
public import ASDExplicitGamma.Scalar.DefectModePotential
public import ASDExplicitGamma.Scalar.GSlotWick

/-! The physical pair-space data of the defect source at a fixed OLD coefficient: modes,
first-response defects, potentials. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped InnerProductSpace BigOperators

noncomputable section

/-- Fixed typing data of the defect source. -/
structure Cfg'' where
  nQ : ℤ
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  hab : a < b
  hcd : c < d
  hQcl : closure (openCubeSet (originCube 2 nQ)) ⊆ closedRectangle a b c d
  β : ℝ
  σ : ℝ
  hσ : 0 < σ
  ν : ℝ
  hν : 0 < ν
  L : {l : ℝ // 0 < l}
  e : Vec 2

namespace Cfg''

variable (C : Cfg'')

abbrev Q : TriadicCube 2 := originCube 2 C.nQ

abbrev K : Set (Vec 2) := closedRectangle C.a C.b C.c C.d

abbrev Xs := (physicalPotentialSpace C.Q).toSubmodule

abbrev Ys := HilbertVectorL2 (openCubeSet C.Q)

abbrev Pr := physicalParityHilbert C.Q

/-- The multiplier amplitude `β / σ`. -/
def amp : ℝ := C.β / C.σ

def α : ℝ := C.ν / C.σ

theorem hα : 0 < C.α := div_pos C.hν C.hσ

def Rest : C(closedRectangle C.a C.b C.c C.d, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet C.Q) :=
  physicalResponseRestriction C.Q C.hQcl

def Vm : C(closedRectangle C.a C.b C.c C.d, ℝ) →L[ℝ] (C.Xs →L[ℝ] C.Ys) :=
  (vmap' C.Q C.σ C.hσ).comp C.Rest

def Fl : C(closedRectangle C.a C.b C.c C.d, ℝ) →L[ℝ] C.Xs :=
  flCLM C.Q C.hab C.hcd C.e

theorem Vm_apply (H : C(closedRectangle C.a C.b C.c C.d, ℝ)) :
    C.Vm H = physicalProjectedInsertion C.Q C.σ C.hσ (C.Rest H) := by
  unfold Vm
  rw [ContinuousLinearMap.comp_apply, vmap_apply]
  rfl

/-- The OLD projected coefficient. -/
def Aold (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Xs →L[ℝ] C.Ys :=
  physicalProjectedCoefficient C.Q C.σ C.hσ (C.Rest old)

def Bop (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Pr →L[ℝ] C.Pr :=
  pureFluxBlockInverse C.α C.hα (C.Aold old)

def load : C.Pr :=
  pureFluxLoad (Y := C.Ys) (X := C.Xs) (physicalConstantLoad C.Q C.e)

def U (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Pr := C.Bop old C.load

/-- The `j`-th Gaussian shell mode as a coefficient field on the source rectangle. -/
def Hs (j : ℕ) : C(closedRectangle C.a C.b C.c C.d, ℝ) :=
  q3H3RangeValue C.a C.b C.c C.d C.β C.L
    (q3H3Directions C.a C.b C.c C.d C.β C.L whiteBasis j)

end Cfg''

theorem potMap_gradient (Q : TriadicCube 2) (x : (physicalPotentialSpace Q).toSubmodule) :
    H10GraphClosed.gradientCLM (potMap Q (x : HilbertVectorL2 (openCubeSet Q))) =
      (x : HilbertVectorL2 (openCubeSet Q)) := by
  obtain ⟨r0, hr0⟩ := x.2
  have h1 : H10GraphClosed.gradientCLM (zOfH10 (openCubeSet Q) r0) =
      (x : HilbertVectorL2 (openCubeSet Q)) := hr0
  rw [← h1, potMap_spec]

theorem rowEltOpt_memL2 (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (o : Option whiteBasisIndex) (r : H10Function (openCubeSet (originCube 2 nQ))) :
    MemVectorL2 (openCubeSet (originCube 2 nQ)) (rowEltOpt (originCube 2 nQ) m b L o r).1 := by
  cases o with
  | none => exact memVectorL2_const (U := openCubeSet (originCube 2 nQ)) 0
  | some l => exact rowElt_memL2 nQ m b L l r

theorem gslotOpt_memL2 (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (o : Option whiteBasisIndex) (g : TiledL2Field (originCube 2 nQ) m) :
    MemVectorL2 (openCubeSet (originCube 2 nQ)) (gSlotOpt nQ m b L o g).1 := by
  cases o with
  | none => exact memVectorL2_const (U := openCubeSet (originCube 2 nQ)) 0
  | some l => exact gSlot_memL2 nQ m b L l g

end

end ASDExplicitGamma.Scalar
