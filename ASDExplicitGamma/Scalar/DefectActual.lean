module

public import ASDExplicitGamma.Scalar.DefectSnId
public import ASDExplicitGamma.Scalar.DefectFinal2
public import ASDExplicitGamma.Scalar.DefectNewBank
public import ASDExplicitGamma.Scalar.PairedTwoSlotBank
public import ASDExplicitGamma.Scalar.FlatResolventSourceBridge
public import ASDExplicitGamma.Scalar.FlatResolventModes

/-! The actual physical defect diagonal `⟪J s_def, N s_def⟫` of the literal NEW resolvent and its
Wick truncations, with the pathwise two-slot bound. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open scoped InnerProductSpace BigOperators

noncomputable section

/-- The typing data of the model's defect source: true `sigmaBar` frame, molecular `ν`, shell
amplitude and length of the fresh shell `m+1`. -/
def Cfg''.ofModel (nQ : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQcl : closure (openCubeSet (originCube 2 nQ)) ⊆ closedRectangle a b c d)
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (e : Vec 2) : Cfg'' where
  nQ := nQ
  a := a
  b := b
  c := c
  d := d
  hab := hab
  hcd := hcd
  hQcl := hQcl
  β := q3ModelAmplitude M h (m + 1)
  σ := (Annealed.sigmaBar M m : ℝ)
  hσ := (Annealed.sigmaBar M m).property
  ν := M.nu
  hν := M.nu_pos
  L := q3ModelLength (m + 1)
  e := e

theorem tiled_vec_admissible (Q : TriadicCube 2) (m : ℕ) (F : TiledHaarField Q m) :
    ∀ U ∈ descendantsAtDepth Q m,
      MemLp F.1 2 (normalizedCubeMeasure U) ∧ ∀ i : Fin 2, Summable (fun j : ℕ =>
        (Real.sqrt 3) ^ (j + 1) * energy U (cubeIncrement U (j + 1) (fun y => F.1 y i))) :=
  fun _ hU => ⟨MemLp.of_eval fun i => (F.2 _ hU i).1, fun i => (F.2 _ hU i).2⟩

namespace Cfg''

variable (C : Cfg'') (m : ℤ)

/-- The OLD field restricted to the source rectangle. -/
def old (ω : Cutoff.CutoffSample 2) : C(closedRectangle C.a C.b C.c C.d, ℝ) :=
  olderField C.K m ω

/-- The actual fresh shell on the source rectangle. -/
def z0 (ω : Cutoff.CutoffSample 2) : C(closedRectangle C.a C.b C.c C.d, ℝ) :=
  shellFieldScalarRestriction C.K (ω.1 (m + 1))

/-- The literal NEW inverse. -/
def Nop (ω : Cutoff.CutoffSample 2) : C.Pr →L[ℝ] C.Pr :=
  pureFluxBlockInverse C.α C.hα (C.Aold (C.old m ω) + C.Vm (C.z0 m ω))

def Jop : C.Pr →L[ℝ] C.Pr := pureFluxParity (Y := C.Ys) (X := C.Xs)

theorem Nop_eq_old_add (ω : Cutoff.CutoffSample 2) :
    C.Nop m ω = pureFluxBlockInverse C.α C.hα
      (physicalProjectedCoefficient C.Q C.σ C.hσ (C.Rest (C.old m ω + C.z0 m ω))) := by
  rw [map_add, physicalProjectedCoefficient_add]
  unfold Nop
  rw [Vm_apply]
  rfl

theorem Nop_eq (ω : Cutoff.CutoffSample 2) :
    C.Nop m ω = pureFluxBlockInverse C.α C.hα
      (physicalProjectedCoefficient C.Q C.σ C.hσ (C.Rest (modelInsertedScalar C.K m 1 ω))) := by
  have hnew : modelInsertedScalar C.K m 1 ω = C.old m ω + C.z0 m ω := by
    ext x
    simp [modelInsertedScalar, old, z0]
  rw [hnew, map_add, physicalProjectedCoefficient_add]
  unfold Nop
  rw [Vm_apply]
  rfl

end Cfg''

end

end ASDExplicitGamma.Scalar
