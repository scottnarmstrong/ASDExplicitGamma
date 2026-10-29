module

public import ASDExplicitGamma.Triadic.DiagLattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Module

/-! Rational Laurent stencils for DIAG's exact nodal Fourier multipliers.
Adjoints reverse the lag. All coefficient identities are kernel checked. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- Finite rational Laurent symbols on the two source grid coordinates. -/
abbrev DiagStencil := AddMonoidAlgebra ℚ (ℤ × ℤ)

/-- A single lattice translation. -/
def diagStencilAtom (g : ℤ × ℤ) : DiagStencil := AddMonoidAlgebra.single g 1

/-- Reversing the stencil lag is the adjoint for normalized counting measure. -/
def diagStencilAdjoint : DiagStencil →ₐ[ℚ] DiagStencil :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (-(AddMonoidHom.id (ℤ × ℤ)))

@[simp] theorem diagStencilAdjoint_atom (g : ℤ × ℤ) :
    diagStencilAdjoint (diagStencilAtom g) = diagStencilAtom (-g) := by
  simp [diagStencilAdjoint, diagStencilAtom]

theorem diagStencilAtom_inverse (g : ℤ × ℤ) :
    diagStencilAtom (-g) * diagStencilAtom g = 1 := by
  rw [diagStencilAtom, diagStencilAtom, AddMonoidAlgebra.single_mul_single, neg_add_cancel, one_mul]
  rfl

/-- Neighbor averaging and its orthogonal difference partner. -/
def diagStencilAverage (g : ℤ × ℤ) : DiagStencil := (1 / 2 : ℚ) • (1 + diagStencilAtom g)

def diagStencilDifference (g : ℤ × ℤ) : DiagStencil := (1 / 2 : ℚ) • (1 - diagStencilAtom g)

/-- The squared averaging multiplier U=cos²(theta/2). -/
def diagStencilU (g : ℤ × ℤ) : DiagStencil :=
  diagStencilAdjoint (diagStencilAverage g) * diagStencilAverage g

theorem diagStencil_complement (g : ℤ × ℤ) :
    1 - diagStencilU g =
      diagStencilAdjoint (diagStencilDifference g) * diagStencilDifference g := by
  unfold diagStencilU diagStencilAverage diagStencilDifference
  simp only [map_smul, map_add, map_sub, map_one, diagStencilAdjoint_atom,
    smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub,
    one_mul, mul_one, diagStencilAtom_inverse]
  module

/-- Translation representation of the integer lags on any finite grid. -/
def diagTranslationHom {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) : Multiplicative (ℤ × ℤ) →* Module.End ℚ (G → ℝ) where
  toFun g :=
    { toFun := fun f x => f (x + φ (Multiplicative.toAdd g))
      map_add' := by intro f h; rfl
      map_smul' := by intro c f; rfl }
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [map_add, add_assoc]

/-- Apply the exact Laurent multiplier as an operator on cell arrays. -/
def diagStencilAction {G : Type*} [AddCommGroup G] (φ : (ℤ × ℤ) →+ G) :
    DiagStencil →ₐ[ℚ] Module.End ℚ (G → ℝ) :=
  AddMonoidAlgebra.lift ℚ (Module.End ℚ (G → ℝ)) (ℤ × ℤ) (diagTranslationHom φ)

theorem diagStencilAction_single {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g : ℤ × ℤ) (c : ℚ) (f : G → ℝ) (x : G) :
    diagStencilAction φ (AddMonoidAlgebra.single g c) f x = c • f (x + φ g) := by
  rw [diagStencilAction, AddMonoidAlgebra.lift_single]
  rfl

@[simp] theorem diagStencilAction_atom {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g : ℤ × ℤ) (f : G → ℝ) (x : G) :
    diagStencilAction φ (diagStencilAtom g) f x = f (x + φ g) := by
  rw [diagStencilAtom, diagStencilAction_single, one_smul]

end

end ASDExplicitGamma.Triadic
