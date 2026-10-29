module

public import ASDExplicitGamma.Inverse.StoppedPhysicalBlocks
public import ASDExplicitGamma.Gaussian.WaveGateEnlargedFailure
public import Homogenization.Geometry.TriadicPartition
public import Mathlib.Data.Fintype.EquivFin

/-! The actual fine parents and their two descendant generations in each block. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian
noncomputable section

/-- The corner and buffer-volume index of an elementary parent. -/
abbrev BufferedParentIndex := Fin 4 × (Fin (3^40) × Fin (3^40))

/-- Literal two-by-two buffer blocks on the centered fine triadic lattice. -/
def bufferedParent (j : ℤ) (x : BlockSite) (i : BufferedParentIndex) : TriadicCube 2 where
  scale := j
  index := fun d => 2*(3^40:ℤ)*x d+(3^40:ℤ)*
    (if d=0 then (i.1.val%2:ℤ) else (i.1.val/2:ℤ))+
    (if d=0 then (i.2.1.val:ℤ) else (i.2.2.val:ℤ))

/-- The three exact generations, of respective populations 1,9,81. -/
abbrev GenerationIndex := Fin 1 ⊕ (Fin 9 ⊕ Fin 81)

def generationDepth : GenerationIndex → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- The generation index really enumerates all 9^depth descendants. -/
def generationRank (i : GenerationIndex) : Fin (9^generationDepth i) :=
  match i with
  | .inl a => a
  | .inr (.inl a) => a
  | .inr (.inr a) => a

/-- A deterministic bijection with the genuine triadic descendant population. -/
def descendantEnumeration (Q : TriadicCube 2) (r : ℕ) :
    {R // R ∈ descendantsAtDepth Q r} ≃ Fin (9^r) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe,descendantsAtDepth_card]
    norm_num)

/-- The actual descendant corresponding to an elementary source index. -/
def elementaryCube (j : ℤ) (x : BlockSite) (i : WavePlanarElementaryIndex) : TriadicCube 2 :=
  ((descendantEnumeration (bufferedParent j x (i.1,i.2.1))
    (generationDepth i.2.2)).symm (generationRank i.2.2)).val

theorem elementary_cube_mem (j : ℤ) (x : BlockSite) (i : WavePlanarElementaryIndex) :
    elementaryCube j x i ∈ descendantsAtDepth (bufferedParent j x (i.1,i.2.1))
      (generationDepth i.2.2) :=
  ((descendantEnumeration (bufferedParent j x (i.1,i.2.1))
    (generationDepth i.2.2)).symm (generationRank i.2.2)).property

theorem elementary_cube_scale (j : ℤ) (x : BlockSite) (i : WavePlanarElementaryIndex) :
    (elementaryCube j x i).scale = j-generationDepth i.2.2 :=
  scale_eq_sub_of_mem_descendantsAtDepth (elementary_cube_mem j x i)

/-- In particular all elementary old cutoffs and fresh shells are below the
parent's buffered old cutoff and corresponding fresh shell. -/
theorem elementary_cube_scale_le (j : ℤ) (x : BlockSite) (i : WavePlanarElementaryIndex) :
    (elementaryCube j x i).scale ≤ j := by
  rw [elementary_cube_scale]
  omega

end
end ASDExplicitGamma.Inverse
