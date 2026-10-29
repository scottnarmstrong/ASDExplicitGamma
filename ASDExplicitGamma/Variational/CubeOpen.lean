module

public import ASDExplicitGamma.Variational.CubeBoundary
public import Homogenization.CoarseGraining.OriginCubeOpenBridge

/-! VA-OPEN-CUBE-ADAPTER: reuse the established domain transport, not just equality
of volumes. The Mu and response admissibility spaces are transported by the upstream bridge. -/
@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization

theorem zero_dim_cube_eq_open (Q : TriadicCube 0) : cubeSet Q = openCubeSet Q := by
  ext x
  simp [cubeSet,openCubeSet]

/-- Exact Mu equality, with the same origin and scale, including dimension zero. -/
theorem cube_Mu_eq_open {d : ℕ} (Q : TriadicCube d) (P : BlockVec d) (a : CoeffField d) :
    Mu (cubeSet Q) P a = Mu (openCubeSet Q) P a := by
  by_cases hd : d = 0
  · subst d
    rw [zero_dim_cube_eq_open]
  · have instNeZeroCubeDimension : NeZero d := ⟨hd⟩
    exact Mu_cubeSet_eq_openCubeSet_of_triadicCube Q P a

/-- The corresponding canonical coarse matrices agree, without changing any parameter. -/
theorem cube_coarseMatrix_eq_open {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) :
    coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a :=
  coarseBlockMatrix_eq_of_mu_eq (fun P => cube_Mu_eq_open Q P a)

/-- Response equality uses the actual transported harmonic test space. -/
theorem cube_response_eq_open {d : ℕ} (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q a := by
  by_cases hd : d = 0
  · subst d
    rw [zero_dim_cube_eq_open]
  · have instNeZeroCubeDimension : NeZero d := ⟨hd⟩
    exact responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a

end ASDExplicitGamma.Variational
