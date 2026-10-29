module

public import ASDExplicitGamma.Native.OldSignedPatchMeans

/-! The exact depth projection is unchanged when subtracting the actual
child affine patch instead of its prescribed affine first component. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Linearity of the normalized scalar mean for actual square-integrable fields. -/
theorem old_signed_cube_average_sub (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x-g x)=cubeAverage Q f-cubeAverage Q g := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))

/-- The actual patch and its affine datum have identical depth projections.
The other field is arbitrary L², so this also applies to reciprocal fields. -/
theorem old_signed_patch_projection_eq (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (S : Vec 2 → BlockVec 2) (hS : MemBlockL2 (openCubeSet Q) S) (i : Fin 2) :
    cubeProjection Q depth (fun x => (S x).1 i-
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x).1 i)=
    cubeProjection Q depth (fun x => (S x).1 i-P.1 i) := by
  let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
  let D : Vec 2 → BlockVec 2 := fun x => S x-L x
  have hL := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
  have hScoord (i : Fin 2) : MemLp (fun x => (S x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hS) i)
  have hLcoordParent (i : Fin 2) : MemLp (fun x => (L x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hL) i)
  have hPcoord (i : Fin 2) : MemLp (fun _ : Vec 2 => P.1 i) 2
      (normalizedCubeMeasure Q) := memLp_const (P.1 i)
  have hSPcoord (i : Fin 2) : MemLp (fun x => (S x).1 i - P.1 i) 2
      (normalizedCubeMeasure Q) := (hScoord i).sub (hPcoord i)
  have hPLcoord (i : Fin 2) : MemLp (fun x => P.1 i - (L x).1 i) 2
      (normalizedCubeMeasure Q) := (hPcoord i).sub (hLcoordParent i)
  have hLocalMean (i : Fin 2) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q depth) :
      cubeAverage R (fun x => (L x).1 i) = P.1 i :=
    old_signed_patch_first_mean Q depth nu sigma hnu hsigma k P R hR i
  have hPLproj (i : Fin 2) :
      cubeProjection Q depth (fun x => P.1 i - (L x).1 i) = 0 := by
    funext x
    by_cases hx : x ∈ cubeSet Q
    · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet depth hx
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
      have hLR : MemBlockL2 (openCubeSet R) L := by
        exact hL.mono_measure (Measure.restrict_mono_set volume
          (openCubeSet_subset_of_mem_descendantsAtDepth hR))
      have hLcoord (i : Fin 2) : MemLp (fun y => (L y).1 i) 2
          (normalizedCubeMeasure R) :=
        memLp_normalized_of_memL2On
          (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hLR) i)
      have hconst : MemLp (fun _ : Vec 2 => P.1 i) 2
          (normalizedCubeMeasure R) := memLp_const (P.1 i)
      calc
        cubeAverage R (fun y => P.1 i - (L y).1 i) =
            cubeAverage R (fun _ => P.1 i) - cubeAverage R (fun y => (L y).1 i) :=
          old_signed_cube_average_sub R hconst (hLcoord i)
        _ = 0 := by rw [cubeAverage_const, hLocalMean i R hR, sub_self]
    · exact cubeProjection_eq_zero_of_not_mem_cubeSet Q depth _ hx
  have hProjAdd (i : Fin 2) :
      cubeProjection Q depth (fun x => (D x).1 i) =
        fun x => cubeProjection Q depth (fun y => (S y).1 i - P.1 i) x := by
    have hdecomp : (fun x => (D x).1 i) =
        (fun x => (S x).1 i - P.1 i) + (fun x => P.1 i - (L x).1 i) := by
      funext x
      simp only [D]
      change (S x).1 i - (L x).1 i =
        ((S x).1 i - P.1 i) + (P.1 i - (L x).1 i)
      ring
    calc
      cubeProjection Q depth (fun x => (D x).1 i) =
          cubeProjection Q depth
            ((fun x => (S x).1 i - P.1 i) + (fun x => P.1 i - (L x).1 i)) := by
              rw [hdecomp]
      _ = cubeProjection Q depth (fun x => (S x).1 i - P.1 i) +
            cubeProjection Q depth (fun x => P.1 i - (L x).1 i) :=
              projection_add Q depth (hSPcoord i) (hPLcoord i)
      _ = fun x => cubeProjection Q depth (fun y => (S y).1 i - P.1 i) x := by
            rw [hPLproj i]
            simp
  exact hProjAdd i

end
end ASDExplicitGamma.Native
