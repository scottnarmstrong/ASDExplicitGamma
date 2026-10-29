module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterPhysical
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandCoefficient

/-! One actual fresh-band center on an arbitrary translated source square. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

local instance parentCommonCubeCarrierCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

/-- The actual source-square center, in its common compact field carrier. -/
def parentBoundaryCommonCubeCenter (P : TriadicCube 2) : closure (cubeSet P) :=
  ⟨cubeCenter P,subset_closure (openCubeSet_subset_cubeSet P (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos P)))⟩

/-- The literal old-plus-fresh physical field on the common source square. -/
def parentBoundaryCommonCubeBand (P : TriadicCube 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : C(closure (cubeSet P),ℝ) :=
  olderField (closure (cubeSet P)) n ω +
    Real.sqrt t • modelBand (closure (cubeSet P)) (nativeSourceBandIndex n height) ω

/-- Center only the fresh band, once on P, before any descendant is observed. -/
def parentBoundaryCommonCubeCentered (P : TriadicCube 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : C(closure (cubeSet P),ℝ) :=
  olderField (closure (cubeSet P)) n ω + Real.sqrt t •
    centeringMap (parentBoundaryCommonCubeCenter P)
      (modelBand (closure (cubeSet P)) (nativeSourceBandIndex n height) ω)

/-- The one scalar center shared by every descendant and the whole history. -/
def parentBoundaryCommonCubeCenterValue (P : TriadicCube 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt t * modelBand (closure (cubeSet P)) (nativeSourceBandIndex n height) ω
    (parentBoundaryCommonCubeCenter P)

/-- Pathwise common-center restoration, including all correlations. -/
theorem parent_boundary_common_cube_split
    (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    parentBoundaryCommonCubeBand P n height t ω =
      parentBoundaryCommonCubeCentered P n height t ω +
        ContinuousMap.const _ (parentBoundaryCommonCubeCenterValue P n height t ω) := by
  ext x
  simp only [parentBoundaryCommonCubeBand,parentBoundaryCommonCubeCentered,
    parentBoundaryCommonCubeCenterValue,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    ContinuousMap.const_apply,centeringMap_apply,smul_eq_mul]
  ring

/-- The generic source-square field is the actual physical coefficient,
not a replacement law or a separately sampled descendant. -/
theorem parent_boundary_common_cube_band_apply
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : closure (cubeSet P)) :
    parentBoundaryCommonCubeBand P n height t ω x =
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω x 1 0 := by
  let K := closure (cubeSet P)
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K (isBounded_cubeSet P).isCompact_closure
  simp only [parentBoundaryCommonCubeBand,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    modelBand,ContinuousMap.sum_apply,smul_eq_mul]
  rw [olderField_apply_eq_coefficientCutoff K M ell n hK ω x,Finset.mul_sum]
  have hsum := native_source_band_index_sum n height
    (fun j => Real.sqrt t * shellFieldScalarRestriction K (ω.1 j) x)
  rw [hsum]
  simp only [attenuatedCoefficient,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rfl

/-- Literal centered coefficient on any actual descendant observation square. -/
def parentBoundaryCommonCubeObserved {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet Q) :=
  parentBoundaryCommonOpenCellCoefficient hQ (parentBoundaryCommonCubeCentered P n height t ω)

end
end ASDExplicitGamma.Native
