module

public import ASDExplicitGamma.Native.ParentBoundaryCommonShearYoung
public import ASDExplicitGamma.Native.ParentBoundaryBandResponse
public import ASDExplicitGamma.Inverse.FullResponseTrace

/-! Actual common-center full traces paid by the original physical response. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The closed-cell coefficient is the original simultaneous-band physical
field, including every old and fresh shell. -/
theorem parent_boundary_common_cell_physical_coarse
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu
      (parentBoundaryCellCoefficient hQ (parentBoundaryCommonCubeBand P n height t ω)))=
      coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) := by
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  change responsePlanarCoefficient M.nu (responseCoefficientExtension _ x)=_
  rw [parent_boundary_cell_coefficient_value hQ _ hx,parent_boundary_common_cube_band_apply M]
  exact native_source_planar_of_symm M.nu _ (native_source_band_attenuated_symm M n height t ω x)

/-- The actual centered full trace has the sharp Young split into its
uncentered full response and its one correlated center-square/inverse term.
This is a pointwise identity/estimate on the original cutoff sample space. -/
theorem parent_boundary_common_cube_full_young
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (eta : ℝ) (heta : 0 < eta) :
    let sigma : ℝ := Annealed.sigmaBar M n
    let a := attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω
    squareTrace Q M.nu sigma (parentBoundaryCommonCubeObserved hQ n height t ω)+4 ≤
      (1+eta)*nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω+
        (1+1/eta)*(parentBoundaryCommonCubeCenterValue P n height t ω/sigma)^2*
          Matrix.trace (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a)).lowerRight := by
  intro sigma a
  let f := parentBoundaryCommonCubeBand P n height t ω
  let fc := parentBoundaryCommonCubeCentered P n height t ω
  let g := parentBoundaryCommonCubeCenterValue P n height t ω
  let k := parentBoundaryCellCoefficient hQ f
  let kc := parentBoundaryCellCoefficient hQ fc
  have he : responsePlanarCoefficientField M.nu kc=ᵐ[volume.restrict (cubeSet Q)]
      (fun x => responsePlanarCoefficient M.nu (responseCoefficientExtension k x+(-g))) := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    change responsePlanarCoefficient M.nu (responseCoefficientExtension kc x)=_
    rw [parent_boundary_cell_coefficient_value hQ fc hx,parent_boundary_cell_coefficient_value hQ f hx]
    congr 1
    have hs := congrArg (fun z : C(closure (cubeSet P),ℝ) => z
      ⟨x,subset_closure (cubeSet_subset_of_mem_descendantsAtDepth hQ hx)⟩)
      (parent_boundary_common_cube_split P n height t ω)
    change f _=fc _+g at hs
    linarith only [hs]
  have hmat := coarseBlockMatrix_congr_of_ae_eq he
  have hb := parent_boundary_response_trace_shear_young Q M.nu sigma M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 k (-g) eta heta
  have hphysical := parent_boundary_common_cell_physical_coarse M hQ n height t ω
  change coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k)=coarseBlockMatrix (cubeSet Q) a at hphysical
  rw [parentBoundaryCommonCubeObserved,parent_boundary_common_cell_trace_eq hQ M.nu sigma M.nu_pos
    (Annealed.sigmaBar_characterization M n).1]
  change traceDefect (cubeSet Q) (responsePlanarCoefficientField M.nu kc) sigma+4 ≤ _
  unfold traceDefect at hb ⊢
  rw [hmat]
  rw [hphysical,neg_div,neg_sq] at hb
  have hfull : nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω=
      sigma⁻¹*Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft+
        sigma*Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
    have hf := traceDefect_eq_full_framedTrace (cubeSet Q) a sigma
    change _=Matrix.trace (toFullBlockMat (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a)))-4 at hf
    change Matrix.trace (toFullBlockMat (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a)))=_
    unfold traceDefect at hf
    linarith only [hf]
  rw [hfull]
  exact hb.trans_eq (by ring)

end
end ASDExplicitGamma.Native
