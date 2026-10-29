module

public import ASDExplicitGamma.Native.OldSignedMixedPartition
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound
public import ASDExplicitGamma.Native.ParentBoundaryJointMixed
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy
public import ASDExplicitGamma.Native.OldSignedFlatPatchedData

/-! Complete spatial assembly of the two mixed remainders, retaining
their unprojected physical flat pairings for the covariance terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- The complete actual A-R or Z-R remainder has the exact averaged
joint local bill; no local estimate or convergence is assumed. -/
theorem parent_boundary_global_joint_mixed (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let F := fun plus n i => oldSignedFlatInput Q b L plus n i
    let H := fun plus n i => parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)
    let f := fun plus n => ∑ i : Fin 2,
      (oldSignedEnergyPairing Q nu sigma k
        (oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L plus n i)
        (parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))-
        volumeAverage (openCubeSet Q) (fun x => vecDot (F plus n i x).2 (H plus n i x).2))
    Summable (fun n => f true n-f false n) ∧ |∑' n,(f true n-f false n)|≤descendantsAverage Q depth (fun U =>
      parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L*
      (Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true+
          oldSignedFlatDirectionalMeanProxy Q U a b L false)+
        Real.sqrt ((oldSignedInverseHistory U a+1)^2*oldSignedFlatOscillationSize Q U b L true^2+
          oldSignedInverseHistory U a*oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2))) := by
  intro Q a F H f
  let fc := fun (plus : Bool) (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : Fin 2,
      (oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U.val U.property)
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (H plus n i)
          (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)))-
        volumeAverage (openCubeSet U.val) (fun x => vecDot (F plus n i x).2 (H plus n i x).2))
  have he (plus : Bool) : f plus=(fun n => oldSignedCellAverage Q depth (fc plus n)) := by
    funext n
    exact old_signed_mixed_pairing_load_partition Q depth nu sigma hnu hsigma k (F plus n) (H plus n)
      (old_signed_flat_input_memL2 Q b L plus n)
      (fun i => parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))
  have hj : (fun n => f true n-f false n)=
      (fun n => oldSignedCellAverage Q depth (fun U => fc true n U-fc false n U)) := by
    simp only [he,old_signed_cell_average_sub]
  rw [hj,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth (fun n U => fc true n U-fc false n U) _
    (fun U => (parent_boundary_joint_mixed_feedback m depth nu sigma hnu hsigma k b L U.val U.property).1)
    (fun U => by
      have hh := (parent_boundary_joint_mixed_feedback m depth nu sigma hnu hsigma k b L U.val U.property).2
      have he (plus : Bool) := old_signed_flat_directional_proxy_cell_eq Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k b L plus
      dsimp only [oldSignedFlatDirectionalMeanProxy] at he
      dsimp only at hh
      rw [he true,he false] at hh
      exact hh)

end
end ASDExplicitGamma.Native
