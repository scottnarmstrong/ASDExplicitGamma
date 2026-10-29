module

public import ASDExplicitGamma.Native.OldSignedCellCrossPairing
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedSelectedSourceBudget
public import ASDExplicitGamma.Native.OldSignedMixedPairing

/-! Actual local A-R and Z-R cross terms retain their literal flat
pairing before covariance contraction and use joint weak/positive duality. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual weighted flat/OLD-source pairing has exactly the flat
part and the local reciprocal-error remainder of AN (6.1). -/
theorem old_signed_actual_mixed_pairing (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := oldSignedFlatInput Q b L plus n i
    let H := oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)
    let Z := oldSignedFlatCellResidual Q mesh nu sigma hnu hsigma k b L plus n i U hU
    let R := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k H
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))
    |oldSignedEnergyPairing U nu sigma kU Z R-
      volumeAverage (openCubeSet U) (fun x => vecDot (F x).2 (H x).2)|≤
      vectorWeakHaarNorm U (fun x =>
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (Z x)).2-(F x).2)*
      vectorPositiveHaarNorm U (fun x => (H x).2) := by
  intro Q hsub kU F H Z R
  have hF := old_signed_flat_input_cell_memL2 Q mesh b L plus n i U hU
  have hHparent := old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)
  have hH : MemBlockL2 (openCubeSet U) (fun x => (0,(H x).2)) :=
    hHparent.mono_measure (Measure.restrict_mono_set volume hsub)
  have he : oldSignedEnergyPairing U nu sigma kU Z R=
      oldSignedEnergyPairing U nu sigma kU Z (fun x => (0,(H x).2)) :=
    old_signed_residual_cross_pairing U nu sigma hnu hsigma kU F _ hF hH
  rw [he]
  have hZ : MemBlockL2 (openCubeSet U) Z :=
    Lp.memLp (scalarResidualField U nu sigma hnu hsigma kU (toHilbertBlockL2OfBlockField hF))
  have hp := old_signed_old_error_source_positive m mesh
    (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) (oldSignedFlatLoad plus i) b L U hU n
  exact old_signed_mixed_pairing_remainder_bound U nu sigma hnu hsigma kU
    hZ hF (memVectorL2_snd_of_memBlockL2 hH) hp

end
end ASDExplicitGamma.Native
