module

public import ASDExplicitGamma.Inverse.ClippedMatrixActualConcentration
public import ASDExplicitGamma.Inverse.RootMatrixLayerWeights
public import ASDExplicitGamma.Inverse.RootMatrixDeviation

/-! Actual centered layer fluctuations with the exact source Whitney mass. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- Real-order operator fluctuation estimate on the actual deterministic
layer. The literal source volume and fine-depth factors are retained. No
boundedness, matrix moment, or independence premise is supplied by the caller. -/
theorem root_centered_layer_Lp_depth (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (r : RootRow) (hk : ℕ × ℕ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (rootCenteredLayerMatrix M Q r hk ω)‖) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (128*rootResponseEnvelope (rootTau r)*Real.sqrt p*Real.sqrt (bankLayerWeight hk.2)*
        (1/3:ℝ)^(hk.2+1+whitneyProfile (rootH0 r+hk.1) (hk.2+1))*(3:ℝ)^40) := by
  let H := rootH0 r+hk.1
  let n := hk.2
  let d := n+1+whitneyProfile H (n+1)
  let j := Q.scale-(n+1:ℕ)-whitneyProfile H (n+1)
  let I := ↥(whitneyRootLayer Q H (n+1))
  let w : I → ℝ := fun U => (volume (cubeSet U.val)).toReal/(volume (cubeSet Q)).toReal
  have hs (U : I) : U.val.scale=j := root_whitney_layer_scale Q H (n+1) U.property
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hh := clipped_actual_cells_matrix_Lp M h hM j (rootTau r) ht
    (fun U : I => U.val) hs Subtype.val_injective w p hp
  have hlabel : rootLayerOldLabel Q (rootH0 r) hk=j+40 := by
    dsimp only [rootLayerOldLabel,resetDepth,j,H,n,whitneyProfile]
    push_cast
    ring
  have he (ω : Cutoff.CutoffSample 2) :
      (∑ U : I, w U • (clippedCellMatrix M (j+40) U.val (rootTau r) ω-
        ∫ ζ, clippedCellMatrix M (j+40) U.val (rootTau r) ζ ∂(Cutoff.cutoffSampleLaw M).toMeasure)) =
        rootCenteredLayerMatrix M Q r hk ω := by
    have hsum := Finset.sum_coe_sort (whitneyRootLayer Q H (n+1))
      (fun U : TriadicCube 2 => ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) •
        (clippedCellMatrix M (j+40) U (rootTau r) ω-
          ∫ ζ, clippedCellMatrix M (j+40) U (rootTau r) ζ ∂(Cutoff.cutoffSampleLaw M).toMeasure))
    apply hsum.trans
    simp only [rootCenteredLayerMatrix,hlabel,H,n]
  have hefun : (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (∑ U : I, w U • (clippedCellMatrix M (j+40) U.val (rootTau r) ω-
        ∫ ζ, clippedCellMatrix M (j+40) U.val (rootTau r) ζ ∂(Cutoff.cutoffSampleLaw M).toMeasure))‖) =
      fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (rootCenteredLayerMatrix M Q r hk ω)‖ :=
    funext (fun ω => congrArg (fun A : FullBlockMat 2 => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖) (he ω))
  dsimp only at hh
  rw [hefun] at hh
  have hw : (∑ U : I, (w U)^2)=bankLayerWeight n*(1/9:ℝ)^d := by
    exact (Finset.sum_coe_sort (whitneyRootLayer Q H (n+1))
      (fun U : TriadicCube 2 => ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2)).trans
        (root_matrix_layer_squared_weights Q H n)
  have hv : 0 ≤ bankLayerWeight n := bankLayerWeight_nonneg n
  have hroot : Real.sqrt ((1/9:ℝ)^d)=(1/3:ℝ)^d := by
    have hpw : (1/9:ℝ)^d=((1/3:ℝ)^d)^2 := by
      rw [← pow_mul,Nat.mul_comm d 2,pow_mul]
      norm_num
    rw [hpw,Real.sqrt_sq (by positivity)]
  apply hh.trans_eq
  congr 1
  rw [hw,Real.sqrt_mul hv,hroot]
  dsimp only [rootResponseEnvelope,n,H,d]
  ring

end
end ASDExplicitGamma.Inverse
