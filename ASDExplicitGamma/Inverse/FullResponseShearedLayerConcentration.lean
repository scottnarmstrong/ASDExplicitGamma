module

public import ASDExplicitGamma.Inverse.AssemblyShearedLayers

/-! The generic sheared-family estimate at the fixed full-response entrance. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section

/-- Applying the actual finite-family estimate to each fixed-entrance Whitney layer gives
the full-response sheared matrix error with no extra cell-count factor. -/
theorem full_response_sheared_centered_layer_Lp (A : ABKModel 2) (h : ℝ)
    (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (H i : ℕ) (hH : 377 ≤ H) (hi : 1 ≤ i)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (layerOldCutoff Q.scale H i) N,
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342 → nativeInductionState A h n) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (assemblyShearedCenteredLayerMatrix A Q H i τ N weights ω)‖)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal
        (256*(1+τ+Real.sqrt (τ*(τ+2)))*Real.sqrt p*
          Real.sqrt (bankLayerWeight (i-1))*(1/3:ℝ)^(layerDepth H i)*(3:ℝ)^40*
          (2+80*(p+2)*(A.gamma*((N-layerOldCutoff Q.scale H i:ℤ):ℝ)*
            (3:ℝ)^(2*A.gamma*((N-layerOldCutoff Q.scale H i:ℤ):ℝ))))) := by
  let j : ℤ := Q.scale-(layerDepth H i:ℤ)
  let I := ↥(whitneyRootLayer Q H i)
  let w : I → ℝ := fun U =>
    (volume (cubeSet U.val)).toReal/(volume (cubeSet Q)).toReal
  let a : I → ℝ := fun U => ((U.val.index 0:ℝ)-1/2)*(3:ℝ)^j
  let c : I → ℝ := fun U => ((U.val.index 1:ℝ)-1/2)*(3:ℝ)^j
  have hscale (U : I) : U.val.scale=j := by
    have hs := root_whitney_layer_scale Q H i U.property
    dsimp [j, layerDepth, layerProfile, whitneyProfile] at *
    omega
  have hlabel : layerOldCutoff Q.scale H i=j+40 := by
    unfold layerOldCutoff
    dsimp [j]
  have hcut : layerOldCutoff Q.scale H i ≤ Q.scale-342 := by
    have hH0 : heightEntrance 0 ≤ H := by simpa only [heightEntrance, mul_zero, add_zero] using hH
    have hh := layer_old_cutoff_le_protected Q.scale 0 H i hH0 hi
    simpa only [protectedOldLabel, Nat.cast_zero, mul_zero, sub_zero] using hh
  have hstate : nativeInductionState A h (j+40) := by
    rw [← hlabel]
    exact hpast _ hcut
  have hstrict : j+40<N := by
    rw [← hlabel]
    omega
  have hw' : ∀ k ∈ Finset.Ioc (j+40) N, 0 ≤ weights k ∧ weights k ≤ 1 := by
    intro k hk
    rw [← hlabel] at hk
    exact hw k hk
  have hh := assembly_source_sheared_family_Lp A h hA j N hstrict hstate τ hτ
    (fun U : I => U.val) hscale Subtype.val_injective a c weights hw' w p hp
  have he (ω : Cutoff.CutoffSample 2) :
      (∑ U : I, w U •
        ((assemblyPhysicalShearMatrix A (j+40) U.val.scale N (a U) (c U) weights ω).transpose *
          (clippedCellMatrix A (j+40) U.val τ ω-
            ∫ ζ, clippedCellMatrix A (j+40) U.val τ ζ
              ∂(Cutoff.cutoffSampleLaw A).toMeasure) *
          assemblyPhysicalShearMatrix A (j+40) U.val.scale N (a U) (c U) weights ω)) =
        assemblyShearedCenteredLayerMatrix A Q H i τ N weights ω := by
    have hsum := Finset.sum_coe_sort (whitneyRootLayer Q H i)
      (fun U : TriadicCube 2 =>
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) •
          ((assemblyPhysicalShearMatrix A (U.scale+40) U.scale N
              (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
              (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω).transpose *
            (clippedCellMatrix A (U.scale+40) U τ ω-
              ∫ ζ, clippedCellMatrix A (U.scale+40) U τ ζ
                ∂(Cutoff.cutoffSampleLaw A).toMeasure) *
            assemblyPhysicalShearMatrix A (U.scale+40) U.scale N
              (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
              (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω))
    calc
      _ = ∑ U : I,
          ((volume (cubeSet U.val)).toReal/(volume (cubeSet Q)).toReal) •
            ((assemblyPhysicalShearMatrix A (U.val.scale+40) U.val.scale N
                (((U.val.index 0:ℝ)-1/2)*(3:ℝ)^U.val.scale)
                (((U.val.index 1:ℝ)-1/2)*(3:ℝ)^U.val.scale) weights ω).transpose *
              (clippedCellMatrix A (U.val.scale+40) U.val τ ω-
                ∫ ζ, clippedCellMatrix A (U.val.scale+40) U.val τ ζ
                  ∂(Cutoff.cutoffSampleLaw A).toMeasure) *
              assemblyPhysicalShearMatrix A (U.val.scale+40) U.val.scale N
                (((U.val.index 0:ℝ)-1/2)*(3:ℝ)^U.val.scale)
                (((U.val.index 1:ℝ)-1/2)*(3:ℝ)^U.val.scale) weights ω) := by
        apply Finset.sum_congr rfl
        intro U hU
        dsimp [w, a, c]
        rw [hscale U]
      _ = assemblyShearedCenteredLayerMatrix A Q H i τ N weights ω := by
        simpa only [assemblyShearedCenteredLayerMatrix] using hsum
  have hefun :
      (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (∑ U : I, w U •
          ((assemblyPhysicalShearMatrix A (j+40) U.val.scale N (a U) (c U) weights ω).transpose *
            (clippedCellMatrix A (j+40) U.val τ ω-
              ∫ ζ, clippedCellMatrix A (j+40) U.val τ ζ
                ∂(Cutoff.cutoffSampleLaw A).toMeasure) *
            assemblyPhysicalShearMatrix A (j+40) U.val.scale N (a U) (c U) weights ω))‖) =
      fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (assemblyShearedCenteredLayerMatrix A Q H i τ N weights ω)‖ := by
    funext ω
    exact congrArg (fun B : FullBlockMat 2 =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) B‖) (he ω)
  dsimp only [] at hh
  rw [hefun] at hh
  have hweight : (∑ U : I, (w U)^2) =
      bankLayerWeight (i-1)*(1/9:ℝ)^(layerDepth H i) := by
    have hn : i-1+1=i := Nat.sub_add_cancel hi
    have hsum := root_matrix_layer_squared_weights Q H (i-1)
    have hsum' :
        (∑ U ∈ whitneyRootLayer Q H i,
          ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2) =
        bankLayerWeight (i-1)*(1/9:ℝ)^(i+whitneyProfile H i) := by
      simpa only [hn] using hsum
    have hcoe := Finset.sum_coe_sort (whitneyRootLayer Q H i)
      (fun U : TriadicCube 2 =>
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2)
    have hcoe' : (∑ U : I, (w U)^2) =
        ∑ U ∈ whitneyRootLayer Q H i,
          ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2 := by
      simpa only [I, w] using hcoe
    have hbase := hcoe'.trans hsum'
    have hd : i+whitneyProfile H i=layerDepth H i := by
      rw [layer_depth_eq_compatible_mesh]
      rfl
    rw [hd] at hbase
    exact hbase
  have hroot : Real.sqrt ((1/9:ℝ)^(layerDepth H i))=
      (1/3:ℝ)^(layerDepth H i) := by
    have hpw : (1/9:ℝ)^(layerDepth H i)=
        ((1/3:ℝ)^(layerDepth H i))^2 := by
      rw [← pow_mul, Nat.mul_comm (layerDepth H i) 2, pow_mul]
      norm_num
    rw [hpw, Real.sqrt_sq (by positivity)]
  apply hh.trans_eq
  congr 1
  rw [hweight, Real.sqrt_mul (bankLayerWeight_nonneg _), hroot]
  have hlabelCast : ((N-(j+40):ℤ):ℝ) =
      ((N-layerOldCutoff Q.scale H i:ℤ):ℝ) := by rw [hlabel]
  rw [hlabelCast]
  ring


end
end ASDExplicitGamma.Inverse
