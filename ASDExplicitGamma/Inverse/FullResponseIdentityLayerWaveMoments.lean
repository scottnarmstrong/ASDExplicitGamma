module

public import ASDExplicitGamma.Inverse.FullResponseShearMeanMoments
public import ASDExplicitGamma.Inverse.FullResponseShearedLayerMean
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! The identity wave keeps the exact layer fraction in every ordinary moment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

noncomputable section

/-- The complete weighted family of identity-cell shear means has the source
ordinary wave moment with the exact factor vₖ. Correlations among the cells
are retained by the finite Lp triangle inequality. -/
theorem full_response_identity_layer_wave_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (H : ℕ) (hH : 377 ≤ H)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (k : ℕ) (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    let old := layerOldCutoff Q.scale H (k+1)
    let F := assemblyLayerMeanSquare M Q H (k+1) N (sourceBandWeights (Q.scale-342) weights)
    Measurable F ∧ eLpNorm F (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (bankLayerWeight k*20*(p+2)*
        (M.gamma*(N-old:ℝ)*(3:ℝ)^(2*M.gamma*(N-old:ℝ)))) := by
  classical
  dsimp only
  let old := layerOldCutoff Q.scale H (k+1)
  let I := ↥(whitneyRootLayer Q H (k+1))
  let a := sourceBandWeights (Q.scale-342) weights
  let w := fun U : I => (volume (cubeSet U.val)).toReal/(volume (cubeSet Q)).toReal
  let Y := fun U : I => fun ω : Cutoff.CutoffSample 2 =>
    (physicalMissingWaveAverage M old U.val.scale N
      (((U.val.index 0:ℝ)-1/2)*(3:ℝ)^U.val.scale)
      (((U.val.index 1:ℝ)-1/2)*(3:ℝ)^U.val.scale) a ω/(Annealed.sigmaBar M old : ℝ))^2
  let B := 20*(p+2)*(M.gamma*(N-old:ℝ)*(3:ℝ)^(2*M.gamma*(N-old:ℝ)))
  have hH0 : heightEntrance 0 ≤ H := by
    simpa only [heightEntrance, mul_zero, add_zero] using hH
  have hold : old ≤ Q.scale-342 := by
    simpa only [old, protectedOldLabel, Nat.cast_zero, mul_zero, sub_zero] using
      layer_old_cutoff_le_protected Q.scale 0 H (k+1) hH0 (by omega)
  have hstrict : old < N := by omega
  have hw0 (U : I) : 0 ≤ w U := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hY (U : I) : Measurable (Y U) :=
    (physical_shear_mean_measurable M old U.val.scale N _ _ a).pow_const 2
  have hB : 0 ≤ B := by
    have hgap : (0:ℝ) ≤ (N-old:ℝ) := by exact_mod_cast sub_nonneg.mpr hstrict.le
    have hγ := M.shellPrefix.gamma_pos.le
    dsimp only [B]
    positivity
  have hb (U : I) : eLpNorm (Y U) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal B :=
    physical_shear_mean_square_Lp M h hM old U.val.scale N hstrict (hpast old hold)
      _ _ a (source_band_weights_bounds old (Q.scale-342) N weights hw) p hp
  have hfun : assemblyLayerMeanSquare M Q H (k+1) N a =
      fun ω => ∑ U : I, w U*Y U ω := by
    funext ω
    have hsum := Finset.sum_coe_sort (whitneyRootLayer Q H (k+1))
      (fun U : TriadicCube 2 => ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
        (physicalMissingWaveAverage M (U.scale+40) U.scale N
          (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
          (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) a ω/(Annealed.sigmaBar M (U.scale+40) : ℝ))^2)
    dsimp only [assemblyLayerMeanSquare]
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro U hU
    have hl := root_whitney_old_cutoff_eq Q H (k+1) U.property
    dsimp only [w, Y]
    rw [show U.val.scale+40=old from hl.symm]
  rw [hfun]
  refine ⟨Finset.measurable_sum _ (fun U _ => (hY U).const_mul (w U)), ?_⟩
  have hs := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp) Y w (fun _ => B) hw0 (fun _ => hB) hb
  apply hs.trans_eq
  congr 1
  rw [← Finset.sum_mul]
  have hwSum : (∑ U : I, w U) = bankLayerWeight k := by
    have hc := Finset.sum_coe_sort (whitneyRootLayer Q H (k+1))
      (fun U : TriadicCube 2 => (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)
    exact hc.trans (root_matrix_layer_weights_sum Q H k)
  rw [hwSum]
  dsimp only [B]
  ring

end
end ASDExplicitGamma.Inverse
