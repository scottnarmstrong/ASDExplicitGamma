/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirResetProfileMeasurable
public import ASDExplicitGamma.AllOrder.CirResetHistoryBridge

/-! # Reset integrability for actual CIR tile histories -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Variational
open Homogenization.Book
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

private theorem aoCir_reset_tile_depth_measurable
    (M : ABKModel 2) (Q U : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (t : ℝ) (j d : ℕ)
    (hU : U ∈ descendantsAtDepth Q j) :
    Measurable (fun ω => lemmaVInverseDepthMax U
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N t ω)) d) := by
  classical
  let S := descendantsAtDepth U d
  have hS : S.Nonempty := descendantsAtDepth_nonempty U d
  have hroot (R : TriadicCube 2) :
      Measurable (fun ω => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand 48)) N Q.scale
        (aoCirStepWeights N t) ω) := by
    have hratio := root_inverse_observable_eq_reference_ratio M R
      (protectedOldLabel R.scale (orderBand 48)) N Q.scale
      (aoCirStepWeights N t)
    have heq : (fun ω => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand 48)) N Q.scale
        (aoCirStepWeights N t) ω) =
      fun ω => ((Annealed.sigmaBar M Q.scale : ℝ) /
        (Annealed.sigmaBar M (protectedOldLabel R.scale (orderBand 48)) : ℝ)) *
        rootInverseResponse M R
          (protectedOldLabel R.scale (orderBand 48)) N
          (aoCirStepWeights N t) ω := funext hratio
    rw [heq]
    exact measurable_const.mul (root_inverse_response_measurable M
      (protectedOldLabel R.scale (orderBand 48)) N
      (aoCirStepWeights N t) R)
  have hpoint (ω : Cutoff.CutoffSample 2) :
      Book.Ch02.finsetSupReal S (fun R =>
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M Q.scale : ℝ)
            (aoCirInsertedResponseCoefficient Q n hQ N t ω)))) =
      Book.Ch02.finsetSupReal S (fun R => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand 48)) N Q.scale
        (aoCirStepWeights N t) ω) := by
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    have hRglobal : R ∈ descendantsAtDepth Q (j + d) :=
      mem_descendantsAtDepth_add hU hR
    exact (aoCir_step_inverse_cell_eq_responseFrame_norm M Q R n ell hQ hK N hN
      48 t (j + d) hRglobal ω).symm
  have heq :
      (fun ω => lemmaVInverseDepthMax U
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M Q.scale : ℝ)
          (aoCirInsertedResponseCoefficient Q n hQ N t ω)) d) =
      S.sup' hS (fun R ω => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand 48)) N Q.scale
        (aoCirStepWeights N t) ω) := by
    funext ω
    change Book.Ch02.finsetSupReal S _ = _
    simpa only [Finset.sup'_apply,
      ← Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS] using hpoint ω
  rw [heq]
  exact Finset.measurable_sup' hS (fun R _ => hroot R)

private theorem aoCir_reset_tile_history_measurable
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (t : ℝ) (j : ℕ) :
    Measurable (fun ω => pureFluxSourceTileHistory Q j
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N t ω))) := by
  classical
  let S := descendantsAtDepth Q j
  have hS : S.Nonempty := descendantsAtDepth_nonempty Q j
  let a := fun ω => responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M Q.scale : ℝ)
    (aoCirInsertedResponseCoefficient Q n hQ N t ω)
  let r : ℝ := ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹
  have hterm (U : TriadicCube 2) (hU : U ∈ S) (d : ℕ) :
      Measurable (fun ω => r ^ d * lemmaVInverseDepthMax U (a ω) d) :=
    measurable_const.mul (aoCir_reset_tile_depth_measurable M Q U n ell hQ hK
      N hN t j d hU)
  have hhistory (U : TriadicCube 2) (hU : U ∈ S) :
      Measurable (fun ω => lemmaVInverseHistory U (a ω)
        ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    change Measurable (fun ω => (1 - r) *
      ∑' d : ℕ, r ^ d * lemmaVInverseDepthMax U (a ω) d)
    exact measurable_const.mul (Measurable.tsum (hterm U hU))
  have hsup : Measurable (S.sup' hS fun U ω =>
      lemmaVInverseHistory U (a ω) ((3 : ℝ) ^ (1 / 4 : ℝ))) :=
    Finset.measurable_sup' hS (fun U hU => hhistory U hU)
  have heq : (fun ω => pureFluxSourceTileHistory Q j (a ω)) =
      S.sup' hS (fun U ω => lemmaVInverseHistory U (a ω)
        ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    funext ω
    change Book.Ch02.finsetSupReal S _ = _
    rw [Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS]
    simp only [Finset.sup'_apply]
  rw [heq]
  exact hsup

/-- The actual four-level tile history has every reset-derived moment of
order at least 48. The profile envelope controls the complete descendant
series, while the finite maxima and history series are measurable. -/
theorem aoCir_reset_tile_history_memLp
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (q : ℝ) (hq48 : 48 ≤ q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MemLp (fun ω => pureFluxSourceTileHistory Q 4
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N t ω)))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    eLpNorm (fun ω => pureFluxSourceTileHistory Q 4
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N t ω)))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aoCirInverseHistoryFactor M.gamma *
        Real.rpow 9 ((4 : ℝ) / q) *
        orderInverseProfile (153 / 100) M.gamma q 5) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := fun ω => pureFluxSourceTileHistory Q 4
    (responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M Q.scale : ℝ)
      (aoCirInsertedResponseCoefficient Q n hQ N t ω))
  let S := fun ω => aoCirResetInverseDepthProfileSeries M Q 4 N 48 t ω
  have hBmeas : Measurable B := by
    change Measurable (fun ω => pureFluxSourceTileHistory Q 4
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N t ω)))
    exact aoCir_reset_tile_history_measurable M Q n ell hQ hK N hN t 4
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω := by
    exact pureFlux_source_tile_history_nonneg Q 4 _
  have hS0 (ω : Cutoff.CutoffSample 2) : 0 ≤ S ω := by
    unfold S aoCirResetInverseDepthProfileSeries
    have hr : 0 < aoCirInverseHistoryDiscount := by
      unfold aoCirInverseHistoryDiscount
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hr1 : aoCirInverseHistoryDiscount < 1 := by
      unfold aoCirInverseHistoryDiscount
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hmax (d : ℕ) :
        0 ≤ aoCirResetInverseDepthMax M Q (4 + d) N Q.scale 48 t ω := by
      unfold aoCirResetInverseDepthMax
      exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ => by
        unfold rootInverseObservable
        exact mul_nonneg (Annealed.sigmaBar_characterization M Q.scale).1.le
          (norm_nonneg _)
    apply mul_nonneg
    · exact sub_nonneg.mpr hr1.le
    · exact tsum_nonneg fun d => mul_nonneg
        (pow_nonneg hr.le d) (hmax d)
  have hBS (ω : Cutoff.CutoffSample 2) : B ω ≤ S ω := by
    dsimp [B, S]
    exact aoCir_step_tile_history_le_fixed_reset_profile_series M Q n ell hQ hK
      N hN 4 48 t ω
  have hLp := aoCir_reset_inverse_fixed_envelope_bound reset M h hM hγ hγsmall
    hstate Q n ell hQ hK N hN 4 q hq48 t ht0 ht1
  have hmono : eLpNorm B (ENNReal.ofReal q) μ ≤
      eLpNorm S (ENNReal.ofReal q) μ := by
    apply eLpNorm_mono_ae hBmeas.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hB0 ω),
      Real.norm_eq_abs, abs_of_nonneg (hS0 ω)]
    exact hBS ω
  have hfinite : eLpNorm B (ENNReal.ofReal q) μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmono.trans hLp)
  refine ⟨lt_top_iff_ne_top.mpr hfinite, ?_⟩
  convert hmono.trans hLp using 1
  norm_num [B, S, μ]

end ASDExplicitGamma.AllOrder
