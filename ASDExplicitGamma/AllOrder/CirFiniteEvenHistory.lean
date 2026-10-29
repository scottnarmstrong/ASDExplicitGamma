/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirResetProfiles
public import ASDExplicitGamma.Inverse.StoppedSelectedMaximum
public import ASDExplicitGamma.Inverse.BankHistoryPhysical

/-! # Depthwise inverse profiles for the finite-even CIR step -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

noncomputable section

/-- The true-frame inverse-root maximum at a specified descendant depth for
the actual partial shell path.  Each descendant uses its own protected reset
label, while `K₀` is the common reference frame. -/
def aoCirResetInverseDepthMax (M : ABKModel 2) (Q : TriadicCube 2)
    (d : ℕ) (N K₀ : ℤ) (q : ℝ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q d) fun R =>
    rootInverseObservable M R
      (protectedOldLabel R.scale (orderBand q)) N K₀
      (aoCirStepWeights N t) ω

/-- The reset producer bounds every inverse root in a finite descendant layer.
The population cost is paid by the exact cardinal factor `card^(1/q)`.  The
order-dependent frame gap is computed from the descendant scale, not replaced
by the top-level gap. -/
theorem aoCir_reset_inverse_depth_population_bound
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ n : ℤ, nativeInductionState M h n)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale ≤ N)
    (d : ℕ) (q : ℝ) (hq48 : 48 ≤ q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm
        (fun ω => ENNReal.ofReal
          (aoCirResetInverseDepthMax M Q d N Q.scale q t ω))
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((descendantsAtDepth Q d).card : ℝ≥0∞) ^ (1 / q : ℝ) *
        ENNReal.ofReal (orderInverseProfile (153 / 100) M.gamma q
          ((d : ℝ) + 1)) := by
  classical
  let S := descendantsAtDepth Q d
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f : ↥S → Cutoff.CutoffSample 2 → ℝ≥0∞ := fun R ω =>
    ENNReal.ofReal (rootInverseObservable M R.1
      (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
      (aoCirStepWeights N t) ω)
  have hrootNonneg (R : ↥S) (ω : Cutoff.CutoffSample 2) :
      0 ≤ rootInverseObservable M R.1
        (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω := by
    unfold rootInverseObservable
    exact mul_nonneg (Annealed.sigmaBar_characterization M Q.scale).1.le
      (norm_nonneg _)
  have hf : ∀ R : ↥S, Measurable (f R) := by
    intro R
    have hmeas : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        rootInverseObservable M R.1
          (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
          (aoCirStepWeights N t) ω) := by
      have hratio := root_inverse_observable_eq_reference_ratio M R.1
        (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t)
      have heq :
          (fun ω => rootInverseObservable M R.1
            (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
            (aoCirStepWeights N t) ω) =
          (fun ω => ((Annealed.sigmaBar M Q.scale : ℝ) /
            (Annealed.sigmaBar M
              (protectedOldLabel R.1.scale (orderBand q)) : ℝ)) *
            rootInverseResponse M R.1
              (protectedOldLabel R.1.scale (orderBand q)) N
              (aoCirStepWeights N t) ω) := funext hratio
      rw [heq]
      exact measurable_const.mul
        (root_inverse_response_measurable M
          (protectedOldLabel R.1.scale (orderBand q)) N
          (aoCirStepWeights N t) R.1)
    exact ENNReal.continuous_ofReal.measurable.comp hmeas
  have hprofile (R : ↥S) :
      eLpNorm
          (fun ω => rootInverseObservable M R.1
            (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
            (aoCirStepWeights N t) ω)
          (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (orderInverseProfile (153 / 100) M.gamma q
          ((d : ℝ) + 1)) := by
    have hscale := scale_eq_sub_of_mem_descendantsAtDepth R.2
    have hRscale : R.1.scale ≤ N := by omega
    have hprof := aoCir_step_profile_of_reset reset M h hM hγ hstate
      R.1 N Q.scale hRscale q (by linarith) t ht0 ht1
    have hfGap :
        |((Q.scale - R.1.scale + 1 : ℤ) : ℝ)| = (d : ℝ) + 1 := by
      rw [hscale]
      have hInt : Q.scale - (Q.scale - (d : ℤ)) + 1 = (d : ℤ) + 1 := by omega
      rw [hInt]
      push_cast
      rw [abs_of_nonneg (by positivity)]
    have hsmall := hprof.2.2 hγsmall
    simpa only [μ, hfGap] using hsmall
  have hprofile' (R : ↥S) : eLpNorm (f R) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (orderInverseProfile (153 / 100) M.gamma q
        ((d : ℝ) + 1)) := by
    change eLpNorm (fun ω => ENNReal.ofReal
      (rootInverseObservable M R.1
        (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω)) (ENNReal.ofReal q) μ ≤ _
    change eLpNorm (ENNReal.ofReal ∘ fun ω =>
      rootInverseObservable M R.1
        (protectedOldLabel R.1.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω) (ENNReal.ofReal q) μ ≤ _
    rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall (hrootNonneg R))]
    exact hprofile R
  have hmax := finite_maximum_Lp μ (Finset.univ : Finset ↥S) f hf q
    (by linarith [hq48])
    (ENNReal.ofReal (orderInverseProfile (153 / 100) M.gamma q
      ((d : ℝ) + 1))) (by
        intro R hR
        exact hprofile' R)
  have hmaxReal (ω : Cutoff.CutoffSample 2) :
      historyFiniteMax (Finset.univ : Finset ↥S)
          (fun R (_ : Unit) => f R ω) () =
        ENNReal.ofReal (Book.Ch02.finsetSupReal S fun R =>
          rootInverseObservable M R
            (protectedOldLabel R.scale (orderBand q)) N Q.scale
            (aoCirStepWeights N t) ω) := by
    simpa [f] using bank_finite_max_ofReal S (descendantsAtDepth_nonempty Q d)
      (fun R => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω)
  have hfunction :
      (fun ω => ENNReal.ofReal (aoCirResetInverseDepthMax M Q d N Q.scale q t ω)) =
        fun ω => historyFiniteMax (Finset.univ : Finset ↥S)
          (fun R (_ : Unit) => f R ω) () := by
    funext ω
    exact (hmaxReal ω).symm
  rw [hfunction]
  have hmaxFun :
      (fun ω => historyFiniteMax (Finset.univ : Finset ↥S)
        (fun R (_ : Unit) => f R ω) ()) =
      historyFiniteMax (Finset.univ : Finset ↥S) f := by
    funext ω
    rfl
  rw [hmaxFun]
  have hcard : ((Finset.univ : Finset ↥S).card : ℝ≥0∞) =
      (S.card : ℝ≥0∞) := by simp
  simpa only [μ, hcard, S] using hmax

end
end ASDExplicitGamma.AllOrder
