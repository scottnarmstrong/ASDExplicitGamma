module

public import ASDExplicitGamma.Main.HotObsMoments
public import ASDExplicitGamma.Main.HotTrialExpectationsSplitOfHist

/-! Successors of `HotObsMoments` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- Successor of `main_hot_obs_cell_trace_l2` with the history envelope `Hfun`. -/
theorem main_hot_obs_cell_trace_l2_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    MemLp (rawCubeFourLoadTrace M m U t) 2 μ ∧
      lpNorm (rawCubeFourLoadTrace M m U t) 2 μ ≤
        Hfun t / (1 - mainAlpha) := by
  intro μ
  obtain ⟨hmem, hnorm⟩ := main_hot_origin_trace_l2_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ m hpast t ht
  have hOrigin : MemLp (rawDepthFourLoadTrace M m U.scale t) 2 μ := by
    rw [hscale]
    exact hmem
  refine ⟨main_rawCubeFourLoadTrace_memLp_of_origin M m U t 2 hOrigin, ?_⟩
  rw [main_rawCubeFourLoadTrace_lpNorm_eq_origin M m U t 2 hOrigin, hscale]
  exact hnorm

end
end ASDExplicitGamma.Main
end
