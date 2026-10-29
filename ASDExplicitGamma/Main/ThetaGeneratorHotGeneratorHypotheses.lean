module

public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorIntegrated
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotInverseIdent
public import ASDExplicitGamma.Main.ThetaGeneratorHotObserverXiDomain
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplit
public import ASDExplicitGamma.Main.InverseDeficitHeatAdapter

/-! MA-GENERATOR-HYPOTHESES at observer roots: domain condition, differential inequality
with the source `I_abs`, in the output form of the observer inverse-deficit adapter. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Inverse

noncomputable section

/-- DOMAIN CONDITION at an observer root: `0 ≤ f(t) ≤ min (a(t), ξ(t)/b_o)`, with `b_o` the OLD
local bank `mainBetaOld = 3683/2500`. -/
theorem main_generator_hot_domain_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ modelTraceHeatAverage (m + (hobs : ℤ)) M m t ∧
      modelTraceHeatAverage (m + (hobs : ℤ)) M m t ≤
        min (inSourceMeanActual M m 5 t)
          (mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
            M.gamma (theta M * mainSourceInversePrefix) (theta M) t / mainBetaOld) := by
  obtain ⟨hΔint, hΔeq, hf0, -⟩ := main_hot_obs_energy_drop_identity_Th M h hM hγ N hpast m hm hobs t ht
  have hΔ0 : 0 ≤ ∫ ω, mainHotDropObs_Th M m hobs t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    integral_nonneg fun ω => (main_hot_drop_obs_pathwise_Th M m hobs t ω).2
  have hxi := hot_observer_xi_domain_Th M h hM hγ N hpast m hm t ht hobs h40
  have hbo : 0 < mainBetaOld := by norm_num [mainBetaOld]
  refine ⟨hf0, le_min ?_ ?_⟩
  · linarith
  · rw [le_div_iff₀ hbo]
    linarith

end

end ASDExplicitGamma.Main
