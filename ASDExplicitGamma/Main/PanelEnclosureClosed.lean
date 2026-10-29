module

public import ASDExplicitGamma.Main.PanelEnclosure
public import ASDExplicitGamma.Main.PanelCertifiedFinal
public import ASDExplicitGamma.Main.PanelLeafBridges
public import ASDExplicitGamma.Main.ObsChronoFinal
public import ASDExplicitGamma.Main.EnvelopeASlope

/-! Closing MA-PANEL-ENCLOSURE: the leaf bounds L1/L2 and the v-monotone (chronology) step
discharge `PanelLeafL1L2` and `ObsChronoV35`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse ASDExplicitGamma Set
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror
  ASDExplicitGamma.Numerics.MainReturnCertificate

noncomputable section

theorem panelLeafL1L2 : PanelLeafL1L2 :=
  fun d s f => ⟨leaf_inverseAbsolute d s f, leaf_pMeanSlope d s f, leaf_pXiSlope d s f⟩

theorem obsChronoV35_of_node (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ) (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (hγ0 : M.gamma = gammaZero) : ObsChronoV35 M m hobs := by
  have hn := ma_chronology_v_monotone_node' M h hM hγ N hpast m hm hobs h1 h40 hγ0
  dsimp only at hn
  have hgpos : 0 < M.gamma := by rw [hγ0]; norm_num [gammaZero]
  have hclock : 0 ≤ mainSourceClock M.gamma := (mainSourceClock_pos hgpos).le
  have hb2 : Real.sqrt (mainSourceClock M.gamma) ^ 2 = panelVbar := by
    rw [Real.sq_sqrt hclock, hγ0]
  have hth : theta M = 1 := by
    unfold theta; rw [hγ0]; exact div_self (by norm_num [gammaZero])
  have hvle := chrono_v_le_clock M h m hgpos (hpast m hm)
  have hvw : (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 ≤ panelVbar := by
    rw [← hb2, Real.sq_sqrt hclock, hγ0]; rw [hγ0] at hvle; exact hvle
  have hv0 : 0 ≤ (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 := sq_nonneg _
  have hg0 : 0 ≤ M.gamma := hgpos.le
  have hAup : ∀ s ∈ Set.Icc (0 : ℝ) 1, inSourceMeanActual M m 5 s ≤
      mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s := by
    intro s hs
    have h0 := main_envelope_a_actual_law M h hM hγ N hpast m hm hs
    have h2 := chrono_envA_mono (gamma := M.gamma) (a0 := mainSourceMeanPrefix) (t := s) hg0 hγ hv0
      hvw hs.1
    rw [div_pow] at h2
    have h3 := h0.trans h2
    rwa [hγ0] at h3
  have hq := chrono_capQ_nonneg' (hobs - 1)
  have hH0 : ∀ s, 0 ≤ mainEnvelopeH35 panelVbar gammaZero s := fun s => chrono_envH35_nonneg _ _ _
  obtain ⟨hdom, hae⟩ := hn
  rw [hb2, hγ0, hth] at hdom hae
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨h0, hle⟩ := hdom s hs
    exact ⟨h0, hle.trans (min_le_min (hAup s hs) le_rfl)⟩
  · filter_upwards [hae] with s hs hs01
    have hd := hs hs01
    have hmono := chrono_sourceError_mono (v := panelVbar) (w := panelVbar)
      (H := mainEnvelopeH35 panelVbar gammaZero s) (H' := mainEnvelopeH35 panelVbar gammaZero s)
      (f := modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (q := mainAffineFlatBoundaryCapQ (hobs - 1))
      (a := inSourceMeanActual M m 5 s)
      (a' := mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s)
      (xi := mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s)
      (xi' := mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s)
      hq (by unfold panelVbar; exact (mainSourceClock_pos (by norm_num [gammaZero])).le) le_rfl
      (hAup s hs01) (hH0 s) le_rfl le_rfl
    have hc : (156 / 5 : ℝ) = 31.2 := by norm_num
    have hAff : mainAffineTerm M (Real.sqrt (mainSourceClock gammaZero))
        (mainAffineFlatBoundaryCapQ (hobs - 1)) s =
        panelVbar / 2 * mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s +
          panelVbar * mainAffineFlatBoundaryCapQ (hobs - 1) * (mainBeta - 1) +
          (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 panelVbar / 9 := by
      have hc0 : 0 ≤ mainSourceClock gammaZero := by
        have := hclock; rwa [hγ0] at this
      unfold mainAffineTerm
      rw [hγ0, Real.sq_sqrt hc0]
    rw [hAff] at hd
    rw [hc]
    linarith

/-- MA-PANEL-ENCLOSURE at `γ = γ₀`: for every observer `1 ≤ hobs ≤ 40` and every certified panel
`j < 8` there are certified data `d` and endpoints `e` (with `e` the `j`-th panel of insertion
`hobs`) such that on `P = [j/8, (j+1)/8]`, `f' ≤ aUpper/G - (ellLower/G) f` a.e., and the endpoint
recurrence `f((j+1)/8) ≤ rhoUpper/G f(j/8) + offsetUpper/G` holds. -/
theorem ma_panel_enclosure_node (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ) (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (hγ0 : M.gamma = gammaZero) (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' hobs j d e ∧ (∃ ins, mainInsertionList[hobs - 1]? = some ins ∧
        ins.panels[j]? = some e) ∧
      (∀ᵐ s : ℝ, s ∈ Icc ((j : ℝ) / 8) (((j : ℝ) + 1) / 8) →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          (e.aUpper : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) -
            (e.ellLower : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) *
              modelTraceHeatAverage (m + (hobs : ℤ)) M m s) ∧
      modelTraceHeatAverage (m + (hobs : ℤ)) M m (((j : ℝ) + 1) / 8) ≤
        (e.rhoUpper : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) *
            modelTraceHeatAverage (m + (hobs : ℤ)) M m ((j : ℝ) / 8) +
          (e.offsetUpper : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) := by
  obtain ⟨d, e, hcert, hins⟩ := panel_certified hobs j h1 h40 hj
  obtain ⟨hb, hfields, hanchor, hmeanQ, hxiQ, hq, hlo, hhi⟩ := hcert
  have hmean : (d.initialMean : ℝ) = mainSourceMeanPrefix := by
    rw [hmeanQ]; rfl
  have hxi : (d.initialInverseMean : ℝ) = mainSourceInversePrefix + 1 / 10 ^ 12 := by
    have hQ : observer1Panel0Data.initialInverseMean =
        ASDExplicitGamma.Numerics.MainReturn.observer1Panel0Data.initialInverseMean := by
      decide +kernel
    rw [hxiQ, hQ]; unfold mainSourceInversePrefix; ring
  have hChrono := obsChronoV35_of_node M h hM hγ N hpast m hm hobs h1 h40 hγ0
  have hAC := (ma_generator_hypotheses_observer_node' M h hM hγ N hpast m hm hobs
    h1 h40).1
  have hjr : (j : ℝ) + 1 ≤ 8 := by exact_mod_cast hj
  have ha0 : (0 : ℝ) ≤ (j : ℝ) / 8 := by positivity
  have hb1 : ((j : ℝ) + 1) / 8 ≤ 1 := by linarith [hjr]
  have hdsub : ∀ s ∈ Icc ((j : ℝ) / 8) (((j : ℝ) + 1) / 8), QInterval.Contains d.time s := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rw [hlo]; push_cast; exact hs.1
    · rw [hhi]; push_cast; exact hs.2
  refine ⟨d, e, ⟨hb, hfields, hanchor, hmeanQ, hxiQ, hq, hlo, hhi⟩, hins, ?_, ?_⟩
  · obtain ⟨hdom, hae⟩ := hChrono
    filter_upwards [hae] with t ht htab
    have hsub : t ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans htab.1, htab.2.trans hb1⟩
    exact panel_pointwise panelLeafL1L2 M m hobs d e hb hfields hanchor hmean hxi
      (by rw [hq]) t hsub.1 (hdsub t htab) (hdom t hsub) (ht hsub)
  · exact panel_endpoint panelLeafL1L2 M m hobs hChrono hAC d e hb hfields hanchor
      hmean hxi (by rw [hq]) (by linarith [ha0]) (by rw [add_div]; ring) ha0 hb1 hdsub

end

end ASDExplicitGamma.Main
