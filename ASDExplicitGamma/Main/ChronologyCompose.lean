module

public import ASDExplicitGamma.Main.ChronologyInsertion
public import ASDExplicitGamma.Main.ChronologyList
public import ASDExplicitGamma.Main.PanelCertifiedFinal

/-! Chronology: the 40 observer insertions composed in chronological order.
The per-panel analytic input is `panel_endpoint` (taken through its named
hypotheses `PanelLeafL1L2` and `ObsChronoV35`, with absolute continuity). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian

theorem foldl_take_succ {α β : Type} (f : α → β → α) (x : α) (C : List β) (i : ℕ) (c : β)
    (h : C[i]? = some c) :
    (C.take (i + 1)).foldl f x = f ((C.take i).foldl f x) c := by
  rw [List.take_add_one, h]
  simp [List.foldl_append]

/-- The chronology node data at every observer of the composition (label `m + i`, observer `40 - i`). -/
def ObsChronoAll (M : ABKModel 2) (m : ℤ) : Prop :=
  ∀ i : ℕ, i < 40 → ObsChronoV35 M (m + (i : ℤ)) (40 - i) ∧
    AbsolutelyContinuousOnInterval
      (modelTraceHeatAverage (m + (i : ℤ) + ((40 - i : ℕ) : ℤ)) M (m + (i : ℤ))) 0 1

/-- One observer step from the certified panels of insertion `k`. -/
theorem main_observer_step (hL : PanelLeafL1L2) (M : ABKModel 2)
    (hγ : M.gamma ≤ ASDExplicitGamma.gammaZero) (m : ℤ) (k : ℕ) (h1 : 1 ≤ k) (h40 : k ≤ 40)
    (hChrono : ObsChronoV35 M m k)
    (hAC : AbsolutelyContinuousOnInterval (modelTraceHeatAverage (m + (k : ℤ)) M m) 0 1)
    (ins : MainInsertionEndpoints) (hins : mainInsertionList[k - 1]? = some ins) (x0 : ℕ)
    (hOld : (∫ ω, cutoffTraceDefect M m (m + (k : ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (x0 : ℝ) / (Spike.gridScale : ℝ)) :
    (∫ ω, cutoffTraceDefect M (m + 1) (m + (k : ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (advanceInsertion x0 ins.toInsertionCert : ℝ) / (Spike.gridScale : ℝ) := by
  have hmem : ins ∈ mainInsertionList := List.mem_of_getElem? hins
  have hlen := mainInsertionList_panels_length ins hmem
  have hframe := mainInsertionList_frame_fields ins hmem
  have hall : ∀ j : ℕ, j < 8 → ∃ (d : MainPanelData) (e : PanelEndpoints),
      PanelCertified' k j d e ∧ ins.panels[j]? = some e := by
    intro j hj
    obtain ⟨d, e, hc, ins', h1', h2'⟩ := panel_certified k j h1 h40 hj
    rw [hins] at h1'
    cases h1'
    exact ⟨d, e, hc, h2'⟩
  have : Nonempty PanelEndpoints := ⟨observer1Panel0Endpoints⟩
  have : Nonempty MainPanelData := ⟨observer1Panel0Data⟩
  choose! d e hc hmemj using hall
  have hpanels : ins.panels = (List.range 8).map e := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < 8
    · rw [hmemj n hn]
      simp [List.getElem?_map, List.getElem?_range, hn]
    · have h1 : ins.panels[n]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      rw [h1]
      simp [List.getElem?_map, List.getElem?_range, hn]
  have hcert : ins.toInsertionCert.panels = (List.range 8).map
      (fun j => mainPanelCertOfEndpoints (e j)) := by
    simp only [MainInsertionEndpoints.toInsertionCert, hpanels, List.map_map]
    rfl
  have hframe' : insertionFrameRecurrenceFields ins.toInsertionCert.frameLower
      ins.toInsertionCert.frameUpper := hframe
  refine main_insertion_step_of_endpoint_bounds M hγ m (m + (k : ℤ))
    ins.toInsertionCert hframe' e hcert x0 hOld ?_
  intro j hj
  obtain ⟨hb, hfields, hanchor, hmeanQ, hxiQ, hqQ, hlo, hhi⟩ := hc j hj
  have hmean : ((d j).initialMean : ℝ) = mainSourceMeanPrefix := by
    rw [hmeanQ]; rfl
  have hxi : ((d j).initialInverseMean : ℝ) = mainSourceInversePrefix + 1 / 10 ^ 12 := by
    have hq : MainReturnCertificate.observer1Panel0Data.initialInverseMean =
        MainReturn.observer1Panel0Data.initialInverseMean := by decide +kernel
    rw [hxiQ, hq]; unfold mainSourceInversePrefix; ring
  have hab : (j : ℝ) / 8 ≤ ((j + 1 : ℕ) : ℝ) / 8 := by
    push_cast; linarith
  have hlen8 : ((j + 1 : ℕ) : ℝ) / 8 - (j : ℝ) / 8 = (1 / 8 : ℝ) := by
    push_cast; ring
  have ha0 : (0 : ℝ) ≤ (j : ℝ) / 8 := by positivity
  have hb1 : ((j + 1 : ℕ) : ℝ) / 8 ≤ 1 := by
    have : ((j + 1 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hj
    linarith
  have hdsub : ∀ s ∈ Icc ((j : ℝ) / 8) (((j + 1 : ℕ) : ℝ) / 8),
      QInterval.Contains (d j).time s := by
    intro s hs
    have hlo' : (((d j).time.lo : ℚ) : ℝ) = (j : ℝ) / 8 := by rw [hlo]; push_cast; ring
    have hhi' : (((d j).time.hi : ℚ) : ℝ) = ((j + 1 : ℕ) : ℝ) / 8 := by
      rw [hhi]; push_cast; ring
    exact ⟨hlo' ▸ hs.1, hhi' ▸ hs.2⟩
  exact panel_endpoint hL M m k hChrono hAC (d j) (e j) hb hfields hanchor hmean hxi
    hqQ hab hlen8 ha0 hb1 hdsub

/-- The 40 insertions composed in chronological order (observers 40 down to 1): the completed
ordinary mean at label `m + i` on the fixed cube `m + 40` obeys the grid recurrence. -/
theorem main_composed_prefix (hL : PanelLeafL1L2) (M : ABKModel 2)
    (hγ : M.gamma ≤ ASDExplicitGamma.gammaZero) (m : ℤ)
    (hcold : (∫ ω, cutoffTraceDefect M m (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (Spike.cold40Upper : ℝ) / (Spike.gridScale : ℝ))
    (hobs : ObsChronoAll M m) (C : List InsertionCert)
    (hC : ∀ i : ℕ, i < 40 → ∃ ins, mainInsertionList[40 - i - 1]? = some ins ∧
      C[i]? = some ins.toInsertionCert) :
    ∀ i : ℕ, i ≤ 40 →
      (∫ ω, cutoffTraceDefect M (m + (i : ℤ)) (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (((C.take i).foldl advanceInsertion Spike.cold40Upper : ℕ) : ℝ) /
          (Spike.gridScale : ℝ) := by
  intro i
  induction i with
  | zero => intro _; simpa using hcold
  | succ i ih =>
    intro hi
    have hi40 : i < 40 := by omega
    have ihi := ih (by omega)
    obtain ⟨hChrono, hAC⟩ := hobs i hi40
    have hcube : m + (i : ℤ) + ((40 - i : ℕ) : ℤ) = m + 40 := by
      have : ((40 - i : ℕ) : ℤ) = 40 - (i : ℤ) := by omega
      omega
    obtain ⟨ins, hins, hcertGet⟩ := hC i hi40
    have hOld : (∫ ω, cutoffTraceDefect M (m + (i : ℤ)) (m + (i : ℤ) + ((40 - i : ℕ) : ℤ)) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (((C.take i).foldl advanceInsertion Spike.cold40Upper : ℕ) : ℝ) /
          (Spike.gridScale : ℝ) := by
      rw [hcube]; exact ihi
    have hstep := main_observer_step hL M hγ (m + (i : ℤ)) (40 - i) (by omega)
      (by omega) hChrono hAC ins hins _ hOld
    rw [hcube] at hstep
    have hidx' : m + ((i + 1 : ℕ) : ℤ) = m + (i : ℤ) + 1 := by push_cast; ring
    rw [hidx', foldl_take_succ advanceInsertion Spike.cold40Upper C i _ hcertGet]
    exact hstep

/-- Chronology composition: from the cold lag-40 grid bound, the completed ordinary mean at
label `m + 40` is bounded by the composed certificate value. -/
theorem main_composed_ordinary_mean (hL : PanelLeafL1L2) (M : ABKModel 2)
    (hγ : M.gamma ≤ ASDExplicitGamma.gammaZero) (m : ℤ)
    (hcold : (∫ ω, cutoffTraceDefect M m (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (Spike.cold40Upper : ℝ) / (Spike.gridScale : ℝ))
    (hobs : ObsChronoAll M m) :
    (∫ ω, cutoffTraceDefect M (m + 40) (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (Spike.composeUpper mainCert : ℝ) / (Spike.gridScale : ℝ) := by
  have h := main_composed_prefix hL M hγ m hcold hobs mainCert mainCert_get 40 le_rfl
  rw [List.take_of_length_le (by rw [mainCert_length])] at h
  exact_mod_cast h

end ASDExplicitGamma.Main

end
