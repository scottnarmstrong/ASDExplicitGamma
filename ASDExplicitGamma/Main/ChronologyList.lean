module

public import ASDExplicitGamma.Main.ChronologyInsertion
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

theorem mainInsertionList_length : mainInsertionList.length = 40 := by decide +kernel

theorem mainInsertionList_panels_length (ins : MainInsertionEndpoints)
    (h : ins ∈ mainInsertionList) : ins.panels.length = 8 := by
  have hall : mainInsertionList.all (fun ins => decide (ins.panels.length = 8)) = true := by
    decide +kernel
  simpa using List.all_eq_true.mp hall ins h

theorem mainInsertionList_frame_fields (ins : MainInsertionEndpoints)
    (h : ins ∈ mainInsertionList) :
    insertionFrameRecurrenceFields ins.frameLower ins.frameUpper := by
  have hall : mainInsertionList.all
      (fun ins => insertionFrameRecurrenceFieldGridCheck ins.frameLower ins.frameUpper) = true := by
    decide +kernel
  exact insertionFrameRecurrenceFields_sound _ _ (List.all_eq_true.mp hall ins h)

theorem mainCert_eq_reverse_map :
    mainCert = mainInsertionList.reverse.map MainInsertionEndpoints.toInsertionCert := by
  decide +kernel

theorem mainCert_length : mainCert.length = 40 := by decide +kernel

theorem mainCert_get (i : ℕ) (hi : i < 40) :
    ∃ ins, mainInsertionList[40 - i - 1]? = some ins ∧
      mainCert[i]? = some ins.toInsertionCert := by
  obtain ⟨ins, hins⟩ : ∃ ins, mainInsertionList[40 - i - 1]? = some ins :=
    ⟨_, List.getElem?_eq_getElem (by rw [mainInsertionList_length]; omega)⟩
  refine ⟨ins, hins, ?_⟩
  rw [mainCert_eq_reverse_map, List.getElem?_map,
    List.getElem?_reverse (by rw [mainInsertionList_length]; omega)]
  rw [show mainInsertionList.length - 1 - i = 40 - i - 1 by
    rw [mainInsertionList_length]; omega, hins]
  rfl

end ASDExplicitGamma.Main

end
