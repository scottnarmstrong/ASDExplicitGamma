module

public import ASDExplicitGamma.Main.PanelEnclosure
public import ASDExplicitGamma.Numerics.MainReturnCertificate.Composition

/-! Instantiation of the certificate leaves at all 40 observers and 8 panels:
each panel's data and endpoints are tied to the observer-independent prefixes, the covariance cap
`q_{k-1}`, and the panel's time interval `[j/8, (j+1)/8]`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.MainReturnCertificate

/-- The certified data of observer `k`, panel `j`. -/
def PanelCertified' (k j : ℕ) (d : MainPanelData) (e : PanelEndpoints) : Prop :=
  panelFormulaBounds d e ∧ panelRecurrenceFields e ∧ d.anchor = 1 / 100 ∧
    d.initialMean = observer1Panel0Data.initialMean ∧
    d.initialInverseMean = observer1Panel0Data.initialInverseMean ∧
    ((d.covarianceCap : ℚ) : ℝ) = mainAffineFlatBoundaryCapQ (k - 1) ∧
    d.time.lo = (j : ℚ) / 8 ∧ d.time.hi = ((j : ℚ) + 1) / 8

/-- The 40 insertion endpoint records, observer 1 first. -/
def mainInsertionList : List MainInsertionEndpoints := [
  observer1InsertionEndpoints,
  observer2InsertionEndpoints,
  observer3InsertionEndpoints,
  observer4InsertionEndpoints,
  observer5InsertionEndpoints,
  observer6InsertionEndpoints,
  observer7InsertionEndpoints,
  observer8InsertionEndpoints,
  observer9InsertionEndpoints,
  observer10InsertionEndpoints,
  observer11InsertionEndpoints,
  observer12InsertionEndpoints,
  observer13InsertionEndpoints,
  observer14InsertionEndpoints,
  observer15InsertionEndpoints,
  observer16InsertionEndpoints,
  observer17InsertionEndpoints,
  observer18InsertionEndpoints,
  observer19InsertionEndpoints,
  observer20InsertionEndpoints,
  observer21InsertionEndpoints,
  observer22InsertionEndpoints,
  observer23InsertionEndpoints,
  observer24InsertionEndpoints,
  observer25InsertionEndpoints,
  observer26InsertionEndpoints,
  observer27InsertionEndpoints,
  observer28InsertionEndpoints,
  observer29InsertionEndpoints,
  observer30InsertionEndpoints,
  observer31InsertionEndpoints,
  observer32InsertionEndpoints,
  observer33InsertionEndpoints,
  observer34InsertionEndpoints,
  observer35InsertionEndpoints,
  observer36InsertionEndpoints,
  observer37InsertionEndpoints,
  observer38InsertionEndpoints,
  observer39InsertionEndpoints,
  observer40InsertionEndpoints]

theorem observer1_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 1 j d e ∧ ∃ ins, mainInsertionList[0]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer1_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer1_all_recurrence_fields
  have hcap : ((observer1Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (1 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer1Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer1Panel0Data, observer1Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer1Panel0Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel0Data], by norm_num [observer1Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel1Data, observer1Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer1Panel1Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel1Data], by norm_num [observer1Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel2Data, observer1Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer1Panel2Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel2Data], by norm_num [observer1Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel3Data, observer1Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer1Panel3Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel3Data], by norm_num [observer1Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel4Data, observer1Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer1Panel4Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel4Data], by norm_num [observer1Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel5Data, observer1Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer1Panel5Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel5Data], by norm_num [observer1Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel6Data, observer1Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer1Panel6Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel6Data], by norm_num [observer1Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer1Panel7Data, observer1Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer1Panel7Data.covarianceCap = observer1Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer1Panel7Data], by norm_num [observer1Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer2_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 2 j d e ∧ ∃ ins, mainInsertionList[1]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer2_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer2_all_recurrence_fields
  have hcap : ((observer2Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (2 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer2Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer2Panel0Data, observer2Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer2Panel0Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel0Data], by norm_num [observer2Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel1Data, observer2Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer2Panel1Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel1Data], by norm_num [observer2Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel2Data, observer2Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer2Panel2Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel2Data], by norm_num [observer2Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel3Data, observer2Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer2Panel3Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel3Data], by norm_num [observer2Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel4Data, observer2Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer2Panel4Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel4Data], by norm_num [observer2Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel5Data, observer2Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer2Panel5Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel5Data], by norm_num [observer2Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel6Data, observer2Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer2Panel6Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel6Data], by norm_num [observer2Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer2Panel7Data, observer2Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer2Panel7Data.covarianceCap = observer2Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer2Panel7Data], by norm_num [observer2Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer3_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 3 j d e ∧ ∃ ins, mainInsertionList[2]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer3_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer3_all_recurrence_fields
  have hcap : ((observer3Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (3 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer3Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer3Panel0Data, observer3Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer3Panel0Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel0Data], by norm_num [observer3Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel1Data, observer3Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer3Panel1Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel1Data], by norm_num [observer3Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel2Data, observer3Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer3Panel2Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel2Data], by norm_num [observer3Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel3Data, observer3Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer3Panel3Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel3Data], by norm_num [observer3Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel4Data, observer3Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer3Panel4Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel4Data], by norm_num [observer3Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel5Data, observer3Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer3Panel5Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel5Data], by norm_num [observer3Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel6Data, observer3Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer3Panel6Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel6Data], by norm_num [observer3Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer3Panel7Data, observer3Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer3Panel7Data.covarianceCap = observer3Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer3Panel7Data], by norm_num [observer3Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer4_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 4 j d e ∧ ∃ ins, mainInsertionList[3]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer4_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer4_all_recurrence_fields
  have hcap : ((observer4Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (4 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer4Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer4Panel0Data, observer4Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer4Panel0Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel0Data], by norm_num [observer4Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel1Data, observer4Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer4Panel1Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel1Data], by norm_num [observer4Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel2Data, observer4Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer4Panel2Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel2Data], by norm_num [observer4Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel3Data, observer4Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer4Panel3Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel3Data], by norm_num [observer4Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel4Data, observer4Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer4Panel4Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel4Data], by norm_num [observer4Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel5Data, observer4Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer4Panel5Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel5Data], by norm_num [observer4Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel6Data, observer4Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer4Panel6Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel6Data], by norm_num [observer4Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer4Panel7Data, observer4Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer4Panel7Data.covarianceCap = observer4Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer4Panel7Data], by norm_num [observer4Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer5_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 5 j d e ∧ ∃ ins, mainInsertionList[4]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer5_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer5_all_recurrence_fields
  have hcap : ((observer5Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (5 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer5Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer5Panel0Data, observer5Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer5Panel0Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel0Data], by norm_num [observer5Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel1Data, observer5Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer5Panel1Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel1Data], by norm_num [observer5Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel2Data, observer5Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer5Panel2Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel2Data], by norm_num [observer5Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel3Data, observer5Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer5Panel3Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel3Data], by norm_num [observer5Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel4Data, observer5Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer5Panel4Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel4Data], by norm_num [observer5Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel5Data, observer5Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer5Panel5Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel5Data], by norm_num [observer5Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel6Data, observer5Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer5Panel6Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel6Data], by norm_num [observer5Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer5Panel7Data, observer5Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer5Panel7Data.covarianceCap = observer5Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer5Panel7Data], by norm_num [observer5Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer6_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 6 j d e ∧ ∃ ins, mainInsertionList[5]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer6_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer6_all_recurrence_fields
  have hcap : ((observer6Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (6 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer6Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer6Panel0Data, observer6Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer6Panel0Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel0Data], by norm_num [observer6Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel1Data, observer6Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer6Panel1Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel1Data], by norm_num [observer6Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel2Data, observer6Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer6Panel2Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel2Data], by norm_num [observer6Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel3Data, observer6Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer6Panel3Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel3Data], by norm_num [observer6Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel4Data, observer6Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer6Panel4Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel4Data], by norm_num [observer6Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel5Data, observer6Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer6Panel5Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel5Data], by norm_num [observer6Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel6Data, observer6Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer6Panel6Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel6Data], by norm_num [observer6Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer6Panel7Data, observer6Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer6Panel7Data.covarianceCap = observer6Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer6Panel7Data], by norm_num [observer6Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer7_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 7 j d e ∧ ∃ ins, mainInsertionList[6]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer7_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer7_all_recurrence_fields
  have hcap : ((observer7Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (7 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer7Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer7Panel0Data, observer7Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer7Panel0Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel0Data], by norm_num [observer7Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel1Data, observer7Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer7Panel1Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel1Data], by norm_num [observer7Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel2Data, observer7Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer7Panel2Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel2Data], by norm_num [observer7Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel3Data, observer7Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer7Panel3Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel3Data], by norm_num [observer7Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel4Data, observer7Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer7Panel4Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel4Data], by norm_num [observer7Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel5Data, observer7Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer7Panel5Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel5Data], by norm_num [observer7Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel6Data, observer7Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer7Panel6Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel6Data], by norm_num [observer7Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer7Panel7Data, observer7Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer7Panel7Data.covarianceCap = observer7Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer7Panel7Data], by norm_num [observer7Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer8_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 8 j d e ∧ ∃ ins, mainInsertionList[7]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer8_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer8_all_recurrence_fields
  have hcap : ((observer8Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (8 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer8Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer8Panel0Data, observer8Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer8Panel0Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel0Data], by norm_num [observer8Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel1Data, observer8Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer8Panel1Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel1Data], by norm_num [observer8Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel2Data, observer8Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer8Panel2Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel2Data], by norm_num [observer8Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel3Data, observer8Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer8Panel3Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel3Data], by norm_num [observer8Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel4Data, observer8Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer8Panel4Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel4Data], by norm_num [observer8Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel5Data, observer8Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer8Panel5Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel5Data], by norm_num [observer8Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel6Data, observer8Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer8Panel6Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel6Data], by norm_num [observer8Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer8Panel7Data, observer8Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer8Panel7Data.covarianceCap = observer8Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer8Panel7Data], by norm_num [observer8Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer9_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 9 j d e ∧ ∃ ins, mainInsertionList[8]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer9_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer9_all_recurrence_fields
  have hcap : ((observer9Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (9 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer9Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer9Panel0Data, observer9Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer9Panel0Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel0Data], by norm_num [observer9Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel1Data, observer9Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer9Panel1Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel1Data], by norm_num [observer9Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel2Data, observer9Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer9Panel2Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel2Data], by norm_num [observer9Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel3Data, observer9Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer9Panel3Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel3Data], by norm_num [observer9Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel4Data, observer9Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer9Panel4Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel4Data], by norm_num [observer9Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel5Data, observer9Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer9Panel5Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel5Data], by norm_num [observer9Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel6Data, observer9Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer9Panel6Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel6Data], by norm_num [observer9Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer9Panel7Data, observer9Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer9Panel7Data.covarianceCap = observer9Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer9Panel7Data], by norm_num [observer9Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer10_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 10 j d e ∧ ∃ ins, mainInsertionList[9]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer10_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer10_all_recurrence_fields
  have hcap : ((observer10Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (10 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer10Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer10Panel0Data, observer10Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer10Panel0Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel0Data], by norm_num [observer10Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel1Data, observer10Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer10Panel1Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel1Data], by norm_num [observer10Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel2Data, observer10Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer10Panel2Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel2Data], by norm_num [observer10Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel3Data, observer10Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer10Panel3Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel3Data], by norm_num [observer10Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel4Data, observer10Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer10Panel4Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel4Data], by norm_num [observer10Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel5Data, observer10Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer10Panel5Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel5Data], by norm_num [observer10Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel6Data, observer10Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer10Panel6Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel6Data], by norm_num [observer10Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer10Panel7Data, observer10Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer10Panel7Data.covarianceCap = observer10Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer10Panel7Data], by norm_num [observer10Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer11_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 11 j d e ∧ ∃ ins, mainInsertionList[10]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer11_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer11_all_recurrence_fields
  have hcap : ((observer11Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (11 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer11Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer11Panel0Data, observer11Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer11Panel0Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel0Data], by norm_num [observer11Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel1Data, observer11Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer11Panel1Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel1Data], by norm_num [observer11Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel2Data, observer11Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer11Panel2Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel2Data], by norm_num [observer11Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel3Data, observer11Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer11Panel3Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel3Data], by norm_num [observer11Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel4Data, observer11Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer11Panel4Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel4Data], by norm_num [observer11Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel5Data, observer11Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer11Panel5Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel5Data], by norm_num [observer11Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel6Data, observer11Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer11Panel6Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel6Data], by norm_num [observer11Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer11Panel7Data, observer11Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer11Panel7Data.covarianceCap = observer11Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer11Panel7Data], by norm_num [observer11Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer12_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 12 j d e ∧ ∃ ins, mainInsertionList[11]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer12_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer12_all_recurrence_fields
  have hcap : ((observer12Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (12 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer12Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer12Panel0Data, observer12Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer12Panel0Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel0Data], by norm_num [observer12Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel1Data, observer12Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer12Panel1Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel1Data], by norm_num [observer12Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel2Data, observer12Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer12Panel2Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel2Data], by norm_num [observer12Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel3Data, observer12Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer12Panel3Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel3Data], by norm_num [observer12Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel4Data, observer12Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer12Panel4Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel4Data], by norm_num [observer12Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel5Data, observer12Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer12Panel5Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel5Data], by norm_num [observer12Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel6Data, observer12Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer12Panel6Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel6Data], by norm_num [observer12Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer12Panel7Data, observer12Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer12Panel7Data.covarianceCap = observer12Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer12Panel7Data], by norm_num [observer12Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer13_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 13 j d e ∧ ∃ ins, mainInsertionList[12]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer13_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer13_all_recurrence_fields
  have hcap : ((observer13Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (13 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer13Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer13Panel0Data, observer13Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer13Panel0Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel0Data], by norm_num [observer13Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel1Data, observer13Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer13Panel1Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel1Data], by norm_num [observer13Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel2Data, observer13Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer13Panel2Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel2Data], by norm_num [observer13Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel3Data, observer13Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer13Panel3Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel3Data], by norm_num [observer13Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel4Data, observer13Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer13Panel4Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel4Data], by norm_num [observer13Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel5Data, observer13Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer13Panel5Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel5Data], by norm_num [observer13Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel6Data, observer13Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer13Panel6Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel6Data], by norm_num [observer13Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer13Panel7Data, observer13Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer13Panel7Data.covarianceCap = observer13Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer13Panel7Data], by norm_num [observer13Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer14_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 14 j d e ∧ ∃ ins, mainInsertionList[13]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer14_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer14_all_recurrence_fields
  have hcap : ((observer14Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (14 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer14Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer14Panel0Data, observer14Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer14Panel0Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel0Data], by norm_num [observer14Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel1Data, observer14Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer14Panel1Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel1Data], by norm_num [observer14Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel2Data, observer14Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer14Panel2Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel2Data], by norm_num [observer14Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel3Data, observer14Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer14Panel3Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel3Data], by norm_num [observer14Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel4Data, observer14Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer14Panel4Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel4Data], by norm_num [observer14Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel5Data, observer14Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer14Panel5Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel5Data], by norm_num [observer14Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel6Data, observer14Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer14Panel6Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel6Data], by norm_num [observer14Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer14Panel7Data, observer14Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer14Panel7Data.covarianceCap = observer14Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer14Panel7Data], by norm_num [observer14Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer15_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 15 j d e ∧ ∃ ins, mainInsertionList[14]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer15_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer15_all_recurrence_fields
  have hcap : ((observer15Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (15 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer15Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer15Panel0Data, observer15Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer15Panel0Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel0Data], by norm_num [observer15Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel1Data, observer15Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer15Panel1Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel1Data], by norm_num [observer15Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel2Data, observer15Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer15Panel2Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel2Data], by norm_num [observer15Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel3Data, observer15Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer15Panel3Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel3Data], by norm_num [observer15Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel4Data, observer15Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer15Panel4Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel4Data], by norm_num [observer15Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel5Data, observer15Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer15Panel5Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel5Data], by norm_num [observer15Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel6Data, observer15Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer15Panel6Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel6Data], by norm_num [observer15Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer15Panel7Data, observer15Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer15Panel7Data.covarianceCap = observer15Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer15Panel7Data], by norm_num [observer15Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer16_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 16 j d e ∧ ∃ ins, mainInsertionList[15]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer16_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer16_all_recurrence_fields
  have hcap : ((observer16Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (16 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer16Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer16Panel0Data, observer16Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer16Panel0Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel0Data], by norm_num [observer16Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel1Data, observer16Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer16Panel1Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel1Data], by norm_num [observer16Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel2Data, observer16Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer16Panel2Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel2Data], by norm_num [observer16Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel3Data, observer16Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer16Panel3Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel3Data], by norm_num [observer16Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel4Data, observer16Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer16Panel4Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel4Data], by norm_num [observer16Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel5Data, observer16Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer16Panel5Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel5Data], by norm_num [observer16Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel6Data, observer16Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer16Panel6Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel6Data], by norm_num [observer16Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer16Panel7Data, observer16Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer16Panel7Data.covarianceCap = observer16Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer16Panel7Data], by norm_num [observer16Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer17_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 17 j d e ∧ ∃ ins, mainInsertionList[16]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer17_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer17_all_recurrence_fields
  have hcap : ((observer17Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (17 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer17Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer17Panel0Data, observer17Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer17Panel0Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel0Data], by norm_num [observer17Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel1Data, observer17Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer17Panel1Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel1Data], by norm_num [observer17Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel2Data, observer17Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer17Panel2Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel2Data], by norm_num [observer17Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel3Data, observer17Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer17Panel3Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel3Data], by norm_num [observer17Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel4Data, observer17Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer17Panel4Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel4Data], by norm_num [observer17Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel5Data, observer17Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer17Panel5Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel5Data], by norm_num [observer17Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel6Data, observer17Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer17Panel6Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel6Data], by norm_num [observer17Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer17Panel7Data, observer17Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer17Panel7Data.covarianceCap = observer17Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer17Panel7Data], by norm_num [observer17Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer18_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 18 j d e ∧ ∃ ins, mainInsertionList[17]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer18_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer18_all_recurrence_fields
  have hcap : ((observer18Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (18 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer18Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer18Panel0Data, observer18Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer18Panel0Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel0Data], by norm_num [observer18Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel1Data, observer18Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer18Panel1Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel1Data], by norm_num [observer18Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel2Data, observer18Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer18Panel2Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel2Data], by norm_num [observer18Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel3Data, observer18Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer18Panel3Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel3Data], by norm_num [observer18Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel4Data, observer18Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer18Panel4Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel4Data], by norm_num [observer18Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel5Data, observer18Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer18Panel5Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel5Data], by norm_num [observer18Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel6Data, observer18Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer18Panel6Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel6Data], by norm_num [observer18Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer18Panel7Data, observer18Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer18Panel7Data.covarianceCap = observer18Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer18Panel7Data], by norm_num [observer18Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer19_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 19 j d e ∧ ∃ ins, mainInsertionList[18]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer19_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer19_all_recurrence_fields
  have hcap : ((observer19Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (19 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer19Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer19Panel0Data, observer19Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer19Panel0Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel0Data], by norm_num [observer19Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel1Data, observer19Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer19Panel1Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel1Data], by norm_num [observer19Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel2Data, observer19Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer19Panel2Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel2Data], by norm_num [observer19Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel3Data, observer19Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer19Panel3Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel3Data], by norm_num [observer19Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel4Data, observer19Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer19Panel4Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel4Data], by norm_num [observer19Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel5Data, observer19Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer19Panel5Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel5Data], by norm_num [observer19Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel6Data, observer19Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer19Panel6Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel6Data], by norm_num [observer19Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer19Panel7Data, observer19Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer19Panel7Data.covarianceCap = observer19Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer19Panel7Data], by norm_num [observer19Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer20_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 20 j d e ∧ ∃ ins, mainInsertionList[19]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer20_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer20_all_recurrence_fields
  have hcap : ((observer20Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (20 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer20Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer20Panel0Data, observer20Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer20Panel0Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel0Data], by norm_num [observer20Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel1Data, observer20Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer20Panel1Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel1Data], by norm_num [observer20Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel2Data, observer20Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer20Panel2Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel2Data], by norm_num [observer20Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel3Data, observer20Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer20Panel3Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel3Data], by norm_num [observer20Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel4Data, observer20Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer20Panel4Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel4Data], by norm_num [observer20Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel5Data, observer20Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer20Panel5Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel5Data], by norm_num [observer20Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel6Data, observer20Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer20Panel6Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel6Data], by norm_num [observer20Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer20Panel7Data, observer20Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer20Panel7Data.covarianceCap = observer20Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer20Panel7Data], by norm_num [observer20Panel7Data]⟩,
      _, rfl, rfl⟩


end ASDExplicitGamma.Main

end
