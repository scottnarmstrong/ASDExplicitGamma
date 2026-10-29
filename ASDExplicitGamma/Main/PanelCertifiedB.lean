module

public import ASDExplicitGamma.Main.PanelCertified

/-! Instantiation of the certificate leaves at all 40 observers and 8 panels:
each panel's data and endpoints are tied to the observer-independent prefixes, the covariance cap
`q_{k-1}`, and the panel's time interval `[j/8, (j+1)/8]`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.MainReturnCertificate

theorem observer21_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 21 j d e ∧ ∃ ins, mainInsertionList[20]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer21_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer21_all_recurrence_fields
  have hcap : ((observer21Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (21 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer21Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer21Panel0Data, observer21Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer21Panel0Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel0Data], by norm_num [observer21Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel1Data, observer21Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer21Panel1Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel1Data], by norm_num [observer21Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel2Data, observer21Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer21Panel2Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel2Data], by norm_num [observer21Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel3Data, observer21Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer21Panel3Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel3Data], by norm_num [observer21Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel4Data, observer21Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer21Panel4Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel4Data], by norm_num [observer21Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel5Data, observer21Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer21Panel5Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel5Data], by norm_num [observer21Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel6Data, observer21Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer21Panel6Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel6Data], by norm_num [observer21Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer21Panel7Data, observer21Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer21Panel7Data.covarianceCap = observer21Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer21Panel7Data], by norm_num [observer21Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer22_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 22 j d e ∧ ∃ ins, mainInsertionList[21]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer22_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer22_all_recurrence_fields
  have hcap : ((observer22Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (22 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer22Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer22Panel0Data, observer22Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer22Panel0Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel0Data], by norm_num [observer22Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel1Data, observer22Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer22Panel1Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel1Data], by norm_num [observer22Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel2Data, observer22Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer22Panel2Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel2Data], by norm_num [observer22Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel3Data, observer22Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer22Panel3Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel3Data], by norm_num [observer22Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel4Data, observer22Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer22Panel4Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel4Data], by norm_num [observer22Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel5Data, observer22Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer22Panel5Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel5Data], by norm_num [observer22Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel6Data, observer22Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer22Panel6Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel6Data], by norm_num [observer22Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer22Panel7Data, observer22Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer22Panel7Data.covarianceCap = observer22Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer22Panel7Data], by norm_num [observer22Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer23_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 23 j d e ∧ ∃ ins, mainInsertionList[22]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer23_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer23_all_recurrence_fields
  have hcap : ((observer23Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (23 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer23Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer23Panel0Data, observer23Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer23Panel0Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel0Data], by norm_num [observer23Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel1Data, observer23Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer23Panel1Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel1Data], by norm_num [observer23Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel2Data, observer23Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer23Panel2Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel2Data], by norm_num [observer23Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel3Data, observer23Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer23Panel3Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel3Data], by norm_num [observer23Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel4Data, observer23Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer23Panel4Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel4Data], by norm_num [observer23Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel5Data, observer23Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer23Panel5Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel5Data], by norm_num [observer23Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel6Data, observer23Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer23Panel6Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel6Data], by norm_num [observer23Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer23Panel7Data, observer23Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer23Panel7Data.covarianceCap = observer23Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer23Panel7Data], by norm_num [observer23Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer24_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 24 j d e ∧ ∃ ins, mainInsertionList[23]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer24_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer24_all_recurrence_fields
  have hcap : ((observer24Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (24 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer24Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer24Panel0Data, observer24Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer24Panel0Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel0Data], by norm_num [observer24Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel1Data, observer24Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer24Panel1Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel1Data], by norm_num [observer24Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel2Data, observer24Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer24Panel2Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel2Data], by norm_num [observer24Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel3Data, observer24Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer24Panel3Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel3Data], by norm_num [observer24Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel4Data, observer24Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer24Panel4Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel4Data], by norm_num [observer24Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel5Data, observer24Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer24Panel5Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel5Data], by norm_num [observer24Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel6Data, observer24Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer24Panel6Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel6Data], by norm_num [observer24Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer24Panel7Data, observer24Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer24Panel7Data.covarianceCap = observer24Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer24Panel7Data], by norm_num [observer24Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer25_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 25 j d e ∧ ∃ ins, mainInsertionList[24]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer25_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer25_all_recurrence_fields
  have hcap : ((observer25Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (25 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer25Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer25Panel0Data, observer25Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer25Panel0Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel0Data], by norm_num [observer25Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel1Data, observer25Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer25Panel1Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel1Data], by norm_num [observer25Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel2Data, observer25Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer25Panel2Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel2Data], by norm_num [observer25Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel3Data, observer25Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer25Panel3Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel3Data], by norm_num [observer25Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel4Data, observer25Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer25Panel4Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel4Data], by norm_num [observer25Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel5Data, observer25Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer25Panel5Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel5Data], by norm_num [observer25Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel6Data, observer25Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer25Panel6Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel6Data], by norm_num [observer25Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer25Panel7Data, observer25Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer25Panel7Data.covarianceCap = observer25Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer25Panel7Data], by norm_num [observer25Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer26_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 26 j d e ∧ ∃ ins, mainInsertionList[25]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer26_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer26_all_recurrence_fields
  have hcap : ((observer26Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (26 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer26Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer26Panel0Data, observer26Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer26Panel0Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel0Data], by norm_num [observer26Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel1Data, observer26Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer26Panel1Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel1Data], by norm_num [observer26Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel2Data, observer26Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer26Panel2Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel2Data], by norm_num [observer26Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel3Data, observer26Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer26Panel3Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel3Data], by norm_num [observer26Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel4Data, observer26Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer26Panel4Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel4Data], by norm_num [observer26Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel5Data, observer26Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer26Panel5Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel5Data], by norm_num [observer26Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel6Data, observer26Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer26Panel6Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel6Data], by norm_num [observer26Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer26Panel7Data, observer26Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer26Panel7Data.covarianceCap = observer26Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer26Panel7Data], by norm_num [observer26Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer27_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 27 j d e ∧ ∃ ins, mainInsertionList[26]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer27_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer27_all_recurrence_fields
  have hcap : ((observer27Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (27 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer27Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer27Panel0Data, observer27Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer27Panel0Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel0Data], by norm_num [observer27Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel1Data, observer27Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer27Panel1Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel1Data], by norm_num [observer27Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel2Data, observer27Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer27Panel2Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel2Data], by norm_num [observer27Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel3Data, observer27Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer27Panel3Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel3Data], by norm_num [observer27Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel4Data, observer27Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer27Panel4Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel4Data], by norm_num [observer27Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel5Data, observer27Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer27Panel5Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel5Data], by norm_num [observer27Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel6Data, observer27Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer27Panel6Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel6Data], by norm_num [observer27Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer27Panel7Data, observer27Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer27Panel7Data.covarianceCap = observer27Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer27Panel7Data], by norm_num [observer27Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer28_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 28 j d e ∧ ∃ ins, mainInsertionList[27]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer28_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer28_all_recurrence_fields
  have hcap : ((observer28Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (28 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer28Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer28Panel0Data, observer28Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer28Panel0Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel0Data], by norm_num [observer28Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel1Data, observer28Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer28Panel1Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel1Data], by norm_num [observer28Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel2Data, observer28Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer28Panel2Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel2Data], by norm_num [observer28Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel3Data, observer28Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer28Panel3Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel3Data], by norm_num [observer28Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel4Data, observer28Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer28Panel4Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel4Data], by norm_num [observer28Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel5Data, observer28Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer28Panel5Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel5Data], by norm_num [observer28Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel6Data, observer28Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer28Panel6Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel6Data], by norm_num [observer28Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer28Panel7Data, observer28Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer28Panel7Data.covarianceCap = observer28Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer28Panel7Data], by norm_num [observer28Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer29_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 29 j d e ∧ ∃ ins, mainInsertionList[28]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer29_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer29_all_recurrence_fields
  have hcap : ((observer29Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (29 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer29Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer29Panel0Data, observer29Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer29Panel0Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel0Data], by norm_num [observer29Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel1Data, observer29Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer29Panel1Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel1Data], by norm_num [observer29Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel2Data, observer29Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer29Panel2Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel2Data], by norm_num [observer29Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel3Data, observer29Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer29Panel3Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel3Data], by norm_num [observer29Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel4Data, observer29Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer29Panel4Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel4Data], by norm_num [observer29Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel5Data, observer29Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer29Panel5Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel5Data], by norm_num [observer29Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel6Data, observer29Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer29Panel6Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel6Data], by norm_num [observer29Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer29Panel7Data, observer29Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer29Panel7Data.covarianceCap = observer29Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer29Panel7Data], by norm_num [observer29Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer30_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 30 j d e ∧ ∃ ins, mainInsertionList[29]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer30_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer30_all_recurrence_fields
  have hcap : ((observer30Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (30 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer30Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer30Panel0Data, observer30Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer30Panel0Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel0Data], by norm_num [observer30Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel1Data, observer30Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer30Panel1Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel1Data], by norm_num [observer30Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel2Data, observer30Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer30Panel2Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel2Data], by norm_num [observer30Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel3Data, observer30Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer30Panel3Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel3Data], by norm_num [observer30Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel4Data, observer30Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer30Panel4Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel4Data], by norm_num [observer30Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel5Data, observer30Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer30Panel5Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel5Data], by norm_num [observer30Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel6Data, observer30Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer30Panel6Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel6Data], by norm_num [observer30Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer30Panel7Data, observer30Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer30Panel7Data.covarianceCap = observer30Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer30Panel7Data], by norm_num [observer30Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer31_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 31 j d e ∧ ∃ ins, mainInsertionList[30]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer31_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer31_all_recurrence_fields
  have hcap : ((observer31Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (31 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer31Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer31Panel0Data, observer31Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer31Panel0Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel0Data], by norm_num [observer31Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel1Data, observer31Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer31Panel1Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel1Data], by norm_num [observer31Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel2Data, observer31Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer31Panel2Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel2Data], by norm_num [observer31Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel3Data, observer31Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer31Panel3Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel3Data], by norm_num [observer31Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel4Data, observer31Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer31Panel4Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel4Data], by norm_num [observer31Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel5Data, observer31Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer31Panel5Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel5Data], by norm_num [observer31Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel6Data, observer31Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer31Panel6Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel6Data], by norm_num [observer31Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer31Panel7Data, observer31Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer31Panel7Data.covarianceCap = observer31Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer31Panel7Data], by norm_num [observer31Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer32_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 32 j d e ∧ ∃ ins, mainInsertionList[31]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer32_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer32_all_recurrence_fields
  have hcap : ((observer32Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (32 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer32Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer32Panel0Data, observer32Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer32Panel0Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel0Data], by norm_num [observer32Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel1Data, observer32Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer32Panel1Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel1Data], by norm_num [observer32Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel2Data, observer32Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer32Panel2Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel2Data], by norm_num [observer32Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel3Data, observer32Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer32Panel3Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel3Data], by norm_num [observer32Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel4Data, observer32Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer32Panel4Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel4Data], by norm_num [observer32Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel5Data, observer32Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer32Panel5Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel5Data], by norm_num [observer32Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel6Data, observer32Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer32Panel6Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel6Data], by norm_num [observer32Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer32Panel7Data, observer32Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer32Panel7Data.covarianceCap = observer32Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer32Panel7Data], by norm_num [observer32Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer33_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 33 j d e ∧ ∃ ins, mainInsertionList[32]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer33_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer33_all_recurrence_fields
  have hcap : ((observer33Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (33 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer33Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer33Panel0Data, observer33Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer33Panel0Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel0Data], by norm_num [observer33Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel1Data, observer33Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer33Panel1Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel1Data], by norm_num [observer33Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel2Data, observer33Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer33Panel2Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel2Data], by norm_num [observer33Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel3Data, observer33Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer33Panel3Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel3Data], by norm_num [observer33Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel4Data, observer33Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer33Panel4Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel4Data], by norm_num [observer33Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel5Data, observer33Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer33Panel5Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel5Data], by norm_num [observer33Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel6Data, observer33Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer33Panel6Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel6Data], by norm_num [observer33Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer33Panel7Data, observer33Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer33Panel7Data.covarianceCap = observer33Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer33Panel7Data], by norm_num [observer33Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer34_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 34 j d e ∧ ∃ ins, mainInsertionList[33]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer34_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer34_all_recurrence_fields
  have hcap : ((observer34Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (34 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer34Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer34Panel0Data, observer34Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer34Panel0Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel0Data], by norm_num [observer34Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel1Data, observer34Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer34Panel1Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel1Data], by norm_num [observer34Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel2Data, observer34Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer34Panel2Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel2Data], by norm_num [observer34Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel3Data, observer34Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer34Panel3Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel3Data], by norm_num [observer34Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel4Data, observer34Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer34Panel4Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel4Data], by norm_num [observer34Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel5Data, observer34Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer34Panel5Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel5Data], by norm_num [observer34Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel6Data, observer34Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer34Panel6Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel6Data], by norm_num [observer34Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer34Panel7Data, observer34Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer34Panel7Data.covarianceCap = observer34Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer34Panel7Data], by norm_num [observer34Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer35_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 35 j d e ∧ ∃ ins, mainInsertionList[34]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer35_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer35_all_recurrence_fields
  have hcap : ((observer35Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (35 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer35Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer35Panel0Data, observer35Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer35Panel0Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel0Data], by norm_num [observer35Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel1Data, observer35Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer35Panel1Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel1Data], by norm_num [observer35Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel2Data, observer35Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer35Panel2Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel2Data], by norm_num [observer35Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel3Data, observer35Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer35Panel3Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel3Data], by norm_num [observer35Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel4Data, observer35Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer35Panel4Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel4Data], by norm_num [observer35Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel5Data, observer35Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer35Panel5Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel5Data], by norm_num [observer35Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel6Data, observer35Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer35Panel6Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel6Data], by norm_num [observer35Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer35Panel7Data, observer35Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer35Panel7Data.covarianceCap = observer35Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer35Panel7Data], by norm_num [observer35Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer36_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 36 j d e ∧ ∃ ins, mainInsertionList[35]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer36_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer36_all_recurrence_fields
  have hcap : ((observer36Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (36 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer36Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer36Panel0Data, observer36Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer36Panel0Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel0Data], by norm_num [observer36Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel1Data, observer36Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer36Panel1Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel1Data], by norm_num [observer36Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel2Data, observer36Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer36Panel2Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel2Data], by norm_num [observer36Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel3Data, observer36Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer36Panel3Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel3Data], by norm_num [observer36Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel4Data, observer36Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer36Panel4Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel4Data], by norm_num [observer36Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel5Data, observer36Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer36Panel5Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel5Data], by norm_num [observer36Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel6Data, observer36Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer36Panel6Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel6Data], by norm_num [observer36Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer36Panel7Data, observer36Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer36Panel7Data.covarianceCap = observer36Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer36Panel7Data], by norm_num [observer36Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer37_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 37 j d e ∧ ∃ ins, mainInsertionList[36]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer37_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer37_all_recurrence_fields
  have hcap : ((observer37Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (37 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer37Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer37Panel0Data, observer37Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer37Panel0Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel0Data], by norm_num [observer37Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel1Data, observer37Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer37Panel1Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel1Data], by norm_num [observer37Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel2Data, observer37Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer37Panel2Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel2Data], by norm_num [observer37Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel3Data, observer37Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer37Panel3Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel3Data], by norm_num [observer37Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel4Data, observer37Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer37Panel4Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel4Data], by norm_num [observer37Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel5Data, observer37Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer37Panel5Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel5Data], by norm_num [observer37Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel6Data, observer37Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer37Panel6Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel6Data], by norm_num [observer37Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer37Panel7Data, observer37Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer37Panel7Data.covarianceCap = observer37Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer37Panel7Data], by norm_num [observer37Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer38_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 38 j d e ∧ ∃ ins, mainInsertionList[37]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer38_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer38_all_recurrence_fields
  have hcap : ((observer38Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (38 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer38Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer38Panel0Data, observer38Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer38Panel0Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel0Data], by norm_num [observer38Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel1Data, observer38Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer38Panel1Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel1Data], by norm_num [observer38Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel2Data, observer38Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer38Panel2Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel2Data], by norm_num [observer38Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel3Data, observer38Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer38Panel3Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel3Data], by norm_num [observer38Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel4Data, observer38Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer38Panel4Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel4Data], by norm_num [observer38Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel5Data, observer38Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer38Panel5Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel5Data], by norm_num [observer38Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel6Data, observer38Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer38Panel6Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel6Data], by norm_num [observer38Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer38Panel7Data, observer38Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer38Panel7Data.covarianceCap = observer38Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer38Panel7Data], by norm_num [observer38Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer39_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 39 j d e ∧ ∃ ins, mainInsertionList[38]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer39_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer39_all_recurrence_fields
  have hcap : ((observer39Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (39 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer39Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer39Panel0Data, observer39Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer39Panel0Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel0Data], by norm_num [observer39Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel1Data, observer39Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer39Panel1Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel1Data], by norm_num [observer39Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel2Data, observer39Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer39Panel2Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel2Data], by norm_num [observer39Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel3Data, observer39Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer39Panel3Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel3Data], by norm_num [observer39Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel4Data, observer39Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer39Panel4Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel4Data], by norm_num [observer39Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel5Data, observer39Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer39Panel5Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel5Data], by norm_num [observer39Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel6Data, observer39Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer39Panel6Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel6Data], by norm_num [observer39Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer39Panel7Data, observer39Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer39Panel7Data.covarianceCap = observer39Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer39Panel7Data], by norm_num [observer39Panel7Data]⟩,
      _, rfl, rfl⟩

theorem observer40_certified (j : ℕ) (hj : j < 8) :
    ∃ d e, PanelCertified' 40 j d e ∧ ∃ ins, mainInsertionList[39]? = some ins ∧
      ins.panels[j]? = some e := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := observer40_all_panel_formula_bounds
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -⟩ := observer40_all_recurrence_fields
  have hcap : ((observer40Panel0Data.covarianceCap : ℚ) : ℝ) =
      mainAffineFlatBoundaryCapQ (40 - 1) := by
    simp only [mainAffineFlatBoundaryCapQ, observer40Panel0Data]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  interval_cases j
  · exact ⟨observer40Panel0Data, observer40Panel0Endpoints,
      ⟨b0, r0, rfl, rfl, rfl,
        by rw [show observer40Panel0Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel0Data], by norm_num [observer40Panel0Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel1Data, observer40Panel1Endpoints,
      ⟨b1, r1, rfl, rfl, rfl,
        by rw [show observer40Panel1Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel1Data], by norm_num [observer40Panel1Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel2Data, observer40Panel2Endpoints,
      ⟨b2, r2, rfl, rfl, rfl,
        by rw [show observer40Panel2Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel2Data], by norm_num [observer40Panel2Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel3Data, observer40Panel3Endpoints,
      ⟨b3, r3, rfl, rfl, rfl,
        by rw [show observer40Panel3Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel3Data], by norm_num [observer40Panel3Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel4Data, observer40Panel4Endpoints,
      ⟨b4, r4, rfl, rfl, rfl,
        by rw [show observer40Panel4Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel4Data], by norm_num [observer40Panel4Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel5Data, observer40Panel5Endpoints,
      ⟨b5, r5, rfl, rfl, rfl,
        by rw [show observer40Panel5Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel5Data], by norm_num [observer40Panel5Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel6Data, observer40Panel6Endpoints,
      ⟨b6, r6, rfl, rfl, rfl,
        by rw [show observer40Panel6Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel6Data], by norm_num [observer40Panel6Data]⟩,
      _, rfl, rfl⟩
  · exact ⟨observer40Panel7Data, observer40Panel7Endpoints,
      ⟨b7, r7, rfl, rfl, rfl,
        by rw [show observer40Panel7Data.covarianceCap = observer40Panel0Data.covarianceCap from rfl]; exact hcap,
        by norm_num [observer40Panel7Data], by norm_num [observer40Panel7Data]⟩,
      _, rfl, rfl⟩


end ASDExplicitGamma.Main

end
