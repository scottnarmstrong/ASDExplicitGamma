module

public import ASDExplicitGamma.Main.ErrorProfile

/-! Supporting slope of the actual full error formula at an interior anchor. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set Filter
open scoped Topology

/-- The source interior gates imply strict positivity of all three radicands. -/
theorem mainError_anchor_radicands (a H xi anchor : ℝ) (hH : 0 ≤ H)
    (ha : anchor < a) (hxi : mainBetaOld*anchor < xi) :
    ∀ i, 0 < mainErrorOffsets a H xi i - mainErrorRates i * anchor := by
  have haf : 0 < a-anchor := sub_pos.mpr ha
  have hHd := mainHd_nonneg hH
  have hb : 0 < mainBeta := by norm_num [mainBeta]
  have he : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
  intro i
  fin_cases i <;> norm_num [mainErrorOffsets, mainErrorRates]
  · have h : 0 < mainBeta*(a-anchor)+mainEpsNew*mainHd H := by positivity
    nlinarith only [h]
  · have h : 0 < mainBeta^2*(a-anchor)+(2*mainBeta*mainEpsNew+mainEpsNew^2)*mainHd H := by positivity
    nlinarith only [h]
  · exact hxi

end ASDExplicitGamma.Main
