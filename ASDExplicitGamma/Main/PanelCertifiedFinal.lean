module

public import ASDExplicitGamma.Main.PanelCertifiedB

/-! Instantiation of the certificate leaves at all 40 observers and 8 panels:
each panel's data and endpoints are tied to the observer-independent prefixes, the covariance cap
`q_{k-1}`, and the panel's time interval `[j/8, (j+1)/8]`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.MainReturnCertificate

theorem panel_certified (k j : ℕ) (h1 : 1 ≤ k) (h40 : k ≤ 40) (hj : j < 8) :
    ∃ d e, PanelCertified' k j d e ∧ ∃ ins, mainInsertionList[k - 1]? = some ins ∧
      ins.panels[j]? = some e := by
  interval_cases k
  · exact observer1_certified j hj
  · exact observer2_certified j hj
  · exact observer3_certified j hj
  · exact observer4_certified j hj
  · exact observer5_certified j hj
  · exact observer6_certified j hj
  · exact observer7_certified j hj
  · exact observer8_certified j hj
  · exact observer9_certified j hj
  · exact observer10_certified j hj
  · exact observer11_certified j hj
  · exact observer12_certified j hj
  · exact observer13_certified j hj
  · exact observer14_certified j hj
  · exact observer15_certified j hj
  · exact observer16_certified j hj
  · exact observer17_certified j hj
  · exact observer18_certified j hj
  · exact observer19_certified j hj
  · exact observer20_certified j hj
  · exact observer21_certified j hj
  · exact observer22_certified j hj
  · exact observer23_certified j hj
  · exact observer24_certified j hj
  · exact observer25_certified j hj
  · exact observer26_certified j hj
  · exact observer27_certified j hj
  · exact observer28_certified j hj
  · exact observer29_certified j hj
  · exact observer30_certified j hj
  · exact observer31_certified j hj
  · exact observer32_certified j hj
  · exact observer33_certified j hj
  · exact observer34_certified j hj
  · exact observer35_certified j hj
  · exact observer36_certified j hj
  · exact observer37_certified j hj
  · exact observer38_certified j hj
  · exact observer39_certified j hj
  · exact observer40_certified j hj

end ASDExplicitGamma.Main

end
