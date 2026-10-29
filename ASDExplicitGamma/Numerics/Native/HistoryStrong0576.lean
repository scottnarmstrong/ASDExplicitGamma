module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0576Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 585).2.2,
  nativeAvg*nativeA+(nativeRaw 586).2.2,
  nativeAvg*nativeA+(nativeRaw 587).2.2,
  nativeAvg*nativeA+(nativeRaw 588).2.2,
  nativeAvg*nativeA+(nativeRaw 589).2.2,
  nativeAvg*nativeA+(nativeRaw 590).2.2,
  nativeAvg*nativeA+(nativeRaw 591).2.2,
  nativeAvg*nativeA+(nativeRaw 592).2.2,
  nativeAvg*nativeA+(nativeRaw 593).2.2,
  nativeAvg*nativeA+(nativeRaw 594).2.2,
  nativeAvg*nativeA+(nativeRaw 595).2.2,
  nativeAvg*nativeA+(nativeRaw 596).2.2,
  nativeAvg*nativeA+(nativeRaw 597).2.2,
  nativeAvg*nativeA+(nativeRaw 598).2.2,
  nativeAvg*nativeA+(nativeRaw 599).2.2,
  nativeAvg*nativeA+(nativeRaw 600).2.2,
  nativeAvg*nativeA+(nativeRaw 601).2.2,
  nativeAvg*nativeA+(nativeRaw 602).2.2,
  nativeAvg*nativeA+(nativeRaw 603).2.2,
  nativeAvg*nativeA+(nativeRaw 604).2.2,
  nativeAvg*nativeA+(nativeRaw 605).2.2,
  nativeAvg*nativeA+(nativeRaw 606).2.2,
  nativeAvg*nativeA+(nativeRaw 607).2.2,
  nativeAvg*nativeA+(nativeRaw 608).2.2,
  nativeAvg*nativeA+(nativeRaw 609).2.2,
  nativeAvg*nativeA+(nativeRaw 610).2.2,
  nativeAvg*nativeA+(nativeRaw 611).2.2,
  nativeAvg*nativeA+(nativeRaw 612).2.2,
  nativeAvg*nativeA+(nativeRaw 613).2.2,
  nativeAvg*nativeA+(nativeRaw 614).2.2,
  nativeAvg*nativeA+(nativeRaw 615).2.2,
  nativeAvg*nativeA+(nativeRaw 616).2.2
]

def nativeHistoryStrong0576Start : ℚ × ℚ := ((59803198745587883394037968344665236371819882007316878155517/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428778790894394796392574662502953340673415408578547046148153201005412448340340633953/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0576End : ℚ × ℚ := ((306579023859253780951388211910455767918388101771680393813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789866593257713705939433948435494178076914559160986358201994289339/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0576Inputs_length : nativeHistoryStrong0576Inputs.length = 32 := rfl

theorem nativeHistoryStrong0576Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(585+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(585+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0576Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0576Inputs.getD i.val 0)*(nativeHistoryStrong0576Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0576_checked : nativeHistorySteps 9 576 32 nativeHistoryStrong0576Inputs nativeHistoryStrong0576Start = nativeHistoryStrong0576End := by
  decide +kernel

theorem nativeHistoryStrong0576Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0576Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0576Weight : nativeHistoryRatio^576 ≤ nativeHistoryStrong0576Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0576Real_bound : nativeHistoryReal 9 576 nativeHistoryStrong0576Inputs ≤ (nativeHistoryStrong0576End.2 : ℝ)-(nativeHistoryStrong0576Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0576Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0576Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0576Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0576Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0576Inputs.length) := nativeHistoryStrong0576Domains ⟨i,by simpa only [nativeHistoryStrong0576Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0576Inputs.length) := nativeHistoryStrong0576Roots ⟨i,by simpa only [nativeHistoryStrong0576Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0576Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 576 nativeHistoryStrong0576Inputs nativeHistoryStrong0576Start ht hd hr hw
  simpa only [nativeHistoryStrong0576Inputs_length,nativeHistoryStrong0576_checked] using hs

end ASDExplicitGamma.Numerics.Native
