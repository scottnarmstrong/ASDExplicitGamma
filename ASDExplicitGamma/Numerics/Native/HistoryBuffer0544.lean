module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0544Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 616).2.2,
  nativeAvg*nativeA+(nativeRaw 617).2.2,
  nativeAvg*nativeA+(nativeRaw 618).2.2,
  nativeAvg*nativeA+(nativeRaw 619).2.2,
  nativeAvg*nativeA+(nativeRaw 620).2.2,
  nativeAvg*nativeA+(nativeRaw 621).2.2,
  nativeAvg*nativeA+(nativeRaw 622).2.2,
  nativeAvg*nativeA+(nativeRaw 623).2.2,
  nativeAvg*nativeA+(nativeRaw 624).2.2
]

def nativeHistoryBuffer0544Start : ℚ × ℚ := ((2916395367810756253020280767694726678452625408466791919355183/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768686760125800696542065912481783478933511968258039276130744507582095853/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0544End : ℚ × ℚ := ((59803198745587883394037968344665236371819882007316878155517/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687239351416921221298584243345779512232462610228720246971288643772793/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0544Inputs_length : nativeHistoryBuffer0544Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0544Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(593+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(593+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0544Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0544Inputs.getD i.val 0)*(nativeHistoryBuffer0544Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0544_checked : nativeHistorySteps 49 544 32 nativeHistoryBuffer0544Inputs nativeHistoryBuffer0544Start = nativeHistoryBuffer0544End := by
  decide +kernel

theorem nativeHistoryBuffer0544Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0544Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0544Weight : nativeHistoryRatio^544 ≤ nativeHistoryBuffer0544Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0544Real_bound : nativeHistoryReal 49 544 nativeHistoryBuffer0544Inputs ≤ (nativeHistoryBuffer0544End.2 : ℝ)-(nativeHistoryBuffer0544Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0544Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0544Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0544Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0544Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0544Inputs.length) := nativeHistoryBuffer0544Domains ⟨i,by simpa only [nativeHistoryBuffer0544Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0544Inputs.length) := nativeHistoryBuffer0544Roots ⟨i,by simpa only [nativeHistoryBuffer0544Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0544Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 544 nativeHistoryBuffer0544Inputs nativeHistoryBuffer0544Start ht hd hr hw
  simpa only [nativeHistoryBuffer0544Inputs_length,nativeHistoryBuffer0544_checked] using hs

end ASDExplicitGamma.Numerics.Native
