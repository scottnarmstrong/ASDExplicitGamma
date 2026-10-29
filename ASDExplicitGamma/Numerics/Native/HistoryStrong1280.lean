module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1280Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1289).2.2,
  nativeAvg*nativeA+(nativeRaw 1290).2.2,
  nativeAvg*nativeA+(nativeRaw 1291).2.2,
  nativeAvg*nativeA+(nativeRaw 1292).2.2,
  nativeAvg*nativeA+(nativeRaw 1293).2.2,
  nativeAvg*nativeA+(nativeRaw 1294).2.2
]

def nativeHistoryStrong1280Start : ℚ × ℚ := ((123506817/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1903012531672556171511516357757918557979056160801968373309087864727043026504440675879038281498429929/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1280End : ℚ × ℚ := ((91899217/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215132522203379491593511104511847/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1280Inputs_length : nativeHistoryStrong1280Inputs.length = 6 := rfl

theorem nativeHistoryStrong1280Domains : ∀ i : Fin 6, 0 ≤ (11/10)*(2*nativeGamma*(1289+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1289+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1280Roots : ∀ i : Fin 6, nativeRootValid ((nativeHistoryStrong1280Inputs.getD i.val 0)*(nativeHistoryStrong1280Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1280_checked : nativeHistorySteps 9 1280 6 nativeHistoryStrong1280Inputs nativeHistoryStrong1280Start = nativeHistoryStrong1280End := by
  decide +kernel

theorem nativeHistoryStrong1280Inputs_nonneg : ∀ i : Fin 6, 0 ≤ nativeHistoryStrong1280Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1280Weight : nativeHistoryRatio^1280 ≤ nativeHistoryStrong1280Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1280Real_bound : nativeHistoryReal 9 1280 nativeHistoryStrong1280Inputs ≤ (nativeHistoryStrong1280End.2 : ℝ)-(nativeHistoryStrong1280Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1280Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1280Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1280Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1280Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1280Inputs.length) := nativeHistoryStrong1280Domains ⟨i,by simpa only [nativeHistoryStrong1280Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1280Inputs.length) := nativeHistoryStrong1280Roots ⟨i,by simpa only [nativeHistoryStrong1280Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1280Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1280 nativeHistoryStrong1280Inputs nativeHistoryStrong1280Start ht hd hr hw
  simpa only [nativeHistoryStrong1280Inputs_length,nativeHistoryStrong1280_checked] using hs

end ASDExplicitGamma.Numerics.Native
