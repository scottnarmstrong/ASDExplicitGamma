module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0480Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 489).2.2,
  nativeAvg*nativeA+(nativeRaw 490).2.2,
  nativeAvg*nativeA+(nativeRaw 491).2.2,
  nativeAvg*nativeA+(nativeRaw 492).2.2,
  nativeAvg*nativeA+(nativeRaw 493).2.2,
  nativeAvg*nativeA+(nativeRaw 494).2.2,
  nativeAvg*nativeA+(nativeRaw 495).2.2,
  nativeAvg*nativeA+(nativeRaw 496).2.2,
  nativeAvg*nativeA+(nativeRaw 497).2.2,
  nativeAvg*nativeA+(nativeRaw 498).2.2,
  nativeAvg*nativeA+(nativeRaw 499).2.2,
  nativeAvg*nativeA+(nativeRaw 500).2.2,
  nativeAvg*nativeA+(nativeRaw 501).2.2,
  nativeAvg*nativeA+(nativeRaw 502).2.2,
  nativeAvg*nativeA+(nativeRaw 503).2.2,
  nativeAvg*nativeA+(nativeRaw 504).2.2,
  nativeAvg*nativeA+(nativeRaw 505).2.2,
  nativeAvg*nativeA+(nativeRaw 506).2.2,
  nativeAvg*nativeA+(nativeRaw 507).2.2,
  nativeAvg*nativeA+(nativeRaw 508).2.2,
  nativeAvg*nativeA+(nativeRaw 509).2.2,
  nativeAvg*nativeA+(nativeRaw 510).2.2,
  nativeAvg*nativeA+(nativeRaw 511).2.2,
  nativeAvg*nativeA+(nativeRaw 512).2.2,
  nativeAvg*nativeA+(nativeRaw 513).2.2,
  nativeAvg*nativeA+(nativeRaw 514).2.2,
  nativeAvg*nativeA+(nativeRaw 515).2.2,
  nativeAvg*nativeA+(nativeRaw 516).2.2,
  nativeAvg*nativeA+(nativeRaw 517).2.2,
  nativeAvg*nativeA+(nativeRaw 518).2.2,
  nativeAvg*nativeA+(nativeRaw 519).2.2,
  nativeAvg*nativeA+(nativeRaw 520).2.2
]

def nativeHistoryStrong0480Start : ℚ × ℚ := ((221942436486919759978175313407914436355682164484339807322373132619/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(475753132918139042877879089438378954029972567315987811414602532916617674852963901737201847024668897/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0480End : ℚ × ℚ := ((2275560403401475541316635205942694748700948209401832896534123111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789461253796271614670659144007991066277062023981452968825170772160861501/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0480Inputs_length : nativeHistoryStrong0480Inputs.length = 32 := rfl

theorem nativeHistoryStrong0480Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(489+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(489+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0480Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0480Inputs.getD i.val 0)*(nativeHistoryStrong0480Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0480_checked : nativeHistorySteps 9 480 32 nativeHistoryStrong0480Inputs nativeHistoryStrong0480Start = nativeHistoryStrong0480End := by
  decide +kernel

theorem nativeHistoryStrong0480Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0480Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0480Weight : nativeHistoryRatio^480 ≤ nativeHistoryStrong0480Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0480Real_bound : nativeHistoryReal 9 480 nativeHistoryStrong0480Inputs ≤ (nativeHistoryStrong0480End.2 : ℝ)-(nativeHistoryStrong0480Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0480Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0480Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0480Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0480Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0480Inputs.length) := nativeHistoryStrong0480Domains ⟨i,by simpa only [nativeHistoryStrong0480Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0480Inputs.length) := nativeHistoryStrong0480Roots ⟨i,by simpa only [nativeHistoryStrong0480Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0480Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 480 nativeHistoryStrong0480Inputs nativeHistoryStrong0480Start ht hd hr hw
  simpa only [nativeHistoryStrong0480Inputs_length,nativeHistoryStrong0480_checked] using hs

end ASDExplicitGamma.Numerics.Native
