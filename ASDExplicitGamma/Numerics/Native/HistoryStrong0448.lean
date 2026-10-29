module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0448Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 457).2.2,
  nativeAvg*nativeA+(nativeRaw 458).2.2,
  nativeAvg*nativeA+(nativeRaw 459).2.2,
  nativeAvg*nativeA+(nativeRaw 460).2.2,
  nativeAvg*nativeA+(nativeRaw 461).2.2,
  nativeAvg*nativeA+(nativeRaw 462).2.2,
  nativeAvg*nativeA+(nativeRaw 463).2.2,
  nativeAvg*nativeA+(nativeRaw 464).2.2,
  nativeAvg*nativeA+(nativeRaw 465).2.2,
  nativeAvg*nativeA+(nativeRaw 466).2.2,
  nativeAvg*nativeA+(nativeRaw 467).2.2,
  nativeAvg*nativeA+(nativeRaw 468).2.2,
  nativeAvg*nativeA+(nativeRaw 469).2.2,
  nativeAvg*nativeA+(nativeRaw 470).2.2,
  nativeAvg*nativeA+(nativeRaw 471).2.2,
  nativeAvg*nativeA+(nativeRaw 472).2.2,
  nativeAvg*nativeA+(nativeRaw 473).2.2,
  nativeAvg*nativeA+(nativeRaw 474).2.2,
  nativeAvg*nativeA+(nativeRaw 475).2.2,
  nativeAvg*nativeA+(nativeRaw 476).2.2,
  nativeAvg*nativeA+(nativeRaw 477).2.2,
  nativeAvg*nativeA+(nativeRaw 478).2.2,
  nativeAvg*nativeA+(nativeRaw 479).2.2,
  nativeAvg*nativeA+(nativeRaw 480).2.2,
  nativeAvg*nativeA+(nativeRaw 481).2.2,
  nativeAvg*nativeA+(nativeRaw 482).2.2,
  nativeAvg*nativeA+(nativeRaw 483).2.2,
  nativeAvg*nativeA+(nativeRaw 484).2.2,
  nativeAvg*nativeA+(nativeRaw 485).2.2,
  nativeAvg*nativeA+(nativeRaw 486).2.2,
  nativeAvg*nativeA+(nativeRaw 487).2.2,
  nativeAvg*nativeA+(nativeRaw 488).2.2
]

def nativeHistoryStrong0448Start : ℚ × ℚ := ((86586926086637091678870978027611080834722316789952727645292792882353/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581785094730284692014473437228572704966399314186056614685313052687640622134559/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0448End : ℚ × ℚ := ((221942436486919759978175313407914436355682164484339807322373132619/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(475753132918139042877879089438378954029972567315987811414602532916617674852963901737201847024668897/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0448Inputs_length : nativeHistoryStrong0448Inputs.length = 32 := rfl

theorem nativeHistoryStrong0448Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(457+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(457+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0448Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0448Inputs.getD i.val 0)*(nativeHistoryStrong0448Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0448_checked : nativeHistorySteps 9 448 32 nativeHistoryStrong0448Inputs nativeHistoryStrong0448Start = nativeHistoryStrong0448End := by
  decide +kernel

theorem nativeHistoryStrong0448Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0448Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0448Weight : nativeHistoryRatio^448 ≤ nativeHistoryStrong0448Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0448Real_bound : nativeHistoryReal 9 448 nativeHistoryStrong0448Inputs ≤ (nativeHistoryStrong0448End.2 : ℝ)-(nativeHistoryStrong0448Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0448Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0448Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0448Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0448Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0448Inputs.length) := nativeHistoryStrong0448Domains ⟨i,by simpa only [nativeHistoryStrong0448Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0448Inputs.length) := nativeHistoryStrong0448Roots ⟨i,by simpa only [nativeHistoryStrong0448Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0448Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 448 nativeHistoryStrong0448Inputs nativeHistoryStrong0448Start ht hd hr hw
  simpa only [nativeHistoryStrong0448Inputs_length,nativeHistoryStrong0448_checked] using hs

end ASDExplicitGamma.Numerics.Native
