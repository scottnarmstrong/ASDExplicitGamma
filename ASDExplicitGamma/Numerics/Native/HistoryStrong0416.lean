module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0416Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 425).2.2,
  nativeAvg*nativeA+(nativeRaw 426).2.2,
  nativeAvg*nativeA+(nativeRaw 427).2.2,
  nativeAvg*nativeA+(nativeRaw 428).2.2,
  nativeAvg*nativeA+(nativeRaw 429).2.2,
  nativeAvg*nativeA+(nativeRaw 430).2.2,
  nativeAvg*nativeA+(nativeRaw 431).2.2,
  nativeAvg*nativeA+(nativeRaw 432).2.2,
  nativeAvg*nativeA+(nativeRaw 433).2.2,
  nativeAvg*nativeA+(nativeRaw 434).2.2,
  nativeAvg*nativeA+(nativeRaw 435).2.2,
  nativeAvg*nativeA+(nativeRaw 436).2.2,
  nativeAvg*nativeA+(nativeRaw 437).2.2,
  nativeAvg*nativeA+(nativeRaw 438).2.2,
  nativeAvg*nativeA+(nativeRaw 439).2.2,
  nativeAvg*nativeA+(nativeRaw 440).2.2,
  nativeAvg*nativeA+(nativeRaw 441).2.2,
  nativeAvg*nativeA+(nativeRaw 442).2.2,
  nativeAvg*nativeA+(nativeRaw 443).2.2,
  nativeAvg*nativeA+(nativeRaw 444).2.2,
  nativeAvg*nativeA+(nativeRaw 445).2.2,
  nativeAvg*nativeA+(nativeRaw 446).2.2,
  nativeAvg*nativeA+(nativeRaw 447).2.2,
  nativeAvg*nativeA+(nativeRaw 448).2.2,
  nativeAvg*nativeA+(nativeRaw 449).2.2,
  nativeAvg*nativeA+(nativeRaw 450).2.2,
  nativeAvg*nativeA+(nativeRaw 451).2.2,
  nativeAvg*nativeA+(nativeRaw 452).2.2,
  nativeAvg*nativeA+(nativeRaw 453).2.2,
  nativeAvg*nativeA+(nativeRaw 454).2.2,
  nativeAvg*nativeA+(nativeRaw 455).2.2,
  nativeAvg*nativeA+(nativeRaw 456).2.2
]

def nativeHistoryStrong0416Start : ℚ × ℚ := ((675607232920920928789347869936852715201793472232371387794890463299287/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395291775041821079883764316504992459835058247594335827591744203619036069879977/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0416End : ℚ × ℚ := ((86586926086637091678870978027611080834722316789952727645292792882353/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581785094730284692014473437228572704966399314186056614685313052687640622134559/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0416Inputs_length : nativeHistoryStrong0416Inputs.length = 32 := rfl

theorem nativeHistoryStrong0416Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(425+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(425+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0416Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0416Inputs.getD i.val 0)*(nativeHistoryStrong0416Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0416_checked : nativeHistorySteps 9 416 32 nativeHistoryStrong0416Inputs nativeHistoryStrong0416Start = nativeHistoryStrong0416End := by
  decide +kernel

theorem nativeHistoryStrong0416Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0416Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0416Weight : nativeHistoryRatio^416 ≤ nativeHistoryStrong0416Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0416Real_bound : nativeHistoryReal 9 416 nativeHistoryStrong0416Inputs ≤ (nativeHistoryStrong0416End.2 : ℝ)-(nativeHistoryStrong0416Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0416Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0416Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0416Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0416Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0416Inputs.length) := nativeHistoryStrong0416Domains ⟨i,by simpa only [nativeHistoryStrong0416Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0416Inputs.length) := nativeHistoryStrong0416Roots ⟨i,by simpa only [nativeHistoryStrong0416Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0416Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 416 nativeHistoryStrong0416Inputs nativeHistoryStrong0416Start ht hd hr hw
  simpa only [nativeHistoryStrong0416Inputs_length,nativeHistoryStrong0416_checked] using hs

end ASDExplicitGamma.Numerics.Native
