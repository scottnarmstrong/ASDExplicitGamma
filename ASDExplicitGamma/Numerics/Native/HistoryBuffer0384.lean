module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0384Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 456).2.2,
  nativeAvg*nativeA+(nativeRaw 457).2.2,
  nativeAvg*nativeA+(nativeRaw 458).2.2,
  nativeAvg*nativeA+(nativeRaw 459).2.2,
  nativeAvg*nativeA+(nativeRaw 460).2.2,
  nativeAvg*nativeA+(nativeRaw 461).2.2,
  nativeAvg*nativeA+(nativeRaw 462).2.2,
  nativeAvg*nativeA+(nativeRaw 463).2.2,
  nativeAvg*nativeA+(nativeRaw 464).2.2
]

def nativeHistoryBuffer0384Start : ℚ × ℚ := ((411837879469487115546782955178815160158819774395295499779662072215120479/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(36603952314622765566753460834430145595681347998965503075686110281270262215323128799218818108715759/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0384End : ℚ × ℚ := ((675607232920920928789347869936852715201793472232371387794890463299287/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11713264740679284981361132479476321124227376286181433045673339099913397082705527481774101100296483917/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0384Inputs_length : nativeHistoryBuffer0384Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0384Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(433+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(433+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0384Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0384Inputs.getD i.val 0)*(nativeHistoryBuffer0384Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0384_checked : nativeHistorySteps 49 384 32 nativeHistoryBuffer0384Inputs nativeHistoryBuffer0384Start = nativeHistoryBuffer0384End := by
  decide +kernel

theorem nativeHistoryBuffer0384Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0384Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0384Weight : nativeHistoryRatio^384 ≤ nativeHistoryBuffer0384Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0384Real_bound : nativeHistoryReal 49 384 nativeHistoryBuffer0384Inputs ≤ (nativeHistoryBuffer0384End.2 : ℝ)-(nativeHistoryBuffer0384Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0384Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0384Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0384Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0384Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0384Inputs.length) := nativeHistoryBuffer0384Domains ⟨i,by simpa only [nativeHistoryBuffer0384Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0384Inputs.length) := nativeHistoryBuffer0384Roots ⟨i,by simpa only [nativeHistoryBuffer0384Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0384Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 384 nativeHistoryBuffer0384Inputs nativeHistoryBuffer0384Start ht hd hr hw
  simpa only [nativeHistoryBuffer0384Inputs_length,nativeHistoryBuffer0384_checked] using hs

end ASDExplicitGamma.Numerics.Native
