module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0384Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 393).2.2,
  nativeAvg*nativeA+(nativeRaw 394).2.2,
  nativeAvg*nativeA+(nativeRaw 395).2.2,
  nativeAvg*nativeA+(nativeRaw 396).2.2,
  nativeAvg*nativeA+(nativeRaw 397).2.2,
  nativeAvg*nativeA+(nativeRaw 398).2.2,
  nativeAvg*nativeA+(nativeRaw 399).2.2,
  nativeAvg*nativeA+(nativeRaw 400).2.2,
  nativeAvg*nativeA+(nativeRaw 401).2.2,
  nativeAvg*nativeA+(nativeRaw 402).2.2,
  nativeAvg*nativeA+(nativeRaw 403).2.2,
  nativeAvg*nativeA+(nativeRaw 404).2.2,
  nativeAvg*nativeA+(nativeRaw 405).2.2,
  nativeAvg*nativeA+(nativeRaw 406).2.2,
  nativeAvg*nativeA+(nativeRaw 407).2.2,
  nativeAvg*nativeA+(nativeRaw 408).2.2,
  nativeAvg*nativeA+(nativeRaw 409).2.2,
  nativeAvg*nativeA+(nativeRaw 410).2.2,
  nativeAvg*nativeA+(nativeRaw 411).2.2,
  nativeAvg*nativeA+(nativeRaw 412).2.2,
  nativeAvg*nativeA+(nativeRaw 413).2.2,
  nativeAvg*nativeA+(nativeRaw 414).2.2,
  nativeAvg*nativeA+(nativeRaw 415).2.2,
  nativeAvg*nativeA+(nativeRaw 416).2.2,
  nativeAvg*nativeA+(nativeRaw 417).2.2,
  nativeAvg*nativeA+(nativeRaw 418).2.2,
  nativeAvg*nativeA+(nativeRaw 419).2.2,
  nativeAvg*nativeA+(nativeRaw 420).2.2,
  nativeAvg*nativeA+(nativeRaw 421).2.2,
  nativeAvg*nativeA+(nativeRaw 422).2.2,
  nativeAvg*nativeA+(nativeRaw 423).2.2,
  nativeAvg*nativeA+(nativeRaw 424).2.2
]

def nativeHistoryStrong0384Start : ℚ × ℚ := ((411837879469487115546782955178815160158819774395295499779662072215120479/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557476969809454735013732682799506210542655649663624675482713545055651782422245481/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0384End : ℚ × ℚ := ((675607232920920928789347869936852715201793472232371387794890463299287/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395291775041821079883764316504992459835058247594335827591744203619036069879977/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0384Inputs_length : nativeHistoryStrong0384Inputs.length = 32 := rfl

theorem nativeHistoryStrong0384Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(393+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(393+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0384Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0384Inputs.getD i.val 0)*(nativeHistoryStrong0384Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0384_checked : nativeHistorySteps 9 384 32 nativeHistoryStrong0384Inputs nativeHistoryStrong0384Start = nativeHistoryStrong0384End := by
  decide +kernel

theorem nativeHistoryStrong0384Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0384Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0384Weight : nativeHistoryRatio^384 ≤ nativeHistoryStrong0384Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0384Real_bound : nativeHistoryReal 9 384 nativeHistoryStrong0384Inputs ≤ (nativeHistoryStrong0384End.2 : ℝ)-(nativeHistoryStrong0384Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0384Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0384Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0384Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0384Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0384Inputs.length) := nativeHistoryStrong0384Domains ⟨i,by simpa only [nativeHistoryStrong0384Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0384Inputs.length) := nativeHistoryStrong0384Roots ⟨i,by simpa only [nativeHistoryStrong0384Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0384Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 384 nativeHistoryStrong0384Inputs nativeHistoryStrong0384Start ht hd hr hw
  simpa only [nativeHistoryStrong0384Inputs_length,nativeHistoryStrong0384_checked] using hs

end ASDExplicitGamma.Numerics.Native
