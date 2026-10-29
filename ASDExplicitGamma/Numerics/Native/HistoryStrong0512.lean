module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0512Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 521).2.2,
  nativeAvg*nativeA+(nativeRaw 522).2.2,
  nativeAvg*nativeA+(nativeRaw 523).2.2,
  nativeAvg*nativeA+(nativeRaw 524).2.2,
  nativeAvg*nativeA+(nativeRaw 525).2.2,
  nativeAvg*nativeA+(nativeRaw 526).2.2,
  nativeAvg*nativeA+(nativeRaw 527).2.2,
  nativeAvg*nativeA+(nativeRaw 528).2.2,
  nativeAvg*nativeA+(nativeRaw 529).2.2,
  nativeAvg*nativeA+(nativeRaw 530).2.2,
  nativeAvg*nativeA+(nativeRaw 531).2.2,
  nativeAvg*nativeA+(nativeRaw 532).2.2,
  nativeAvg*nativeA+(nativeRaw 533).2.2,
  nativeAvg*nativeA+(nativeRaw 534).2.2,
  nativeAvg*nativeA+(nativeRaw 535).2.2,
  nativeAvg*nativeA+(nativeRaw 536).2.2,
  nativeAvg*nativeA+(nativeRaw 537).2.2,
  nativeAvg*nativeA+(nativeRaw 538).2.2,
  nativeAvg*nativeA+(nativeRaw 539).2.2,
  nativeAvg*nativeA+(nativeRaw 540).2.2,
  nativeAvg*nativeA+(nativeRaw 541).2.2,
  nativeAvg*nativeA+(nativeRaw 542).2.2,
  nativeAvg*nativeA+(nativeRaw 543).2.2,
  nativeAvg*nativeA+(nativeRaw 544).2.2,
  nativeAvg*nativeA+(nativeRaw 545).2.2,
  nativeAvg*nativeA+(nativeRaw 546).2.2,
  nativeAvg*nativeA+(nativeRaw 547).2.2,
  nativeAvg*nativeA+(nativeRaw 548).2.2,
  nativeAvg*nativeA+(nativeRaw 549).2.2,
  nativeAvg*nativeA+(nativeRaw 550).2.2,
  nativeAvg*nativeA+(nativeRaw 551).2.2,
  nativeAvg*nativeA+(nativeRaw 552).2.2
]

def nativeHistoryStrong0512Start : ℚ × ℚ := ((2275560403401475541316635205942694748700948209401832896534123111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789461253796271614670659144007991066277062023981452968825170772160861501/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0512End : ℚ × ℚ := ((2916395367810756253020280767694726678452625408466791919355183/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428778790894394796000652810569018235807489126805325478626890149506140921187552770497/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0512Inputs_length : nativeHistoryStrong0512Inputs.length = 32 := rfl

theorem nativeHistoryStrong0512Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(521+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(521+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0512Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0512Inputs.getD i.val 0)*(nativeHistoryStrong0512Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0512_checked : nativeHistorySteps 9 512 32 nativeHistoryStrong0512Inputs nativeHistoryStrong0512Start = nativeHistoryStrong0512End := by
  decide +kernel

theorem nativeHistoryStrong0512Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0512Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0512Weight : nativeHistoryRatio^512 ≤ nativeHistoryStrong0512Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0512Real_bound : nativeHistoryReal 9 512 nativeHistoryStrong0512Inputs ≤ (nativeHistoryStrong0512End.2 : ℝ)-(nativeHistoryStrong0512Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0512Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0512Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0512Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0512Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0512Inputs.length) := nativeHistoryStrong0512Domains ⟨i,by simpa only [nativeHistoryStrong0512Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0512Inputs.length) := nativeHistoryStrong0512Roots ⟨i,by simpa only [nativeHistoryStrong0512Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0512Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 512 nativeHistoryStrong0512Inputs nativeHistoryStrong0512Start ht hd hr hw
  simpa only [nativeHistoryStrong0512Inputs_length,nativeHistoryStrong0512_checked] using hs

end ASDExplicitGamma.Numerics.Native
