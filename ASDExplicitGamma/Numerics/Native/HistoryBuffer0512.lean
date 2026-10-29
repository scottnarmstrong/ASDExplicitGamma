module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0512Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 561).2.2,
  nativeAvg*nativeA+(nativeRaw 562).2.2,
  nativeAvg*nativeA+(nativeRaw 563).2.2,
  nativeAvg*nativeA+(nativeRaw 564).2.2,
  nativeAvg*nativeA+(nativeRaw 565).2.2,
  nativeAvg*nativeA+(nativeRaw 566).2.2,
  nativeAvg*nativeA+(nativeRaw 567).2.2,
  nativeAvg*nativeA+(nativeRaw 568).2.2,
  nativeAvg*nativeA+(nativeRaw 569).2.2,
  nativeAvg*nativeA+(nativeRaw 570).2.2,
  nativeAvg*nativeA+(nativeRaw 571).2.2,
  nativeAvg*nativeA+(nativeRaw 572).2.2,
  nativeAvg*nativeA+(nativeRaw 573).2.2,
  nativeAvg*nativeA+(nativeRaw 574).2.2,
  nativeAvg*nativeA+(nativeRaw 575).2.2,
  nativeAvg*nativeA+(nativeRaw 576).2.2,
  nativeAvg*nativeA+(nativeRaw 577).2.2,
  nativeAvg*nativeA+(nativeRaw 578).2.2,
  nativeAvg*nativeA+(nativeRaw 579).2.2,
  nativeAvg*nativeA+(nativeRaw 580).2.2,
  nativeAvg*nativeA+(nativeRaw 581).2.2,
  nativeAvg*nativeA+(nativeRaw 582).2.2,
  nativeAvg*nativeA+(nativeRaw 583).2.2,
  nativeAvg*nativeA+(nativeRaw 584).2.2,
  nativeAvg*nativeA+(nativeRaw 585).2.2,
  nativeAvg*nativeA+(nativeRaw 586).2.2,
  nativeAvg*nativeA+(nativeRaw 587).2.2,
  nativeAvg*nativeA+(nativeRaw 588).2.2,
  nativeAvg*nativeA+(nativeRaw 589).2.2,
  nativeAvg*nativeA+(nativeRaw 590).2.2,
  nativeAvg*nativeA+(nativeRaw 591).2.2,
  nativeAvg*nativeA+(nativeRaw 592).2.2
]

def nativeHistoryBuffer0512Start : ℚ × ℚ := ((2275560403401475541316635205942694748700948209401832896534123111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11713264740679284981361132629107442884981596073000254243351779137691078756116031893441178107654067901/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0512End : ℚ × ℚ := ((2916395367810756253020280767694726678452625408466791919355183/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768686760125800696542065912481783478933511968258039276130744507582095853/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0512Inputs_length : nativeHistoryBuffer0512Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0512Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(561+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(561+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0512Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0512Inputs.getD i.val 0)*(nativeHistoryBuffer0512Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0512_checked : nativeHistorySteps 49 512 32 nativeHistoryBuffer0512Inputs nativeHistoryBuffer0512Start = nativeHistoryBuffer0512End := by
  decide +kernel

theorem nativeHistoryBuffer0512Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0512Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0512Weight : nativeHistoryRatio^512 ≤ nativeHistoryBuffer0512Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0512Real_bound : nativeHistoryReal 49 512 nativeHistoryBuffer0512Inputs ≤ (nativeHistoryBuffer0512End.2 : ℝ)-(nativeHistoryBuffer0512Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0512Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0512Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0512Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0512Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0512Inputs.length) := nativeHistoryBuffer0512Domains ⟨i,by simpa only [nativeHistoryBuffer0512Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0512Inputs.length) := nativeHistoryBuffer0512Roots ⟨i,by simpa only [nativeHistoryBuffer0512Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0512Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 512 nativeHistoryBuffer0512Inputs nativeHistoryBuffer0512Start ht hd hr hw
  simpa only [nativeHistoryBuffer0512Inputs_length,nativeHistoryBuffer0512_checked] using hs

end ASDExplicitGamma.Numerics.Native
