module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0480Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 552).2.2,
  nativeAvg*nativeA+(nativeRaw 553).2.2,
  nativeAvg*nativeA+(nativeRaw 554).2.2,
  nativeAvg*nativeA+(nativeRaw 555).2.2,
  nativeAvg*nativeA+(nativeRaw 556).2.2,
  nativeAvg*nativeA+(nativeRaw 557).2.2,
  nativeAvg*nativeA+(nativeRaw 558).2.2,
  nativeAvg*nativeA+(nativeRaw 559).2.2,
  nativeAvg*nativeA+(nativeRaw 560).2.2
]

def nativeHistoryBuffer0480Start : ℚ × ℚ := ((221942436486919759978175313407914436355682164484339807322373132619/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145510701009379496477061711780736078402751489996343192980442863146217084341/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0480End : ℚ × ℚ := ((2275560403401475541316635205942694748700948209401832896534123111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11713264740679284981361132629107442884981596073000254243351779137691078756116031893441178107654067901/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0480Inputs_length : nativeHistoryBuffer0480Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0480Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(529+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(529+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0480Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0480Inputs.getD i.val 0)*(nativeHistoryBuffer0480Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0480_checked : nativeHistorySteps 49 480 32 nativeHistoryBuffer0480Inputs nativeHistoryBuffer0480Start = nativeHistoryBuffer0480End := by
  decide +kernel

theorem nativeHistoryBuffer0480Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0480Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0480Weight : nativeHistoryRatio^480 ≤ nativeHistoryBuffer0480Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0480Real_bound : nativeHistoryReal 49 480 nativeHistoryBuffer0480Inputs ≤ (nativeHistoryBuffer0480End.2 : ℝ)-(nativeHistoryBuffer0480Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0480Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0480Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0480Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0480Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0480Inputs.length) := nativeHistoryBuffer0480Domains ⟨i,by simpa only [nativeHistoryBuffer0480Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0480Inputs.length) := nativeHistoryBuffer0480Roots ⟨i,by simpa only [nativeHistoryBuffer0480Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0480Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 480 nativeHistoryBuffer0480Inputs nativeHistoryBuffer0480Start ht hd hr hw
  simpa only [nativeHistoryBuffer0480Inputs_length,nativeHistoryBuffer0480_checked] using hs

end ASDExplicitGamma.Numerics.Native
