module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0448Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 520).2.2,
  nativeAvg*nativeA+(nativeRaw 521).2.2,
  nativeAvg*nativeA+(nativeRaw 522).2.2,
  nativeAvg*nativeA+(nativeRaw 523).2.2,
  nativeAvg*nativeA+(nativeRaw 524).2.2,
  nativeAvg*nativeA+(nativeRaw 525).2.2,
  nativeAvg*nativeA+(nativeRaw 526).2.2,
  nativeAvg*nativeA+(nativeRaw 527).2.2,
  nativeAvg*nativeA+(nativeRaw 528).2.2
]

def nativeHistoryBuffer0448Start : ℚ × ℚ := ((86586926086637091678870978027611080834722316789952727645292792882353/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663141076876971368119708953716772780181381262221612298008888544288236806665769/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0448End : ℚ × ℚ := ((221942436486919759978175313407914436355682164484339807322373132619/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145510701009379496477061711780736078402751489996343192980442863146217084341/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0448Inputs_length : nativeHistoryBuffer0448Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0448Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(497+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(497+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0448Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0448Inputs.getD i.val 0)*(nativeHistoryBuffer0448Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0448_checked : nativeHistorySteps 49 448 32 nativeHistoryBuffer0448Inputs nativeHistoryBuffer0448Start = nativeHistoryBuffer0448End := by
  decide +kernel

theorem nativeHistoryBuffer0448Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0448Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0448Weight : nativeHistoryRatio^448 ≤ nativeHistoryBuffer0448Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0448Real_bound : nativeHistoryReal 49 448 nativeHistoryBuffer0448Inputs ≤ (nativeHistoryBuffer0448End.2 : ℝ)-(nativeHistoryBuffer0448Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0448Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0448Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0448Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0448Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0448Inputs.length) := nativeHistoryBuffer0448Domains ⟨i,by simpa only [nativeHistoryBuffer0448Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0448Inputs.length) := nativeHistoryBuffer0448Roots ⟨i,by simpa only [nativeHistoryBuffer0448Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0448Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 448 nativeHistoryBuffer0448Inputs nativeHistoryBuffer0448Start ht hd hr hw
  simpa only [nativeHistoryBuffer0448Inputs_length,nativeHistoryBuffer0448_checked] using hs

end ASDExplicitGamma.Numerics.Native
