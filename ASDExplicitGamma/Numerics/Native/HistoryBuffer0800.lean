module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0800Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 849).2.2,
  nativeAvg*nativeA+(nativeRaw 850).2.2,
  nativeAvg*nativeA+(nativeRaw 851).2.2,
  nativeAvg*nativeA+(nativeRaw 852).2.2,
  nativeAvg*nativeA+(nativeRaw 853).2.2,
  nativeAvg*nativeA+(nativeRaw 854).2.2,
  nativeAvg*nativeA+(nativeRaw 855).2.2,
  nativeAvg*nativeA+(nativeRaw 856).2.2,
  nativeAvg*nativeA+(nativeRaw 857).2.2,
  nativeAvg*nativeA+(nativeRaw 858).2.2,
  nativeAvg*nativeA+(nativeRaw 859).2.2,
  nativeAvg*nativeA+(nativeRaw 860).2.2,
  nativeAvg*nativeA+(nativeRaw 861).2.2,
  nativeAvg*nativeA+(nativeRaw 862).2.2,
  nativeAvg*nativeA+(nativeRaw 863).2.2,
  nativeAvg*nativeA+(nativeRaw 864).2.2,
  nativeAvg*nativeA+(nativeRaw 865).2.2,
  nativeAvg*nativeA+(nativeRaw 866).2.2,
  nativeAvg*nativeA+(nativeRaw 867).2.2,
  nativeAvg*nativeA+(nativeRaw 868).2.2,
  nativeAvg*nativeA+(nativeRaw 869).2.2,
  nativeAvg*nativeA+(nativeRaw 870).2.2,
  nativeAvg*nativeA+(nativeRaw 871).2.2,
  nativeAvg*nativeA+(nativeRaw 872).2.2,
  nativeAvg*nativeA+(nativeRaw 873).2.2,
  nativeAvg*nativeA+(nativeRaw 874).2.2,
  nativeAvg*nativeA+(nativeRaw 875).2.2,
  nativeAvg*nativeA+(nativeRaw 876).2.2,
  nativeAvg*nativeA+(nativeRaw 877).2.2,
  nativeAvg*nativeA+(nativeRaw 878).2.2,
  nativeAvg*nativeA+(nativeRaw 879).2.2,
  nativeAvg*nativeA+(nativeRaw 880).2.2
]

def nativeHistoryBuffer0800Start : ℚ × ℚ := ((1391203250801999705329508869525379513380709/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093453627784085286157945817600804624780467881841751029/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0800End : ℚ × ℚ := ((1141112832937658760071440520171253214589/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687242269239556546727853914238405358164385194026496476623280612068607/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0800Inputs_length : nativeHistoryBuffer0800Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0800Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(849+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(849+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0800Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0800Inputs.getD i.val 0)*(nativeHistoryBuffer0800Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0800_checked : nativeHistorySteps 49 800 32 nativeHistoryBuffer0800Inputs nativeHistoryBuffer0800Start = nativeHistoryBuffer0800End := by
  decide +kernel

theorem nativeHistoryBuffer0800Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0800Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0800Weight : nativeHistoryRatio^800 ≤ nativeHistoryBuffer0800Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0800Real_bound : nativeHistoryReal 49 800 nativeHistoryBuffer0800Inputs ≤ (nativeHistoryBuffer0800End.2 : ℝ)-(nativeHistoryBuffer0800Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0800Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0800Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0800Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0800Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0800Inputs.length) := nativeHistoryBuffer0800Domains ⟨i,by simpa only [nativeHistoryBuffer0800Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0800Inputs.length) := nativeHistoryBuffer0800Roots ⟨i,by simpa only [nativeHistoryBuffer0800Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0800Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 800 nativeHistoryBuffer0800Inputs nativeHistoryBuffer0800Start ht hd hr hw
  simpa only [nativeHistoryBuffer0800Inputs_length,nativeHistoryBuffer0800_checked] using hs

end ASDExplicitGamma.Numerics.Native
