module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0960Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1009).2.2,
  nativeAvg*nativeA+(nativeRaw 1010).2.2,
  nativeAvg*nativeA+(nativeRaw 1011).2.2,
  nativeAvg*nativeA+(nativeRaw 1012).2.2,
  nativeAvg*nativeA+(nativeRaw 1013).2.2,
  nativeAvg*nativeA+(nativeRaw 1014).2.2,
  nativeAvg*nativeA+(nativeRaw 1015).2.2,
  nativeAvg*nativeA+(nativeRaw 1016).2.2,
  nativeAvg*nativeA+(nativeRaw 1017).2.2,
  nativeAvg*nativeA+(nativeRaw 1018).2.2,
  nativeAvg*nativeA+(nativeRaw 1019).2.2,
  nativeAvg*nativeA+(nativeRaw 1020).2.2,
  nativeAvg*nativeA+(nativeRaw 1021).2.2,
  nativeAvg*nativeA+(nativeRaw 1022).2.2,
  nativeAvg*nativeA+(nativeRaw 1023).2.2,
  nativeAvg*nativeA+(nativeRaw 1024).2.2,
  nativeAvg*nativeA+(nativeRaw 1025).2.2,
  nativeAvg*nativeA+(nativeRaw 1026).2.2,
  nativeAvg*nativeA+(nativeRaw 1027).2.2,
  nativeAvg*nativeA+(nativeRaw 1028).2.2,
  nativeAvg*nativeA+(nativeRaw 1029).2.2,
  nativeAvg*nativeA+(nativeRaw 1030).2.2,
  nativeAvg*nativeA+(nativeRaw 1031).2.2,
  nativeAvg*nativeA+(nativeRaw 1032).2.2,
  nativeAvg*nativeA+(nativeRaw 1033).2.2,
  nativeAvg*nativeA+(nativeRaw 1034).2.2,
  nativeAvg*nativeA+(nativeRaw 1035).2.2,
  nativeAvg*nativeA+(nativeRaw 1036).2.2,
  nativeAvg*nativeA+(nativeRaw 1037).2.2,
  nativeAvg*nativeA+(nativeRaw 1038).2.2,
  nativeAvg*nativeA+(nativeRaw 1039).2.2,
  nativeAvg*nativeA+(nativeRaw 1040).2.2
]

def nativeHistoryBuffer0960Start : ℚ × ℚ := ((9851689022750082313854784888569/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733743253465594759782962129389045612338077/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0960End : ℚ × ℚ := ((101008684060816298614863785309/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935000990955028796864364106241701990060269/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0960Inputs_length : nativeHistoryBuffer0960Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0960Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1009+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1009+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0960Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0960Inputs.getD i.val 0)*(nativeHistoryBuffer0960Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0960_checked : nativeHistorySteps 49 960 32 nativeHistoryBuffer0960Inputs nativeHistoryBuffer0960Start = nativeHistoryBuffer0960End := by
  decide +kernel

theorem nativeHistoryBuffer0960Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0960Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0960Weight : nativeHistoryRatio^960 ≤ nativeHistoryBuffer0960Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0960Real_bound : nativeHistoryReal 49 960 nativeHistoryBuffer0960Inputs ≤ (nativeHistoryBuffer0960End.2 : ℝ)-(nativeHistoryBuffer0960Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0960Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0960Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0960Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0960Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0960Inputs.length) := nativeHistoryBuffer0960Domains ⟨i,by simpa only [nativeHistoryBuffer0960Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0960Inputs.length) := nativeHistoryBuffer0960Roots ⟨i,by simpa only [nativeHistoryBuffer0960Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0960Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 960 nativeHistoryBuffer0960Inputs nativeHistoryBuffer0960Start ht hd hr hw
  simpa only [nativeHistoryBuffer0960Inputs_length,nativeHistoryBuffer0960_checked] using hs

end ASDExplicitGamma.Numerics.Native
