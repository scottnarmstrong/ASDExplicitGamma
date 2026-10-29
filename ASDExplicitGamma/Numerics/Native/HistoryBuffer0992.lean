module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0992Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1041).2.2,
  nativeAvg*nativeA+(nativeRaw 1042).2.2,
  nativeAvg*nativeA+(nativeRaw 1043).2.2,
  nativeAvg*nativeA+(nativeRaw 1044).2.2,
  nativeAvg*nativeA+(nativeRaw 1045).2.2,
  nativeAvg*nativeA+(nativeRaw 1046).2.2,
  nativeAvg*nativeA+(nativeRaw 1047).2.2,
  nativeAvg*nativeA+(nativeRaw 1048).2.2,
  nativeAvg*nativeA+(nativeRaw 1049).2.2,
  nativeAvg*nativeA+(nativeRaw 1050).2.2,
  nativeAvg*nativeA+(nativeRaw 1051).2.2,
  nativeAvg*nativeA+(nativeRaw 1052).2.2,
  nativeAvg*nativeA+(nativeRaw 1053).2.2,
  nativeAvg*nativeA+(nativeRaw 1054).2.2,
  nativeAvg*nativeA+(nativeRaw 1055).2.2,
  nativeAvg*nativeA+(nativeRaw 1056).2.2,
  nativeAvg*nativeA+(nativeRaw 1057).2.2,
  nativeAvg*nativeA+(nativeRaw 1058).2.2,
  nativeAvg*nativeA+(nativeRaw 1059).2.2,
  nativeAvg*nativeA+(nativeRaw 1060).2.2,
  nativeAvg*nativeA+(nativeRaw 1061).2.2,
  nativeAvg*nativeA+(nativeRaw 1062).2.2,
  nativeAvg*nativeA+(nativeRaw 1063).2.2,
  nativeAvg*nativeA+(nativeRaw 1064).2.2,
  nativeAvg*nativeA+(nativeRaw 1065).2.2,
  nativeAvg*nativeA+(nativeRaw 1066).2.2,
  nativeAvg*nativeA+(nativeRaw 1067).2.2,
  nativeAvg*nativeA+(nativeRaw 1068).2.2,
  nativeAvg*nativeA+(nativeRaw 1069).2.2,
  nativeAvg*nativeA+(nativeRaw 1070).2.2,
  nativeAvg*nativeA+(nativeRaw 1071).2.2,
  nativeAvg*nativeA+(nativeRaw 1072).2.2
]

def nativeHistoryBuffer0992Start : ℚ × ℚ := ((101008684060816298614863785309/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935000990955028796864364106241701990060269/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0992End : ℚ × ℚ := ((32363594684554288114671461/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733750297986995758137379056692878028148091/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0992Inputs_length : nativeHistoryBuffer0992Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0992Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1041+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1041+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0992Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0992Inputs.getD i.val 0)*(nativeHistoryBuffer0992Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0992_checked : nativeHistorySteps 49 992 32 nativeHistoryBuffer0992Inputs nativeHistoryBuffer0992Start = nativeHistoryBuffer0992End := by
  decide +kernel

theorem nativeHistoryBuffer0992Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0992Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0992Weight : nativeHistoryRatio^992 ≤ nativeHistoryBuffer0992Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0992Real_bound : nativeHistoryReal 49 992 nativeHistoryBuffer0992Inputs ≤ (nativeHistoryBuffer0992End.2 : ℝ)-(nativeHistoryBuffer0992Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0992Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0992Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0992Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0992Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0992Inputs.length) := nativeHistoryBuffer0992Domains ⟨i,by simpa only [nativeHistoryBuffer0992Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0992Inputs.length) := nativeHistoryBuffer0992Roots ⟨i,by simpa only [nativeHistoryBuffer0992Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0992Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 992 nativeHistoryBuffer0992Inputs nativeHistoryBuffer0992Start ht hd hr hw
  simpa only [nativeHistoryBuffer0992Inputs_length,nativeHistoryBuffer0992_checked] using hs

end ASDExplicitGamma.Numerics.Native
