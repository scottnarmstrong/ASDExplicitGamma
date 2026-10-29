module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1024Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1073).2.2,
  nativeAvg*nativeA+(nativeRaw 1074).2.2,
  nativeAvg*nativeA+(nativeRaw 1075).2.2,
  nativeAvg*nativeA+(nativeRaw 1076).2.2,
  nativeAvg*nativeA+(nativeRaw 1077).2.2,
  nativeAvg*nativeA+(nativeRaw 1078).2.2,
  nativeAvg*nativeA+(nativeRaw 1079).2.2,
  nativeAvg*nativeA+(nativeRaw 1080).2.2,
  nativeAvg*nativeA+(nativeRaw 1081).2.2,
  nativeAvg*nativeA+(nativeRaw 1082).2.2,
  nativeAvg*nativeA+(nativeRaw 1083).2.2,
  nativeAvg*nativeA+(nativeRaw 1084).2.2,
  nativeAvg*nativeA+(nativeRaw 1085).2.2,
  nativeAvg*nativeA+(nativeRaw 1086).2.2,
  nativeAvg*nativeA+(nativeRaw 1087).2.2,
  nativeAvg*nativeA+(nativeRaw 1088).2.2,
  nativeAvg*nativeA+(nativeRaw 1089).2.2,
  nativeAvg*nativeA+(nativeRaw 1090).2.2,
  nativeAvg*nativeA+(nativeRaw 1091).2.2,
  nativeAvg*nativeA+(nativeRaw 1092).2.2,
  nativeAvg*nativeA+(nativeRaw 1093).2.2,
  nativeAvg*nativeA+(nativeRaw 1094).2.2,
  nativeAvg*nativeA+(nativeRaw 1095).2.2,
  nativeAvg*nativeA+(nativeRaw 1096).2.2,
  nativeAvg*nativeA+(nativeRaw 1097).2.2,
  nativeAvg*nativeA+(nativeRaw 1098).2.2,
  nativeAvg*nativeA+(nativeRaw 1099).2.2,
  nativeAvg*nativeA+(nativeRaw 1100).2.2,
  nativeAvg*nativeA+(nativeRaw 1101).2.2,
  nativeAvg*nativeA+(nativeRaw 1102).2.2,
  nativeAvg*nativeA+(nativeRaw 1103).2.2,
  nativeAvg*nativeA+(nativeRaw 1104).2.2
]

def nativeHistoryBuffer1024Start : ℚ × ℚ := ((32363594684554288114671461/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733750297986995758137379056692878028148091/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1024End : ℚ × ℚ := ((165910845491340978396069/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687242269239556546727860683467500596722791842205694945226035456709269/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1024Inputs_length : nativeHistoryBuffer1024Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1024Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1073+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1073+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1024Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1024Inputs.getD i.val 0)*(nativeHistoryBuffer1024Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1024_checked : nativeHistorySteps 49 1024 32 nativeHistoryBuffer1024Inputs nativeHistoryBuffer1024Start = nativeHistoryBuffer1024End := by
  decide +kernel

theorem nativeHistoryBuffer1024Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1024Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1024Weight : nativeHistoryRatio^1024 ≤ nativeHistoryBuffer1024Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1024Real_bound : nativeHistoryReal 49 1024 nativeHistoryBuffer1024Inputs ≤ (nativeHistoryBuffer1024End.2 : ℝ)-(nativeHistoryBuffer1024Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1024Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1024Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1024Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1024Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1024Inputs.length) := nativeHistoryBuffer1024Domains ⟨i,by simpa only [nativeHistoryBuffer1024Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1024Inputs.length) := nativeHistoryBuffer1024Roots ⟨i,by simpa only [nativeHistoryBuffer1024Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1024Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1024 nativeHistoryBuffer1024Inputs nativeHistoryBuffer1024Start ht hd hr hw
  simpa only [nativeHistoryBuffer1024Inputs_length,nativeHistoryBuffer1024_checked] using hs

end ASDExplicitGamma.Numerics.Native
