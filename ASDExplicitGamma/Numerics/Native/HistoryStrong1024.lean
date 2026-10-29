module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1024Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1033).2.2,
  nativeAvg*nativeA+(nativeRaw 1034).2.2,
  nativeAvg*nativeA+(nativeRaw 1035).2.2,
  nativeAvg*nativeA+(nativeRaw 1036).2.2,
  nativeAvg*nativeA+(nativeRaw 1037).2.2,
  nativeAvg*nativeA+(nativeRaw 1038).2.2,
  nativeAvg*nativeA+(nativeRaw 1039).2.2,
  nativeAvg*nativeA+(nativeRaw 1040).2.2,
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
  nativeAvg*nativeA+(nativeRaw 1064).2.2
]

def nativeHistoryStrong1024Start : ℚ × ℚ := ((32363594684554288114671461/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820201002460466636359830908566007063531533757008473220892427/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1024End : ℚ × ℚ := ((165910845491340978396069/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635208113409683509923227496294529371/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1024Inputs_length : nativeHistoryStrong1024Inputs.length = 32 := rfl

theorem nativeHistoryStrong1024Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1033+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1033+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1024Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1024Inputs.getD i.val 0)*(nativeHistoryStrong1024Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1024_checked : nativeHistorySteps 9 1024 32 nativeHistoryStrong1024Inputs nativeHistoryStrong1024Start = nativeHistoryStrong1024End := by
  decide +kernel

theorem nativeHistoryStrong1024Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1024Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1024Weight : nativeHistoryRatio^1024 ≤ nativeHistoryStrong1024Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1024Real_bound : nativeHistoryReal 9 1024 nativeHistoryStrong1024Inputs ≤ (nativeHistoryStrong1024End.2 : ℝ)-(nativeHistoryStrong1024Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1024Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1024Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1024Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1024Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1024Inputs.length) := nativeHistoryStrong1024Domains ⟨i,by simpa only [nativeHistoryStrong1024Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1024Inputs.length) := nativeHistoryStrong1024Roots ⟨i,by simpa only [nativeHistoryStrong1024Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1024Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1024 nativeHistoryStrong1024Inputs nativeHistoryStrong1024Start ht hd hr hw
  simpa only [nativeHistoryStrong1024Inputs_length,nativeHistoryStrong1024_checked] using hs

end ASDExplicitGamma.Numerics.Native
