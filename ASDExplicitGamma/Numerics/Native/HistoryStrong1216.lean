module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1216Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1225).2.2,
  nativeAvg*nativeA+(nativeRaw 1226).2.2,
  nativeAvg*nativeA+(nativeRaw 1227).2.2,
  nativeAvg*nativeA+(nativeRaw 1228).2.2,
  nativeAvg*nativeA+(nativeRaw 1229).2.2,
  nativeAvg*nativeA+(nativeRaw 1230).2.2,
  nativeAvg*nativeA+(nativeRaw 1231).2.2,
  nativeAvg*nativeA+(nativeRaw 1232).2.2,
  nativeAvg*nativeA+(nativeRaw 1233).2.2,
  nativeAvg*nativeA+(nativeRaw 1234).2.2,
  nativeAvg*nativeA+(nativeRaw 1235).2.2,
  nativeAvg*nativeA+(nativeRaw 1236).2.2,
  nativeAvg*nativeA+(nativeRaw 1237).2.2,
  nativeAvg*nativeA+(nativeRaw 1238).2.2,
  nativeAvg*nativeA+(nativeRaw 1239).2.2,
  nativeAvg*nativeA+(nativeRaw 1240).2.2,
  nativeAvg*nativeA+(nativeRaw 1241).2.2,
  nativeAvg*nativeA+(nativeRaw 1242).2.2,
  nativeAvg*nativeA+(nativeRaw 1243).2.2,
  nativeAvg*nativeA+(nativeRaw 1244).2.2,
  nativeAvg*nativeA+(nativeRaw 1245).2.2,
  nativeAvg*nativeA+(nativeRaw 1246).2.2,
  nativeAvg*nativeA+(nativeRaw 1247).2.2,
  nativeAvg*nativeA+(nativeRaw 1248).2.2,
  nativeAvg*nativeA+(nativeRaw 1249).2.2,
  nativeAvg*nativeA+(nativeRaw 1250).2.2,
  nativeAvg*nativeA+(nativeRaw 1251).2.2,
  nativeAvg*nativeA+(nativeRaw 1252).2.2,
  nativeAvg*nativeA+(nativeRaw 1253).2.2,
  nativeAvg*nativeA+(nativeRaw 1254).2.2,
  nativeAvg*nativeA+(nativeRaw 1255).2.2,
  nativeAvg*nativeA+(nativeRaw 1256).2.2
]

def nativeHistoryStrong1216Start : ℚ × ℚ := ((9399069787053/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(594691416147673803597348861799349549368455050250615116659089957727200945782637683165962614471711403/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1216End : ℚ × ℚ := ((24092002611/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(951506265836278085755758178878959278989528080400984186654543932363521513252220337241664610266036069/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1216Inputs_length : nativeHistoryStrong1216Inputs.length = 32 := rfl

theorem nativeHistoryStrong1216Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1225+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1225+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1216Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1216Inputs.getD i.val 0)*(nativeHistoryStrong1216Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1216_checked : nativeHistorySteps 9 1216 32 nativeHistoryStrong1216Inputs nativeHistoryStrong1216Start = nativeHistoryStrong1216End := by
  decide +kernel

theorem nativeHistoryStrong1216Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1216Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1216Weight : nativeHistoryRatio^1216 ≤ nativeHistoryStrong1216Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1216Real_bound : nativeHistoryReal 9 1216 nativeHistoryStrong1216Inputs ≤ (nativeHistoryStrong1216End.2 : ℝ)-(nativeHistoryStrong1216Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1216Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1216Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1216Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1216Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1216Inputs.length) := nativeHistoryStrong1216Domains ⟨i,by simpa only [nativeHistoryStrong1216Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1216Inputs.length) := nativeHistoryStrong1216Roots ⟨i,by simpa only [nativeHistoryStrong1216Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1216Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1216 nativeHistoryStrong1216Inputs nativeHistoryStrong1216Start ht hd hr hw
  simpa only [nativeHistoryStrong1216Inputs_length,nativeHistoryStrong1216_checked] using hs

end ASDExplicitGamma.Numerics.Native
