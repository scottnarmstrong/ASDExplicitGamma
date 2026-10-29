module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1248Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1257).2.2,
  nativeAvg*nativeA+(nativeRaw 1258).2.2,
  nativeAvg*nativeA+(nativeRaw 1259).2.2,
  nativeAvg*nativeA+(nativeRaw 1260).2.2,
  nativeAvg*nativeA+(nativeRaw 1261).2.2,
  nativeAvg*nativeA+(nativeRaw 1262).2.2,
  nativeAvg*nativeA+(nativeRaw 1263).2.2,
  nativeAvg*nativeA+(nativeRaw 1264).2.2,
  nativeAvg*nativeA+(nativeRaw 1265).2.2,
  nativeAvg*nativeA+(nativeRaw 1266).2.2,
  nativeAvg*nativeA+(nativeRaw 1267).2.2,
  nativeAvg*nativeA+(nativeRaw 1268).2.2,
  nativeAvg*nativeA+(nativeRaw 1269).2.2,
  nativeAvg*nativeA+(nativeRaw 1270).2.2,
  nativeAvg*nativeA+(nativeRaw 1271).2.2,
  nativeAvg*nativeA+(nativeRaw 1272).2.2,
  nativeAvg*nativeA+(nativeRaw 1273).2.2,
  nativeAvg*nativeA+(nativeRaw 1274).2.2,
  nativeAvg*nativeA+(nativeRaw 1275).2.2,
  nativeAvg*nativeA+(nativeRaw 1276).2.2,
  nativeAvg*nativeA+(nativeRaw 1277).2.2,
  nativeAvg*nativeA+(nativeRaw 1278).2.2,
  nativeAvg*nativeA+(nativeRaw 1279).2.2,
  nativeAvg*nativeA+(nativeRaw 1280).2.2,
  nativeAvg*nativeA+(nativeRaw 1281).2.2,
  nativeAvg*nativeA+(nativeRaw 1282).2.2,
  nativeAvg*nativeA+(nativeRaw 1283).2.2,
  nativeAvg*nativeA+(nativeRaw 1284).2.2,
  nativeAvg*nativeA+(nativeRaw 1285).2.2,
  nativeAvg*nativeA+(nativeRaw 1286).2.2,
  nativeAvg*nativeA+(nativeRaw 1287).2.2,
  nativeAvg*nativeA+(nativeRaw 1288).2.2
]

def nativeHistoryStrong1248Start : ℚ × ℚ := ((24092002611/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(951506265836278085755758178878959278989528080400984186654543932363521513252220337241664610266036069/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1248End : ℚ × ℚ := ((123506817/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1903012531672556171511516357757918557979056160801968373309087864727043026504440675879038281498429929/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1248Inputs_length : nativeHistoryStrong1248Inputs.length = 32 := rfl

theorem nativeHistoryStrong1248Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1257+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1257+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1248Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1248Inputs.getD i.val 0)*(nativeHistoryStrong1248Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1248_checked : nativeHistorySteps 9 1248 32 nativeHistoryStrong1248Inputs nativeHistoryStrong1248Start = nativeHistoryStrong1248End := by
  decide +kernel

theorem nativeHistoryStrong1248Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1248Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1248Weight : nativeHistoryRatio^1248 ≤ nativeHistoryStrong1248Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1248Real_bound : nativeHistoryReal 9 1248 nativeHistoryStrong1248Inputs ≤ (nativeHistoryStrong1248End.2 : ℝ)-(nativeHistoryStrong1248Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1248Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1248Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1248Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1248Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1248Inputs.length) := nativeHistoryStrong1248Domains ⟨i,by simpa only [nativeHistoryStrong1248Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1248Inputs.length) := nativeHistoryStrong1248Roots ⟨i,by simpa only [nativeHistoryStrong1248Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1248Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1248 nativeHistoryStrong1248Inputs nativeHistoryStrong1248Start ht hd hr hw
  simpa only [nativeHistoryStrong1248Inputs_length,nativeHistoryStrong1248_checked] using hs

end ASDExplicitGamma.Numerics.Native
