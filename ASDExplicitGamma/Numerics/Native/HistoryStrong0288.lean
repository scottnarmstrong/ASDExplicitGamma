module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0288Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 297).2.2,
  nativeAvg*nativeA+(nativeRaw 298).2.2,
  nativeAvg*nativeA+(nativeRaw 299).2.2,
  nativeAvg*nativeA+(nativeRaw 300).2.2,
  nativeAvg*nativeA+(nativeRaw 301).2.2,
  nativeAvg*nativeA+(nativeRaw 302).2.2,
  nativeAvg*nativeA+(nativeRaw 303).2.2,
  nativeAvg*nativeA+(nativeRaw 304).2.2,
  nativeAvg*nativeA+(nativeRaw 305).2.2,
  nativeAvg*nativeA+(nativeRaw 306).2.2,
  nativeAvg*nativeA+(nativeRaw 307).2.2,
  nativeAvg*nativeA+(nativeRaw 308).2.2,
  nativeAvg*nativeA+(nativeRaw 309).2.2,
  nativeAvg*nativeA+(nativeRaw 310).2.2,
  nativeAvg*nativeA+(nativeRaw 311).2.2,
  nativeAvg*nativeA+(nativeRaw 312).2.2,
  nativeAvg*nativeA+(nativeRaw 313).2.2,
  nativeAvg*nativeA+(nativeRaw 314).2.2,
  nativeAvg*nativeA+(nativeRaw 315).2.2,
  nativeAvg*nativeA+(nativeRaw 316).2.2,
  nativeAvg*nativeA+(nativeRaw 317).2.2,
  nativeAvg*nativeA+(nativeRaw 318).2.2,
  nativeAvg*nativeA+(nativeRaw 319).2.2,
  nativeAvg*nativeA+(nativeRaw 320).2.2,
  nativeAvg*nativeA+(nativeRaw 321).2.2,
  nativeAvg*nativeA+(nativeRaw 322).2.2,
  nativeAvg*nativeA+(nativeRaw 323).2.2,
  nativeAvg*nativeA+(nativeRaw 324).2.2,
  nativeAvg*nativeA+(nativeRaw 325).2.2,
  nativeAvg*nativeA+(nativeRaw 326).2.2,
  nativeAvg*nativeA+(nativeRaw 327).2.2,
  nativeAvg*nativeA+(nativeRaw 328).2.2
]

def nativeHistoryStrong0288Start : ℚ × ℚ := ((24454692544701494037231425303876049405787723386871865986761000331809011180972461/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1189382832295347543871817436704333299673659788965020214113686132960502468417703612900962612603279919/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0288End : ℚ × ℚ := ((31341533255718553419973577425489141501976444891534968914217777178128571746269/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390427282136170751908310729807243332827932889116616542191559278068174758539136150400413/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0288Inputs_length : nativeHistoryStrong0288Inputs.length = 32 := rfl

theorem nativeHistoryStrong0288Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(297+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(297+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0288Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0288Inputs.getD i.val 0)*(nativeHistoryStrong0288Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0288_checked : nativeHistorySteps 9 288 32 nativeHistoryStrong0288Inputs nativeHistoryStrong0288Start = nativeHistoryStrong0288End := by
  decide +kernel

theorem nativeHistoryStrong0288Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0288Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0288Weight : nativeHistoryRatio^288 ≤ nativeHistoryStrong0288Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0288Real_bound : nativeHistoryReal 9 288 nativeHistoryStrong0288Inputs ≤ (nativeHistoryStrong0288End.2 : ℝ)-(nativeHistoryStrong0288Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0288Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0288Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0288Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0288Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0288Inputs.length) := nativeHistoryStrong0288Domains ⟨i,by simpa only [nativeHistoryStrong0288Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0288Inputs.length) := nativeHistoryStrong0288Roots ⟨i,by simpa only [nativeHistoryStrong0288Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0288Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 288 nativeHistoryStrong0288Inputs nativeHistoryStrong0288Start ht hd hr hw
  simpa only [nativeHistoryStrong0288Inputs_length,nativeHistoryStrong0288_checked] using hs

end ASDExplicitGamma.Numerics.Native
