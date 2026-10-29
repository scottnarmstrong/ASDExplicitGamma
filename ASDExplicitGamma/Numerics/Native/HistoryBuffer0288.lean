module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0288Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 337).2.2,
  nativeAvg*nativeA+(nativeRaw 338).2.2,
  nativeAvg*nativeA+(nativeRaw 339).2.2,
  nativeAvg*nativeA+(nativeRaw 340).2.2,
  nativeAvg*nativeA+(nativeRaw 341).2.2,
  nativeAvg*nativeA+(nativeRaw 342).2.2,
  nativeAvg*nativeA+(nativeRaw 343).2.2,
  nativeAvg*nativeA+(nativeRaw 344).2.2,
  nativeAvg*nativeA+(nativeRaw 345).2.2,
  nativeAvg*nativeA+(nativeRaw 346).2.2,
  nativeAvg*nativeA+(nativeRaw 347).2.2,
  nativeAvg*nativeA+(nativeRaw 348).2.2,
  nativeAvg*nativeA+(nativeRaw 349).2.2,
  nativeAvg*nativeA+(nativeRaw 350).2.2,
  nativeAvg*nativeA+(nativeRaw 351).2.2,
  nativeAvg*nativeA+(nativeRaw 352).2.2,
  nativeAvg*nativeA+(nativeRaw 353).2.2,
  nativeAvg*nativeA+(nativeRaw 354).2.2,
  nativeAvg*nativeA+(nativeRaw 355).2.2,
  nativeAvg*nativeA+(nativeRaw 356).2.2,
  nativeAvg*nativeA+(nativeRaw 357).2.2,
  nativeAvg*nativeA+(nativeRaw 358).2.2,
  nativeAvg*nativeA+(nativeRaw 359).2.2,
  nativeAvg*nativeA+(nativeRaw 360).2.2,
  nativeAvg*nativeA+(nativeRaw 361).2.2,
  nativeAvg*nativeA+(nativeRaw 362).2.2,
  nativeAvg*nativeA+(nativeRaw 363).2.2,
  nativeAvg*nativeA+(nativeRaw 364).2.2,
  nativeAvg*nativeA+(nativeRaw 365).2.2,
  nativeAvg*nativeA+(nativeRaw 366).2.2,
  nativeAvg*nativeA+(nativeRaw 367).2.2,
  nativeAvg*nativeA+(nativeRaw 368).2.2
]

def nativeHistoryBuffer0288Start : ℚ × ℚ := ((24454692544701494037231425303876049405787723386871865986761000331809011180972461/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(7320790462924553037716989732350503412046080193733648155959907609169009114617481186752327050695239913/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0288End : ℚ × ℚ := ((31341533255718553419973577425489141501976444891534968914217777178128571746269/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424903226370149056819699213827747419339208971146938831130435243352762033698162710698657/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0288Inputs_length : nativeHistoryBuffer0288Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0288Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(337+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(337+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0288Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0288Inputs.getD i.val 0)*(nativeHistoryBuffer0288Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0288_checked : nativeHistorySteps 49 288 32 nativeHistoryBuffer0288Inputs nativeHistoryBuffer0288Start = nativeHistoryBuffer0288End := by
  decide +kernel

theorem nativeHistoryBuffer0288Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0288Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0288Weight : nativeHistoryRatio^288 ≤ nativeHistoryBuffer0288Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0288Real_bound : nativeHistoryReal 49 288 nativeHistoryBuffer0288Inputs ≤ (nativeHistoryBuffer0288End.2 : ℝ)-(nativeHistoryBuffer0288Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0288Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0288Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0288Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0288Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0288Inputs.length) := nativeHistoryBuffer0288Domains ⟨i,by simpa only [nativeHistoryBuffer0288Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0288Inputs.length) := nativeHistoryBuffer0288Roots ⟨i,by simpa only [nativeHistoryBuffer0288Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0288Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 288 nativeHistoryBuffer0288Inputs nativeHistoryBuffer0288Start ht hd hr hw
  simpa only [nativeHistoryBuffer0288Inputs_length,nativeHistoryBuffer0288_checked] using hs

end ASDExplicitGamma.Numerics.Native
