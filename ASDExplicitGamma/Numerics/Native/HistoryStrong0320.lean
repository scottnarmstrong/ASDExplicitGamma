module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0320Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 329).2.2,
  nativeAvg*nativeA+(nativeRaw 330).2.2,
  nativeAvg*nativeA+(nativeRaw 331).2.2,
  nativeAvg*nativeA+(nativeRaw 332).2.2,
  nativeAvg*nativeA+(nativeRaw 333).2.2,
  nativeAvg*nativeA+(nativeRaw 334).2.2,
  nativeAvg*nativeA+(nativeRaw 335).2.2,
  nativeAvg*nativeA+(nativeRaw 336).2.2,
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
  nativeAvg*nativeA+(nativeRaw 360).2.2
]

def nativeHistoryStrong0320Start : ℚ × ℚ := ((31341533255718553419973577425489141501976444891534968914217777178128571746269/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390427282136170751908310729807243332827932889116616542191559278068174758539136150400413/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0320End : ℚ × ℚ := ((321342566061299008933678526379079320826925598699175936907128355535521426413/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428769939871601708496878375520640555235539818803994539206500518728678199675491373621/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0320Inputs_length : nativeHistoryStrong0320Inputs.length = 32 := rfl

theorem nativeHistoryStrong0320Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(329+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(329+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0320Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0320Inputs.getD i.val 0)*(nativeHistoryStrong0320Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0320_checked : nativeHistorySteps 9 320 32 nativeHistoryStrong0320Inputs nativeHistoryStrong0320Start = nativeHistoryStrong0320End := by
  decide +kernel

theorem nativeHistoryStrong0320Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0320Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0320Weight : nativeHistoryRatio^320 ≤ nativeHistoryStrong0320Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0320Real_bound : nativeHistoryReal 9 320 nativeHistoryStrong0320Inputs ≤ (nativeHistoryStrong0320End.2 : ℝ)-(nativeHistoryStrong0320Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0320Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0320Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0320Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0320Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0320Inputs.length) := nativeHistoryStrong0320Domains ⟨i,by simpa only [nativeHistoryStrong0320Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0320Inputs.length) := nativeHistoryStrong0320Roots ⟨i,by simpa only [nativeHistoryStrong0320Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0320Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 320 nativeHistoryStrong0320Inputs nativeHistoryStrong0320Start ht hd hr hw
  simpa only [nativeHistoryStrong0320Inputs_length,nativeHistoryStrong0320_checked] using hs

end ASDExplicitGamma.Numerics.Native
