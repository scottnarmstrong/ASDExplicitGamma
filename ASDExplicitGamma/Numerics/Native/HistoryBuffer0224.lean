module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0224Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 273).2.2,
  nativeAvg*nativeA+(nativeRaw 274).2.2,
  nativeAvg*nativeA+(nativeRaw 275).2.2,
  nativeAvg*nativeA+(nativeRaw 276).2.2,
  nativeAvg*nativeA+(nativeRaw 277).2.2,
  nativeAvg*nativeA+(nativeRaw 278).2.2,
  nativeAvg*nativeA+(nativeRaw 279).2.2,
  nativeAvg*nativeA+(nativeRaw 280).2.2,
  nativeAvg*nativeA+(nativeRaw 281).2.2,
  nativeAvg*nativeA+(nativeRaw 282).2.2,
  nativeAvg*nativeA+(nativeRaw 283).2.2,
  nativeAvg*nativeA+(nativeRaw 284).2.2,
  nativeAvg*nativeA+(nativeRaw 285).2.2,
  nativeAvg*nativeA+(nativeRaw 286).2.2,
  nativeAvg*nativeA+(nativeRaw 287).2.2,
  nativeAvg*nativeA+(nativeRaw 288).2.2,
  nativeAvg*nativeA+(nativeRaw 289).2.2,
  nativeAvg*nativeA+(nativeRaw 290).2.2,
  nativeAvg*nativeA+(nativeRaw 291).2.2,
  nativeAvg*nativeA+(nativeRaw 292).2.2,
  nativeAvg*nativeA+(nativeRaw 293).2.2,
  nativeAvg*nativeA+(nativeRaw 294).2.2,
  nativeAvg*nativeA+(nativeRaw 295).2.2,
  nativeAvg*nativeA+(nativeRaw 296).2.2,
  nativeAvg*nativeA+(nativeRaw 297).2.2,
  nativeAvg*nativeA+(nativeRaw 298).2.2,
  nativeAvg*nativeA+(nativeRaw 299).2.2,
  nativeAvg*nativeA+(nativeRaw 300).2.2,
  nativeAvg*nativeA+(nativeRaw 301).2.2,
  nativeAvg*nativeA+(nativeRaw 302).2.2,
  nativeAvg*nativeA+(nativeRaw 303).2.2,
  nativeAvg*nativeA+(nativeRaw 304).2.2
]

def nativeHistoryBuffer0224Start : ℚ × ℚ := ((93052096207789479157517473621490049532302614606852871241834371373282060612229103427/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703379091308058146291834339383757272147536151366262960575599059102132445134763317608918640131/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0224End : ℚ × ℚ := ((190811337331992955824335638343396339518377295688766885423290244550061147419680049/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(7320790462924540315464367271042276139527088094105920727064114703634778848647325909119394748560369569/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0224Inputs_length : nativeHistoryBuffer0224Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0224Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(273+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(273+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0224Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0224Inputs.getD i.val 0)*(nativeHistoryBuffer0224Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0224_checked : nativeHistorySteps 49 224 32 nativeHistoryBuffer0224Inputs nativeHistoryBuffer0224Start = nativeHistoryBuffer0224End := by
  decide +kernel

theorem nativeHistoryBuffer0224Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0224Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0224Weight : nativeHistoryRatio^224 ≤ nativeHistoryBuffer0224Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0224Real_bound : nativeHistoryReal 49 224 nativeHistoryBuffer0224Inputs ≤ (nativeHistoryBuffer0224End.2 : ℝ)-(nativeHistoryBuffer0224Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0224Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0224Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0224Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0224Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0224Inputs.length) := nativeHistoryBuffer0224Domains ⟨i,by simpa only [nativeHistoryBuffer0224Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0224Inputs.length) := nativeHistoryBuffer0224Roots ⟨i,by simpa only [nativeHistoryBuffer0224Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0224Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 224 nativeHistoryBuffer0224Inputs nativeHistoryBuffer0224Start ht hd hr hw
  simpa only [nativeHistoryBuffer0224Inputs_length,nativeHistoryBuffer0224_checked] using hs

end ASDExplicitGamma.Numerics.Native
