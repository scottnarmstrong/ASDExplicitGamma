module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0352Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 361).2.2,
  nativeAvg*nativeA+(nativeRaw 362).2.2,
  nativeAvg*nativeA+(nativeRaw 363).2.2,
  nativeAvg*nativeA+(nativeRaw 364).2.2,
  nativeAvg*nativeA+(nativeRaw 365).2.2,
  nativeAvg*nativeA+(nativeRaw 366).2.2,
  nativeAvg*nativeA+(nativeRaw 367).2.2,
  nativeAvg*nativeA+(nativeRaw 368).2.2,
  nativeAvg*nativeA+(nativeRaw 369).2.2,
  nativeAvg*nativeA+(nativeRaw 370).2.2,
  nativeAvg*nativeA+(nativeRaw 371).2.2,
  nativeAvg*nativeA+(nativeRaw 372).2.2,
  nativeAvg*nativeA+(nativeRaw 373).2.2,
  nativeAvg*nativeA+(nativeRaw 374).2.2,
  nativeAvg*nativeA+(nativeRaw 375).2.2,
  nativeAvg*nativeA+(nativeRaw 376).2.2,
  nativeAvg*nativeA+(nativeRaw 377).2.2,
  nativeAvg*nativeA+(nativeRaw 378).2.2,
  nativeAvg*nativeA+(nativeRaw 379).2.2,
  nativeAvg*nativeA+(nativeRaw 380).2.2,
  nativeAvg*nativeA+(nativeRaw 381).2.2,
  nativeAvg*nativeA+(nativeRaw 382).2.2,
  nativeAvg*nativeA+(nativeRaw 383).2.2,
  nativeAvg*nativeA+(nativeRaw 384).2.2,
  nativeAvg*nativeA+(nativeRaw 385).2.2,
  nativeAvg*nativeA+(nativeRaw 386).2.2,
  nativeAvg*nativeA+(nativeRaw 387).2.2,
  nativeAvg*nativeA+(nativeRaw 388).2.2,
  nativeAvg*nativeA+(nativeRaw 389).2.2,
  nativeAvg*nativeA+(nativeRaw 390).2.2,
  nativeAvg*nativeA+(nativeRaw 391).2.2,
  nativeAvg*nativeA+(nativeRaw 392).2.2
]

def nativeHistoryStrong0352Start : ℚ × ℚ := ((321342566061299008933678526379079320826925598699175936907128355535521426413/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428769939871601708496878375520640555235539818803994539206500518728678199675491373621/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0352End : ℚ × ℚ := ((411837879469487115546782955178815160158819774395295499779662072215120479/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557476969809454735013732682799506210542655649663624675482713545055651782422245481/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0352Inputs_length : nativeHistoryStrong0352Inputs.length = 32 := rfl

theorem nativeHistoryStrong0352Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(361+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(361+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0352Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0352Inputs.getD i.val 0)*(nativeHistoryStrong0352Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0352_checked : nativeHistorySteps 9 352 32 nativeHistoryStrong0352Inputs nativeHistoryStrong0352Start = nativeHistoryStrong0352End := by
  decide +kernel

theorem nativeHistoryStrong0352Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0352Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0352Weight : nativeHistoryRatio^352 ≤ nativeHistoryStrong0352Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0352Real_bound : nativeHistoryReal 9 352 nativeHistoryStrong0352Inputs ≤ (nativeHistoryStrong0352End.2 : ℝ)-(nativeHistoryStrong0352Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0352Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0352Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0352Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0352Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0352Inputs.length) := nativeHistoryStrong0352Domains ⟨i,by simpa only [nativeHistoryStrong0352Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0352Inputs.length) := nativeHistoryStrong0352Roots ⟨i,by simpa only [nativeHistoryStrong0352Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0352Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 352 nativeHistoryStrong0352Inputs nativeHistoryStrong0352Start ht hd hr hw
  simpa only [nativeHistoryStrong0352Inputs_length,nativeHistoryStrong0352_checked] using hs

end ASDExplicitGamma.Numerics.Native
