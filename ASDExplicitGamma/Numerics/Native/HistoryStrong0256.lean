module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0256Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 265).2.2,
  nativeAvg*nativeA+(nativeRaw 266).2.2,
  nativeAvg*nativeA+(nativeRaw 267).2.2,
  nativeAvg*nativeA+(nativeRaw 268).2.2,
  nativeAvg*nativeA+(nativeRaw 269).2.2,
  nativeAvg*nativeA+(nativeRaw 270).2.2,
  nativeAvg*nativeA+(nativeRaw 271).2.2,
  nativeAvg*nativeA+(nativeRaw 272).2.2,
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
  nativeAvg*nativeA+(nativeRaw 296).2.2
]

def nativeHistoryStrong0256Start : ℚ × ℚ := ((190811337331992955824335638343396339518377295688766885423290244550061147419680049/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362695086224439502808652794377106165404919645536532488847738239927789047258475231487657409/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0256End : ℚ × ℚ := ((24454692544701494037231425303876049405787723386871865986761000331809011180972461/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1189382832295347543871817436704333299673659788965020214113686132960502468417703612900962612603279919/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0256Inputs_length : nativeHistoryStrong0256Inputs.length = 32 := rfl

theorem nativeHistoryStrong0256Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(265+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(265+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0256Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0256Inputs.getD i.val 0)*(nativeHistoryStrong0256Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0256_checked : nativeHistorySteps 9 256 32 nativeHistoryStrong0256Inputs nativeHistoryStrong0256Start = nativeHistoryStrong0256End := by
  decide +kernel

theorem nativeHistoryStrong0256Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0256Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0256Weight : nativeHistoryRatio^256 ≤ nativeHistoryStrong0256Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0256Real_bound : nativeHistoryReal 9 256 nativeHistoryStrong0256Inputs ≤ (nativeHistoryStrong0256End.2 : ℝ)-(nativeHistoryStrong0256Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0256Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0256Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0256Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0256Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0256Inputs.length) := nativeHistoryStrong0256Domains ⟨i,by simpa only [nativeHistoryStrong0256Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0256Inputs.length) := nativeHistoryStrong0256Roots ⟨i,by simpa only [nativeHistoryStrong0256Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0256Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 256 nativeHistoryStrong0256Inputs nativeHistoryStrong0256Start ht hd hr hw
  simpa only [nativeHistoryStrong0256Inputs_length,nativeHistoryStrong0256_checked] using hs

end ASDExplicitGamma.Numerics.Native
