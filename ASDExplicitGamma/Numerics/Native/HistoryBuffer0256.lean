module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0256Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 328).2.2,
  nativeAvg*nativeA+(nativeRaw 329).2.2,
  nativeAvg*nativeA+(nativeRaw 330).2.2,
  nativeAvg*nativeA+(nativeRaw 331).2.2,
  nativeAvg*nativeA+(nativeRaw 332).2.2,
  nativeAvg*nativeA+(nativeRaw 333).2.2,
  nativeAvg*nativeA+(nativeRaw 334).2.2,
  nativeAvg*nativeA+(nativeRaw 335).2.2,
  nativeAvg*nativeA+(nativeRaw 336).2.2
]

def nativeHistoryBuffer0256Start : ℚ × ℚ := ((190811337331992955824335638343396339518377295688766885423290244550061147419680049/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(7320790462924540315464367271042276139527088094105920727064114703634778848647325909119394748560369569/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0256End : ℚ × ℚ := ((24454692544701494037231425303876049405787723386871865986761000331809011180972461/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(7320790462924553037716989732350503412046080193733648155959907609169009114617481186752327050695239913/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0256Inputs_length : nativeHistoryBuffer0256Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0256Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(305+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(305+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0256Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0256Inputs.getD i.val 0)*(nativeHistoryBuffer0256Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0256_checked : nativeHistorySteps 49 256 32 nativeHistoryBuffer0256Inputs nativeHistoryBuffer0256Start = nativeHistoryBuffer0256End := by
  decide +kernel

theorem nativeHistoryBuffer0256Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0256Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0256Weight : nativeHistoryRatio^256 ≤ nativeHistoryBuffer0256Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0256Real_bound : nativeHistoryReal 49 256 nativeHistoryBuffer0256Inputs ≤ (nativeHistoryBuffer0256End.2 : ℝ)-(nativeHistoryBuffer0256Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0256Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0256Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0256Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0256Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0256Inputs.length) := nativeHistoryBuffer0256Domains ⟨i,by simpa only [nativeHistoryBuffer0256Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0256Inputs.length) := nativeHistoryBuffer0256Roots ⟨i,by simpa only [nativeHistoryBuffer0256Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0256Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 256 nativeHistoryBuffer0256Inputs nativeHistoryBuffer0256Start ht hd hr hw
  simpa only [nativeHistoryBuffer0256Inputs_length,nativeHistoryBuffer0256_checked] using hs

end ASDExplicitGamma.Numerics.Native
