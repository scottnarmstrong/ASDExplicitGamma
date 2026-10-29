module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0352Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 401).2.2,
  nativeAvg*nativeA+(nativeRaw 402).2.2,
  nativeAvg*nativeA+(nativeRaw 403).2.2,
  nativeAvg*nativeA+(nativeRaw 404).2.2,
  nativeAvg*nativeA+(nativeRaw 405).2.2,
  nativeAvg*nativeA+(nativeRaw 406).2.2,
  nativeAvg*nativeA+(nativeRaw 407).2.2,
  nativeAvg*nativeA+(nativeRaw 408).2.2,
  nativeAvg*nativeA+(nativeRaw 409).2.2,
  nativeAvg*nativeA+(nativeRaw 410).2.2,
  nativeAvg*nativeA+(nativeRaw 411).2.2,
  nativeAvg*nativeA+(nativeRaw 412).2.2,
  nativeAvg*nativeA+(nativeRaw 413).2.2,
  nativeAvg*nativeA+(nativeRaw 414).2.2,
  nativeAvg*nativeA+(nativeRaw 415).2.2,
  nativeAvg*nativeA+(nativeRaw 416).2.2,
  nativeAvg*nativeA+(nativeRaw 417).2.2,
  nativeAvg*nativeA+(nativeRaw 418).2.2,
  nativeAvg*nativeA+(nativeRaw 419).2.2,
  nativeAvg*nativeA+(nativeRaw 420).2.2,
  nativeAvg*nativeA+(nativeRaw 421).2.2,
  nativeAvg*nativeA+(nativeRaw 422).2.2,
  nativeAvg*nativeA+(nativeRaw 423).2.2,
  nativeAvg*nativeA+(nativeRaw 424).2.2,
  nativeAvg*nativeA+(nativeRaw 425).2.2,
  nativeAvg*nativeA+(nativeRaw 426).2.2,
  nativeAvg*nativeA+(nativeRaw 427).2.2,
  nativeAvg*nativeA+(nativeRaw 428).2.2,
  nativeAvg*nativeA+(nativeRaw 429).2.2,
  nativeAvg*nativeA+(nativeRaw 430).2.2,
  nativeAvg*nativeA+(nativeRaw 431).2.2,
  nativeAvg*nativeA+(nativeRaw 432).2.2
]

def nativeHistoryBuffer0352Start : ℚ × ℚ := ((321342566061299008933678526379079320826925598699175936907128355535521426413/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453392230573216967306548364630500781585176137167428818185918500272200065223891004483/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0352End : ℚ × ℚ := ((411837879469487115546782955178815160158819774395295499779662072215120479/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(36603952314622765566753460834430145595681347998965503075686110281270262215323128799218818108715759/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0352Inputs_length : nativeHistoryBuffer0352Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0352Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(401+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(401+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0352Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0352Inputs.getD i.val 0)*(nativeHistoryBuffer0352Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0352_checked : nativeHistorySteps 49 352 32 nativeHistoryBuffer0352Inputs nativeHistoryBuffer0352Start = nativeHistoryBuffer0352End := by
  decide +kernel

theorem nativeHistoryBuffer0352Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0352Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0352Weight : nativeHistoryRatio^352 ≤ nativeHistoryBuffer0352Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0352Real_bound : nativeHistoryReal 49 352 nativeHistoryBuffer0352Inputs ≤ (nativeHistoryBuffer0352End.2 : ℝ)-(nativeHistoryBuffer0352Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0352Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0352Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0352Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0352Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0352Inputs.length) := nativeHistoryBuffer0352Domains ⟨i,by simpa only [nativeHistoryBuffer0352Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0352Inputs.length) := nativeHistoryBuffer0352Roots ⟨i,by simpa only [nativeHistoryBuffer0352Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0352Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 352 nativeHistoryBuffer0352Inputs nativeHistoryBuffer0352Start ht hd hr hw
  simpa only [nativeHistoryBuffer0352Inputs_length,nativeHistoryBuffer0352_checked] using hs

end ASDExplicitGamma.Numerics.Native
