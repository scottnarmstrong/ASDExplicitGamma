module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0128Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 177).2.2,
  nativeAvg*nativeA+(nativeRaw 178).2.2,
  nativeAvg*nativeA+(nativeRaw 179).2.2,
  nativeAvg*nativeA+(nativeRaw 180).2.2,
  nativeAvg*nativeA+(nativeRaw 181).2.2,
  nativeAvg*nativeA+(nativeRaw 182).2.2,
  nativeAvg*nativeA+(nativeRaw 183).2.2,
  nativeAvg*nativeA+(nativeRaw 184).2.2,
  nativeAvg*nativeA+(nativeRaw 185).2.2,
  nativeAvg*nativeA+(nativeRaw 186).2.2,
  nativeAvg*nativeA+(nativeRaw 187).2.2,
  nativeAvg*nativeA+(nativeRaw 188).2.2,
  nativeAvg*nativeA+(nativeRaw 189).2.2,
  nativeAvg*nativeA+(nativeRaw 190).2.2,
  nativeAvg*nativeA+(nativeRaw 191).2.2,
  nativeAvg*nativeA+(nativeRaw 192).2.2,
  nativeAvg*nativeA+(nativeRaw 193).2.2,
  nativeAvg*nativeA+(nativeRaw 194).2.2,
  nativeAvg*nativeA+(nativeRaw 195).2.2,
  nativeAvg*nativeA+(nativeRaw 196).2.2,
  nativeAvg*nativeA+(nativeRaw 197).2.2,
  nativeAvg*nativeA+(nativeRaw 198).2.2,
  nativeAvg*nativeA+(nativeRaw 199).2.2,
  nativeAvg*nativeA+(nativeRaw 200).2.2,
  nativeAvg*nativeA+(nativeRaw 201).2.2,
  nativeAvg*nativeA+(nativeRaw 202).2.2,
  nativeAvg*nativeA+(nativeRaw 203).2.2,
  nativeAvg*nativeA+(nativeRaw 204).2.2,
  nativeAvg*nativeA+(nativeRaw 205).2.2,
  nativeAvg*nativeA+(nativeRaw 206).2.2,
  nativeAvg*nativeA+(nativeRaw 207).2.2,
  nativeAvg*nativeA+(nativeRaw 208).2.2
]

def nativeHistoryBuffer0128Start : ℚ × ℚ := ((6906723849481622278543480070058587293644127317416607730586931675871205564908114350710764033/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566239681696774951318853339535728119205550171644744132084318624527712801593245630331887677535285919/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0128End : ℚ × ℚ := ((1416283209095549299797276381654664966001910515183972732739379003373390715312677559085997/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161603302352930801240766828889477011683769416126868801618272575763876987870500759329379029183559/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0128Inputs_length : nativeHistoryBuffer0128Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0128Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(177+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(177+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0128Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0128Inputs.getD i.val 0)*(nativeHistoryBuffer0128Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0128_checked : nativeHistorySteps 49 128 32 nativeHistoryBuffer0128Inputs nativeHistoryBuffer0128Start = nativeHistoryBuffer0128End := by
  decide +kernel

theorem nativeHistoryBuffer0128Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0128Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0128Weight : nativeHistoryRatio^128 ≤ nativeHistoryBuffer0128Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0128Real_bound : nativeHistoryReal 49 128 nativeHistoryBuffer0128Inputs ≤ (nativeHistoryBuffer0128End.2 : ℝ)-(nativeHistoryBuffer0128Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0128Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0128Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0128Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0128Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0128Inputs.length) := nativeHistoryBuffer0128Domains ⟨i,by simpa only [nativeHistoryBuffer0128Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0128Inputs.length) := nativeHistoryBuffer0128Roots ⟨i,by simpa only [nativeHistoryBuffer0128Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0128Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 128 nativeHistoryBuffer0128Inputs nativeHistoryBuffer0128Start ht hd hr hw
  simpa only [nativeHistoryBuffer0128Inputs_length,nativeHistoryBuffer0128_checked] using hs

end ASDExplicitGamma.Numerics.Native
