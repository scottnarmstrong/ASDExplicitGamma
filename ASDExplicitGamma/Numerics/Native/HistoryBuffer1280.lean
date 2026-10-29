module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1280Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1329).2.2,
  nativeAvg*nativeA+(nativeRaw 1330).2.2,
  nativeAvg*nativeA+(nativeRaw 1331).2.2,
  nativeAvg*nativeA+(nativeRaw 1332).2.2,
  nativeAvg*nativeA+(nativeRaw 1333).2.2,
  nativeAvg*nativeA+(nativeRaw 1334).2.2
]

def nativeHistoryBuffer1280Start : ℚ × ℚ := ((123506817/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733750298364342497892465652216960266779171/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1280End : ℚ × ℚ := ((91899217/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991570073770815122562086263/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1280Inputs_length : nativeHistoryBuffer1280Inputs.length = 6 := rfl

theorem nativeHistoryBuffer1280Domains : ∀ i : Fin 6, 0 ≤ (11/10)*(2*nativeGamma*(1329+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1329+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1280Roots : ∀ i : Fin 6, nativeRootValid ((nativeHistoryBuffer1280Inputs.getD i.val 0)*(nativeHistoryBuffer1280Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1280_checked : nativeHistorySteps 49 1280 6 nativeHistoryBuffer1280Inputs nativeHistoryBuffer1280Start = nativeHistoryBuffer1280End := by
  decide +kernel

theorem nativeHistoryBuffer1280Inputs_nonneg : ∀ i : Fin 6, 0 ≤ nativeHistoryBuffer1280Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1280Weight : nativeHistoryRatio^1280 ≤ nativeHistoryBuffer1280Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1280Real_bound : nativeHistoryReal 49 1280 nativeHistoryBuffer1280Inputs ≤ (nativeHistoryBuffer1280End.2 : ℝ)-(nativeHistoryBuffer1280Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1280Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1280Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1280Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1280Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1280Inputs.length) := nativeHistoryBuffer1280Domains ⟨i,by simpa only [nativeHistoryBuffer1280Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1280Inputs.length) := nativeHistoryBuffer1280Roots ⟨i,by simpa only [nativeHistoryBuffer1280Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1280Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1280 nativeHistoryBuffer1280Inputs nativeHistoryBuffer1280Start ht hd hr hw
  simpa only [nativeHistoryBuffer1280Inputs_length,nativeHistoryBuffer1280_checked] using hs

end ASDExplicitGamma.Numerics.Native
