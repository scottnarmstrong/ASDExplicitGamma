module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0896Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 945).2.2,
  nativeAvg*nativeA+(nativeRaw 946).2.2,
  nativeAvg*nativeA+(nativeRaw 947).2.2,
  nativeAvg*nativeA+(nativeRaw 948).2.2,
  nativeAvg*nativeA+(nativeRaw 949).2.2,
  nativeAvg*nativeA+(nativeRaw 950).2.2,
  nativeAvg*nativeA+(nativeRaw 951).2.2,
  nativeAvg*nativeA+(nativeRaw 952).2.2,
  nativeAvg*nativeA+(nativeRaw 953).2.2,
  nativeAvg*nativeA+(nativeRaw 954).2.2,
  nativeAvg*nativeA+(nativeRaw 955).2.2,
  nativeAvg*nativeA+(nativeRaw 956).2.2,
  nativeAvg*nativeA+(nativeRaw 957).2.2,
  nativeAvg*nativeA+(nativeRaw 958).2.2,
  nativeAvg*nativeA+(nativeRaw 959).2.2,
  nativeAvg*nativeA+(nativeRaw 960).2.2,
  nativeAvg*nativeA+(nativeRaw 961).2.2,
  nativeAvg*nativeA+(nativeRaw 962).2.2,
  nativeAvg*nativeA+(nativeRaw 963).2.2,
  nativeAvg*nativeA+(nativeRaw 964).2.2,
  nativeAvg*nativeA+(nativeRaw 965).2.2,
  nativeAvg*nativeA+(nativeRaw 966).2.2,
  nativeAvg*nativeA+(nativeRaw 967).2.2,
  nativeAvg*nativeA+(nativeRaw 968).2.2,
  nativeAvg*nativeA+(nativeRaw 969).2.2,
  nativeAvg*nativeA+(nativeRaw 970).2.2,
  nativeAvg*nativeA+(nativeRaw 971).2.2,
  nativeAvg*nativeA+(nativeRaw 972).2.2,
  nativeAvg*nativeA+(nativeRaw 973).2.2,
  nativeAvg*nativeA+(nativeRaw 974).2.2,
  nativeAvg*nativeA+(nativeRaw 975).2.2,
  nativeAvg*nativeA+(nativeRaw 976).2.2
]

def nativeHistoryBuffer0896Start : ℚ × ℚ := ((749729576913275489961321993062186813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366342044829631799134032584082454196138749473/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0896End : ℚ × ℚ := ((960865667179053422125864697785571/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366930962635351665766188035353279138515323429/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0896Inputs_length : nativeHistoryBuffer0896Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0896Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(945+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(945+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0896Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0896Inputs.getD i.val 0)*(nativeHistoryBuffer0896Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0896_checked : nativeHistorySteps 49 896 32 nativeHistoryBuffer0896Inputs nativeHistoryBuffer0896Start = nativeHistoryBuffer0896End := by
  decide +kernel

theorem nativeHistoryBuffer0896Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0896Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0896Weight : nativeHistoryRatio^896 ≤ nativeHistoryBuffer0896Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0896Real_bound : nativeHistoryReal 49 896 nativeHistoryBuffer0896Inputs ≤ (nativeHistoryBuffer0896End.2 : ℝ)-(nativeHistoryBuffer0896Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0896Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0896Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0896Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0896Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0896Inputs.length) := nativeHistoryBuffer0896Domains ⟨i,by simpa only [nativeHistoryBuffer0896Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0896Inputs.length) := nativeHistoryBuffer0896Roots ⟨i,by simpa only [nativeHistoryBuffer0896Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0896Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 896 nativeHistoryBuffer0896Inputs nativeHistoryBuffer0896Start ht hd hr hw
  simpa only [nativeHistoryBuffer0896Inputs_length,nativeHistoryBuffer0896_checked] using hs

end ASDExplicitGamma.Numerics.Native
