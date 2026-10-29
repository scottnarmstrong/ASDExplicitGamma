module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0864Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 913).2.2,
  nativeAvg*nativeA+(nativeRaw 914).2.2,
  nativeAvg*nativeA+(nativeRaw 915).2.2,
  nativeAvg*nativeA+(nativeRaw 916).2.2,
  nativeAvg*nativeA+(nativeRaw 917).2.2,
  nativeAvg*nativeA+(nativeRaw 918).2.2,
  nativeAvg*nativeA+(nativeRaw 919).2.2,
  nativeAvg*nativeA+(nativeRaw 920).2.2,
  nativeAvg*nativeA+(nativeRaw 921).2.2,
  nativeAvg*nativeA+(nativeRaw 922).2.2,
  nativeAvg*nativeA+(nativeRaw 923).2.2,
  nativeAvg*nativeA+(nativeRaw 924).2.2,
  nativeAvg*nativeA+(nativeRaw 925).2.2,
  nativeAvg*nativeA+(nativeRaw 926).2.2,
  nativeAvg*nativeA+(nativeRaw 927).2.2,
  nativeAvg*nativeA+(nativeRaw 928).2.2,
  nativeAvg*nativeA+(nativeRaw 929).2.2,
  nativeAvg*nativeA+(nativeRaw 930).2.2,
  nativeAvg*nativeA+(nativeRaw 931).2.2,
  nativeAvg*nativeA+(nativeRaw 932).2.2,
  nativeAvg*nativeA+(nativeRaw 933).2.2,
  nativeAvg*nativeA+(nativeRaw 934).2.2,
  nativeAvg*nativeA+(nativeRaw 935).2.2,
  nativeAvg*nativeA+(nativeRaw 936).2.2,
  nativeAvg*nativeA+(nativeRaw 937).2.2,
  nativeAvg*nativeA+(nativeRaw 938).2.2,
  nativeAvg*nativeA+(nativeRaw 939).2.2,
  nativeAvg*nativeA+(nativeRaw 940).2.2,
  nativeAvg*nativeA+(nativeRaw 941).2.2,
  nativeAvg*nativeA+(nativeRaw 942).2.2,
  nativeAvg*nativeA+(nativeRaw 943).2.2,
  nativeAvg*nativeA+(nativeRaw 944).2.2
]

def nativeHistoryBuffer0864Start : ℚ × ℚ := ((146246883851302975226031747223401938681/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721278099208572207902355936398612577764287349171/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0864End : ℚ × ℚ := ((749729576913275489961321993062186813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366342044829631799134032584082454196138749473/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0864Inputs_length : nativeHistoryBuffer0864Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0864Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(913+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(913+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0864Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0864Inputs.getD i.val 0)*(nativeHistoryBuffer0864Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0864_checked : nativeHistorySteps 49 864 32 nativeHistoryBuffer0864Inputs nativeHistoryBuffer0864Start = nativeHistoryBuffer0864End := by
  decide +kernel

theorem nativeHistoryBuffer0864Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0864Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0864Weight : nativeHistoryRatio^864 ≤ nativeHistoryBuffer0864Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0864Real_bound : nativeHistoryReal 49 864 nativeHistoryBuffer0864Inputs ≤ (nativeHistoryBuffer0864End.2 : ℝ)-(nativeHistoryBuffer0864Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0864Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0864Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0864Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0864Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0864Inputs.length) := nativeHistoryBuffer0864Domains ⟨i,by simpa only [nativeHistoryBuffer0864Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0864Inputs.length) := nativeHistoryBuffer0864Roots ⟨i,by simpa only [nativeHistoryBuffer0864Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0864Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 864 nativeHistoryBuffer0864Inputs nativeHistoryBuffer0864Start ht hd hr hw
  simpa only [nativeHistoryBuffer0864Inputs_length,nativeHistoryBuffer0864_checked] using hs

end ASDExplicitGamma.Numerics.Native
