module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0832Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 881).2.2,
  nativeAvg*nativeA+(nativeRaw 882).2.2,
  nativeAvg*nativeA+(nativeRaw 883).2.2,
  nativeAvg*nativeA+(nativeRaw 884).2.2,
  nativeAvg*nativeA+(nativeRaw 885).2.2,
  nativeAvg*nativeA+(nativeRaw 886).2.2,
  nativeAvg*nativeA+(nativeRaw 887).2.2,
  nativeAvg*nativeA+(nativeRaw 888).2.2,
  nativeAvg*nativeA+(nativeRaw 889).2.2,
  nativeAvg*nativeA+(nativeRaw 890).2.2,
  nativeAvg*nativeA+(nativeRaw 891).2.2,
  nativeAvg*nativeA+(nativeRaw 892).2.2,
  nativeAvg*nativeA+(nativeRaw 893).2.2,
  nativeAvg*nativeA+(nativeRaw 894).2.2,
  nativeAvg*nativeA+(nativeRaw 895).2.2,
  nativeAvg*nativeA+(nativeRaw 896).2.2,
  nativeAvg*nativeA+(nativeRaw 897).2.2,
  nativeAvg*nativeA+(nativeRaw 898).2.2,
  nativeAvg*nativeA+(nativeRaw 899).2.2,
  nativeAvg*nativeA+(nativeRaw 900).2.2,
  nativeAvg*nativeA+(nativeRaw 901).2.2,
  nativeAvg*nativeA+(nativeRaw 902).2.2,
  nativeAvg*nativeA+(nativeRaw 903).2.2,
  nativeAvg*nativeA+(nativeRaw 904).2.2,
  nativeAvg*nativeA+(nativeRaw 905).2.2,
  nativeAvg*nativeA+(nativeRaw 906).2.2,
  nativeAvg*nativeA+(nativeRaw 907).2.2,
  nativeAvg*nativeA+(nativeRaw 908).2.2,
  nativeAvg*nativeA+(nativeRaw 909).2.2,
  nativeAvg*nativeA+(nativeRaw 910).2.2,
  nativeAvg*nativeA+(nativeRaw 911).2.2,
  nativeAvg*nativeA+(nativeRaw 912).2.2
]

def nativeHistoryBuffer0832Start : ℚ × ℚ := ((1141112832937658760071440520171253214589/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687242269239556546727853914238405358164385194026496476623280612068607/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0832End : ℚ × ℚ := ((146246883851302975226031747223401938681/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721278099208572207902355936398612577764287349171/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0832Inputs_length : nativeHistoryBuffer0832Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0832Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(881+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(881+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0832Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0832Inputs.getD i.val 0)*(nativeHistoryBuffer0832Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0832_checked : nativeHistorySteps 49 832 32 nativeHistoryBuffer0832Inputs nativeHistoryBuffer0832Start = nativeHistoryBuffer0832End := by
  decide +kernel

theorem nativeHistoryBuffer0832Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0832Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0832Weight : nativeHistoryRatio^832 ≤ nativeHistoryBuffer0832Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0832Real_bound : nativeHistoryReal 49 832 nativeHistoryBuffer0832Inputs ≤ (nativeHistoryBuffer0832End.2 : ℝ)-(nativeHistoryBuffer0832Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0832Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0832Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0832Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0832Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0832Inputs.length) := nativeHistoryBuffer0832Domains ⟨i,by simpa only [nativeHistoryBuffer0832Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0832Inputs.length) := nativeHistoryBuffer0832Roots ⟨i,by simpa only [nativeHistoryBuffer0832Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0832Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 832 nativeHistoryBuffer0832Inputs nativeHistoryBuffer0832Start ht hd hr hw
  simpa only [nativeHistoryBuffer0832Inputs_length,nativeHistoryBuffer0832_checked] using hs

end ASDExplicitGamma.Numerics.Native
