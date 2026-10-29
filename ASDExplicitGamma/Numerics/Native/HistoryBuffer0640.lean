module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0640Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 689).2.2,
  nativeAvg*nativeA+(nativeRaw 690).2.2,
  nativeAvg*nativeA+(nativeRaw 691).2.2,
  nativeAvg*nativeA+(nativeRaw 692).2.2,
  nativeAvg*nativeA+(nativeRaw 693).2.2,
  nativeAvg*nativeA+(nativeRaw 694).2.2,
  nativeAvg*nativeA+(nativeRaw 695).2.2,
  nativeAvg*nativeA+(nativeRaw 696).2.2,
  nativeAvg*nativeA+(nativeRaw 697).2.2,
  nativeAvg*nativeA+(nativeRaw 698).2.2,
  nativeAvg*nativeA+(nativeRaw 699).2.2,
  nativeAvg*nativeA+(nativeRaw 700).2.2,
  nativeAvg*nativeA+(nativeRaw 701).2.2,
  nativeAvg*nativeA+(nativeRaw 702).2.2,
  nativeAvg*nativeA+(nativeRaw 703).2.2,
  nativeAvg*nativeA+(nativeRaw 704).2.2,
  nativeAvg*nativeA+(nativeRaw 705).2.2,
  nativeAvg*nativeA+(nativeRaw 706).2.2,
  nativeAvg*nativeA+(nativeRaw 707).2.2,
  nativeAvg*nativeA+(nativeRaw 708).2.2,
  nativeAvg*nativeA+(nativeRaw 709).2.2,
  nativeAvg*nativeA+(nativeRaw 710).2.2,
  nativeAvg*nativeA+(nativeRaw 711).2.2,
  nativeAvg*nativeA+(nativeRaw 712).2.2,
  nativeAvg*nativeA+(nativeRaw 713).2.2,
  nativeAvg*nativeA+(nativeRaw 714).2.2,
  nativeAvg*nativeA+(nativeRaw 715).2.2,
  nativeAvg*nativeA+(nativeRaw 716).2.2,
  nativeAvg*nativeA+(nativeRaw 717).2.2,
  nativeAvg*nativeA+(nativeRaw 718).2.2,
  nativeAvg*nativeA+(nativeRaw 719).2.2,
  nativeAvg*nativeA+(nativeRaw 720).2.2
]

def nativeHistoryBuffer0640Start : ℚ × ℚ := ((1571666730910899242945132856355081840621810440544157119/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538261942572699221559174851156342885443274119827641709700208941/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0640End : ℚ × ℚ := ((8057094976550511245455887406884759508833090707909009/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11713264740679284981361132629107474896907695555145955204407052557965439716437504986349051376374205061/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0640Inputs_length : nativeHistoryBuffer0640Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0640Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(689+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(689+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0640Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0640Inputs.getD i.val 0)*(nativeHistoryBuffer0640Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0640_checked : nativeHistorySteps 49 640 32 nativeHistoryBuffer0640Inputs nativeHistoryBuffer0640Start = nativeHistoryBuffer0640End := by
  decide +kernel

theorem nativeHistoryBuffer0640Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0640Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0640Weight : nativeHistoryRatio^640 ≤ nativeHistoryBuffer0640Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0640Real_bound : nativeHistoryReal 49 640 nativeHistoryBuffer0640Inputs ≤ (nativeHistoryBuffer0640End.2 : ℝ)-(nativeHistoryBuffer0640Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0640Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0640Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0640Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0640Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0640Inputs.length) := nativeHistoryBuffer0640Domains ⟨i,by simpa only [nativeHistoryBuffer0640Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0640Inputs.length) := nativeHistoryBuffer0640Roots ⟨i,by simpa only [nativeHistoryBuffer0640Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0640Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 640 nativeHistoryBuffer0640Inputs nativeHistoryBuffer0640Start ht hd hr hw
  simpa only [nativeHistoryBuffer0640Inputs_length,nativeHistoryBuffer0640_checked] using hs

end ASDExplicitGamma.Numerics.Native
