module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0640Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 649).2.2,
  nativeAvg*nativeA+(nativeRaw 650).2.2,
  nativeAvg*nativeA+(nativeRaw 651).2.2,
  nativeAvg*nativeA+(nativeRaw 652).2.2,
  nativeAvg*nativeA+(nativeRaw 653).2.2,
  nativeAvg*nativeA+(nativeRaw 654).2.2,
  nativeAvg*nativeA+(nativeRaw 655).2.2,
  nativeAvg*nativeA+(nativeRaw 656).2.2,
  nativeAvg*nativeA+(nativeRaw 657).2.2,
  nativeAvg*nativeA+(nativeRaw 658).2.2,
  nativeAvg*nativeA+(nativeRaw 659).2.2,
  nativeAvg*nativeA+(nativeRaw 660).2.2,
  nativeAvg*nativeA+(nativeRaw 661).2.2,
  nativeAvg*nativeA+(nativeRaw 662).2.2,
  nativeAvg*nativeA+(nativeRaw 663).2.2,
  nativeAvg*nativeA+(nativeRaw 664).2.2,
  nativeAvg*nativeA+(nativeRaw 665).2.2,
  nativeAvg*nativeA+(nativeRaw 666).2.2,
  nativeAvg*nativeA+(nativeRaw 667).2.2,
  nativeAvg*nativeA+(nativeRaw 668).2.2,
  nativeAvg*nativeA+(nativeRaw 669).2.2,
  nativeAvg*nativeA+(nativeRaw 670).2.2,
  nativeAvg*nativeA+(nativeRaw 671).2.2,
  nativeAvg*nativeA+(nativeRaw 672).2.2,
  nativeAvg*nativeA+(nativeRaw 673).2.2,
  nativeAvg*nativeA+(nativeRaw 674).2.2,
  nativeAvg*nativeA+(nativeRaw 675).2.2,
  nativeAvg*nativeA+(nativeRaw 676).2.2,
  nativeAvg*nativeA+(nativeRaw 677).2.2,
  nativeAvg*nativeA+(nativeRaw 678).2.2,
  nativeAvg*nativeA+(nativeRaw 679).2.2,
  nativeAvg*nativeA+(nativeRaw 680).2.2
]

def nativeHistoryStrong0640Start : ℚ × ℚ := ((1571666730910899242945132856355081840621810440544157119/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895106537458366014260299019287726116929511670349172593119561937/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0640End : ℚ × ℚ := ((8057094976550511245455887406884759508833090707909009/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895279739454572010655506146326876721211970731069283925113367447/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0640Inputs_length : nativeHistoryStrong0640Inputs.length = 32 := rfl

theorem nativeHistoryStrong0640Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(649+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(649+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0640Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0640Inputs.getD i.val 0)*(nativeHistoryStrong0640Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0640_checked : nativeHistorySteps 9 640 32 nativeHistoryStrong0640Inputs nativeHistoryStrong0640Start = nativeHistoryStrong0640End := by
  decide +kernel

theorem nativeHistoryStrong0640Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0640Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0640Weight : nativeHistoryRatio^640 ≤ nativeHistoryStrong0640Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0640Real_bound : nativeHistoryReal 9 640 nativeHistoryStrong0640Inputs ≤ (nativeHistoryStrong0640End.2 : ℝ)-(nativeHistoryStrong0640Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0640Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0640Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0640Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0640Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0640Inputs.length) := nativeHistoryStrong0640Domains ⟨i,by simpa only [nativeHistoryStrong0640Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0640Inputs.length) := nativeHistoryStrong0640Roots ⟨i,by simpa only [nativeHistoryStrong0640Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0640Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 640 nativeHistoryStrong0640Inputs nativeHistoryStrong0640Start ht hd hr hw
  simpa only [nativeHistoryStrong0640Inputs_length,nativeHistoryStrong0640_checked] using hs

end ASDExplicitGamma.Numerics.Native
