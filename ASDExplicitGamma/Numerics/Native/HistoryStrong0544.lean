module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0544Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 553).2.2,
  nativeAvg*nativeA+(nativeRaw 554).2.2,
  nativeAvg*nativeA+(nativeRaw 555).2.2,
  nativeAvg*nativeA+(nativeRaw 556).2.2,
  nativeAvg*nativeA+(nativeRaw 557).2.2,
  nativeAvg*nativeA+(nativeRaw 558).2.2,
  nativeAvg*nativeA+(nativeRaw 559).2.2,
  nativeAvg*nativeA+(nativeRaw 560).2.2,
  nativeAvg*nativeA+(nativeRaw 561).2.2,
  nativeAvg*nativeA+(nativeRaw 562).2.2,
  nativeAvg*nativeA+(nativeRaw 563).2.2,
  nativeAvg*nativeA+(nativeRaw 564).2.2,
  nativeAvg*nativeA+(nativeRaw 565).2.2,
  nativeAvg*nativeA+(nativeRaw 566).2.2,
  nativeAvg*nativeA+(nativeRaw 567).2.2,
  nativeAvg*nativeA+(nativeRaw 568).2.2,
  nativeAvg*nativeA+(nativeRaw 569).2.2,
  nativeAvg*nativeA+(nativeRaw 570).2.2,
  nativeAvg*nativeA+(nativeRaw 571).2.2,
  nativeAvg*nativeA+(nativeRaw 572).2.2,
  nativeAvg*nativeA+(nativeRaw 573).2.2,
  nativeAvg*nativeA+(nativeRaw 574).2.2,
  nativeAvg*nativeA+(nativeRaw 575).2.2,
  nativeAvg*nativeA+(nativeRaw 576).2.2,
  nativeAvg*nativeA+(nativeRaw 577).2.2,
  nativeAvg*nativeA+(nativeRaw 578).2.2,
  nativeAvg*nativeA+(nativeRaw 579).2.2,
  nativeAvg*nativeA+(nativeRaw 580).2.2,
  nativeAvg*nativeA+(nativeRaw 581).2.2,
  nativeAvg*nativeA+(nativeRaw 582).2.2,
  nativeAvg*nativeA+(nativeRaw 583).2.2,
  nativeAvg*nativeA+(nativeRaw 584).2.2
]

def nativeHistoryStrong0544Start : ℚ × ℚ := ((2916395367810756253020280767694726678452625408466791919355183/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428778790894394796000652810569018235807489126805325478626890149506140921187552770497/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0544End : ℚ × ℚ := ((59803198745587883394037968344665236371819882007316878155517/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428778790894394796392574662502953340673415408578547046148153201005412448340340633953/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0544Inputs_length : nativeHistoryStrong0544Inputs.length = 32 := rfl

theorem nativeHistoryStrong0544Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(553+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(553+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0544Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0544Inputs.getD i.val 0)*(nativeHistoryStrong0544Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0544_checked : nativeHistorySteps 9 544 32 nativeHistoryStrong0544Inputs nativeHistoryStrong0544Start = nativeHistoryStrong0544End := by
  decide +kernel

theorem nativeHistoryStrong0544Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0544Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0544Weight : nativeHistoryRatio^544 ≤ nativeHistoryStrong0544Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0544Real_bound : nativeHistoryReal 9 544 nativeHistoryStrong0544Inputs ≤ (nativeHistoryStrong0544End.2 : ℝ)-(nativeHistoryStrong0544Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0544Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0544Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0544Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0544Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0544Inputs.length) := nativeHistoryStrong0544Domains ⟨i,by simpa only [nativeHistoryStrong0544Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0544Inputs.length) := nativeHistoryStrong0544Roots ⟨i,by simpa only [nativeHistoryStrong0544Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0544Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 544 nativeHistoryStrong0544Inputs nativeHistoryStrong0544Start ht hd hr hw
  simpa only [nativeHistoryStrong0544Inputs_length,nativeHistoryStrong0544_checked] using hs

end ASDExplicitGamma.Numerics.Native
