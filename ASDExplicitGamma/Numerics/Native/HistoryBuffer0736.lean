module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0736Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 785).2.2,
  nativeAvg*nativeA+(nativeRaw 786).2.2,
  nativeAvg*nativeA+(nativeRaw 787).2.2,
  nativeAvg*nativeA+(nativeRaw 788).2.2,
  nativeAvg*nativeA+(nativeRaw 789).2.2,
  nativeAvg*nativeA+(nativeRaw 790).2.2,
  nativeAvg*nativeA+(nativeRaw 791).2.2,
  nativeAvg*nativeA+(nativeRaw 792).2.2,
  nativeAvg*nativeA+(nativeRaw 793).2.2,
  nativeAvg*nativeA+(nativeRaw 794).2.2,
  nativeAvg*nativeA+(nativeRaw 795).2.2,
  nativeAvg*nativeA+(nativeRaw 796).2.2,
  nativeAvg*nativeA+(nativeRaw 797).2.2,
  nativeAvg*nativeA+(nativeRaw 798).2.2,
  nativeAvg*nativeA+(nativeRaw 799).2.2,
  nativeAvg*nativeA+(nativeRaw 800).2.2,
  nativeAvg*nativeA+(nativeRaw 801).2.2,
  nativeAvg*nativeA+(nativeRaw 802).2.2,
  nativeAvg*nativeA+(nativeRaw 803).2.2,
  nativeAvg*nativeA+(nativeRaw 804).2.2,
  nativeAvg*nativeA+(nativeRaw 805).2.2,
  nativeAvg*nativeA+(nativeRaw 806).2.2,
  nativeAvg*nativeA+(nativeRaw 807).2.2,
  nativeAvg*nativeA+(nativeRaw 808).2.2,
  nativeAvg*nativeA+(nativeRaw 809).2.2,
  nativeAvg*nativeA+(nativeRaw 810).2.2,
  nativeAvg*nativeA+(nativeRaw 811).2.2,
  nativeAvg*nativeA+(nativeRaw 812).2.2,
  nativeAvg*nativeA+(nativeRaw 813).2.2,
  nativeAvg*nativeA+(nativeRaw 814).2.2,
  nativeAvg*nativeA+(nativeRaw 815).2.2,
  nativeAvg*nativeA+(nativeRaw 816).2.2
]

def nativeHistoryBuffer0736Start : ℚ × ℚ := ((211745665583950339626510461958685185293939777539/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(3660395231462276556675353946596085905283654944565096846700278298249706629093080266976344285204409811/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0736End : ℚ × ℚ := ((1085506809381912300733748395090105166085320679/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093127868371996448608955037226353599191282581351810919/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0736Inputs_length : nativeHistoryBuffer0736Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0736Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(785+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(785+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0736Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0736Inputs.getD i.val 0)*(nativeHistoryBuffer0736Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0736_checked : nativeHistorySteps 49 736 32 nativeHistoryBuffer0736Inputs nativeHistoryBuffer0736Start = nativeHistoryBuffer0736End := by
  decide +kernel

theorem nativeHistoryBuffer0736Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0736Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0736Weight : nativeHistoryRatio^736 ≤ nativeHistoryBuffer0736Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0736Real_bound : nativeHistoryReal 49 736 nativeHistoryBuffer0736Inputs ≤ (nativeHistoryBuffer0736End.2 : ℝ)-(nativeHistoryBuffer0736Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0736Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0736Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0736Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0736Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0736Inputs.length) := nativeHistoryBuffer0736Domains ⟨i,by simpa only [nativeHistoryBuffer0736Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0736Inputs.length) := nativeHistoryBuffer0736Roots ⟨i,by simpa only [nativeHistoryBuffer0736Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0736Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 736 nativeHistoryBuffer0736Inputs nativeHistoryBuffer0736Start ht hd hr hw
  simpa only [nativeHistoryBuffer0736Inputs_length,nativeHistoryBuffer0736_checked] using hs

end ASDExplicitGamma.Numerics.Native
