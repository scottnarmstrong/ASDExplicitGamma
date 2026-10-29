module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0736Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 745).2.2,
  nativeAvg*nativeA+(nativeRaw 746).2.2,
  nativeAvg*nativeA+(nativeRaw 747).2.2,
  nativeAvg*nativeA+(nativeRaw 748).2.2,
  nativeAvg*nativeA+(nativeRaw 749).2.2,
  nativeAvg*nativeA+(nativeRaw 750).2.2,
  nativeAvg*nativeA+(nativeRaw 751).2.2,
  nativeAvg*nativeA+(nativeRaw 752).2.2,
  nativeAvg*nativeA+(nativeRaw 753).2.2,
  nativeAvg*nativeA+(nativeRaw 754).2.2,
  nativeAvg*nativeA+(nativeRaw 755).2.2,
  nativeAvg*nativeA+(nativeRaw 756).2.2,
  nativeAvg*nativeA+(nativeRaw 757).2.2,
  nativeAvg*nativeA+(nativeRaw 758).2.2,
  nativeAvg*nativeA+(nativeRaw 759).2.2,
  nativeAvg*nativeA+(nativeRaw 760).2.2,
  nativeAvg*nativeA+(nativeRaw 761).2.2,
  nativeAvg*nativeA+(nativeRaw 762).2.2,
  nativeAvg*nativeA+(nativeRaw 763).2.2,
  nativeAvg*nativeA+(nativeRaw 764).2.2,
  nativeAvg*nativeA+(nativeRaw 765).2.2,
  nativeAvg*nativeA+(nativeRaw 766).2.2,
  nativeAvg*nativeA+(nativeRaw 767).2.2,
  nativeAvg*nativeA+(nativeRaw 768).2.2,
  nativeAvg*nativeA+(nativeRaw 769).2.2,
  nativeAvg*nativeA+(nativeRaw 770).2.2,
  nativeAvg*nativeA+(nativeRaw 771).2.2,
  nativeAvg*nativeA+(nativeRaw 772).2.2,
  nativeAvg*nativeA+(nativeRaw 773).2.2,
  nativeAvg*nativeA+(nativeRaw 774).2.2,
  nativeAvg*nativeA+(nativeRaw 775).2.2,
  nativeAvg*nativeA+(nativeRaw 776).2.2
]

def nativeHistoryStrong0736Start : ℚ × ℚ := ((211745665583950339626510461958685185293939777539/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280803969319527643060308498324408557495750417431634006823457/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0736End : ℚ × ℚ := ((1085506809381912300733748395090105166085320679/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820201002397227417100121608468092959597929663256766041782217/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0736Inputs_length : nativeHistoryStrong0736Inputs.length = 32 := rfl

theorem nativeHistoryStrong0736Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(745+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(745+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0736Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0736Inputs.getD i.val 0)*(nativeHistoryStrong0736Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0736_checked : nativeHistorySteps 9 736 32 nativeHistoryStrong0736Inputs nativeHistoryStrong0736Start = nativeHistoryStrong0736End := by
  decide +kernel

theorem nativeHistoryStrong0736Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0736Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0736Weight : nativeHistoryRatio^736 ≤ nativeHistoryStrong0736Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0736Real_bound : nativeHistoryReal 9 736 nativeHistoryStrong0736Inputs ≤ (nativeHistoryStrong0736End.2 : ℝ)-(nativeHistoryStrong0736Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0736Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0736Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0736Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0736Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0736Inputs.length) := nativeHistoryStrong0736Domains ⟨i,by simpa only [nativeHistoryStrong0736Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0736Inputs.length) := nativeHistoryStrong0736Roots ⟨i,by simpa only [nativeHistoryStrong0736Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0736Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 736 nativeHistoryStrong0736Inputs nativeHistoryStrong0736Start ht hd hr hw
  simpa only [nativeHistoryStrong0736Inputs_length,nativeHistoryStrong0736_checked] using hs

end ASDExplicitGamma.Numerics.Native
