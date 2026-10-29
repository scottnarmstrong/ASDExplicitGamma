module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0416Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 465).2.2,
  nativeAvg*nativeA+(nativeRaw 466).2.2,
  nativeAvg*nativeA+(nativeRaw 467).2.2,
  nativeAvg*nativeA+(nativeRaw 468).2.2,
  nativeAvg*nativeA+(nativeRaw 469).2.2,
  nativeAvg*nativeA+(nativeRaw 470).2.2,
  nativeAvg*nativeA+(nativeRaw 471).2.2,
  nativeAvg*nativeA+(nativeRaw 472).2.2,
  nativeAvg*nativeA+(nativeRaw 473).2.2,
  nativeAvg*nativeA+(nativeRaw 474).2.2,
  nativeAvg*nativeA+(nativeRaw 475).2.2,
  nativeAvg*nativeA+(nativeRaw 476).2.2,
  nativeAvg*nativeA+(nativeRaw 477).2.2,
  nativeAvg*nativeA+(nativeRaw 478).2.2,
  nativeAvg*nativeA+(nativeRaw 479).2.2,
  nativeAvg*nativeA+(nativeRaw 480).2.2,
  nativeAvg*nativeA+(nativeRaw 481).2.2,
  nativeAvg*nativeA+(nativeRaw 482).2.2,
  nativeAvg*nativeA+(nativeRaw 483).2.2,
  nativeAvg*nativeA+(nativeRaw 484).2.2,
  nativeAvg*nativeA+(nativeRaw 485).2.2,
  nativeAvg*nativeA+(nativeRaw 486).2.2,
  nativeAvg*nativeA+(nativeRaw 487).2.2,
  nativeAvg*nativeA+(nativeRaw 488).2.2,
  nativeAvg*nativeA+(nativeRaw 489).2.2,
  nativeAvg*nativeA+(nativeRaw 490).2.2,
  nativeAvg*nativeA+(nativeRaw 491).2.2,
  nativeAvg*nativeA+(nativeRaw 492).2.2,
  nativeAvg*nativeA+(nativeRaw 493).2.2,
  nativeAvg*nativeA+(nativeRaw 494).2.2,
  nativeAvg*nativeA+(nativeRaw 495).2.2,
  nativeAvg*nativeA+(nativeRaw 496).2.2
]

def nativeHistoryBuffer0416Start : ℚ × ℚ := ((675607232920920928789347869936852715201793472232371387794890463299287/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11713264740679284981361132479476321124227376286181433045673339099913397082705527481774101100296483917/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0416End : ℚ × ℚ := ((86586926086637091678870978027611080834722316789952727645292792882353/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663141076876971368119708953716772780181381262221612298008888544288236806665769/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0416Inputs_length : nativeHistoryBuffer0416Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0416Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(465+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(465+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0416Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0416Inputs.getD i.val 0)*(nativeHistoryBuffer0416Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0416_checked : nativeHistorySteps 49 416 32 nativeHistoryBuffer0416Inputs nativeHistoryBuffer0416Start = nativeHistoryBuffer0416End := by
  decide +kernel

theorem nativeHistoryBuffer0416Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0416Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0416Weight : nativeHistoryRatio^416 ≤ nativeHistoryBuffer0416Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0416Real_bound : nativeHistoryReal 49 416 nativeHistoryBuffer0416Inputs ≤ (nativeHistoryBuffer0416End.2 : ℝ)-(nativeHistoryBuffer0416Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0416Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0416Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0416Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0416Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0416Inputs.length) := nativeHistoryBuffer0416Domains ⟨i,by simpa only [nativeHistoryBuffer0416Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0416Inputs.length) := nativeHistoryBuffer0416Roots ⟨i,by simpa only [nativeHistoryBuffer0416Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0416Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 416 nativeHistoryBuffer0416Inputs nativeHistoryBuffer0416Start ht hd hr hw
  simpa only [nativeHistoryBuffer0416Inputs_length,nativeHistoryBuffer0416_checked] using hs

end ASDExplicitGamma.Numerics.Native
