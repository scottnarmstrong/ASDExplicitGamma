module
public import ASDExplicitGamma.Numerics.Native.HistoryStrongComplete
public import ASDExplicitGamma.Numerics.Native.HistoryBufferComplete
public import ASDExplicitGamma.Numerics.Native.ReturnScalars
public import ASDExplicitGamma.Numerics.Native.SourceTail

/-! Complete native endpoint returns: all 1286 finite terms and the exact raw-tail formula. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeStrongHistoryReturn : ℚ := (297345708073836901798674430899674774708326009029086375186885635508078049176075808932750941826588617/312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

noncomputable def nativeSourceStrongHistory : ℝ := nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix41+(nativeSourceHistoryTail 9 : ℝ)

theorem nativeStrongHistoryReturnInitial : nativeHistoryStrong0000Start = (1,0) := by
  decide +kernel

theorem nativeStrongHistoryReturnSum : nativeHistoryStrong1280End.2+nativeStrongTail = nativeStrongHistoryReturn := by
  decide +kernel

theorem nativeStrongHistoryReturn_bound : nativeSourceStrongHistory ≤ (nativeStrongHistoryReturn : ℝ) := by
  have hf := nativeHistoryStrongCompletePrefix41_real
  have hz : (nativeHistoryStrong0000Start.2 : ℝ) = 0 := by rw [nativeStrongHistoryReturnInitial]; norm_num
  rw [hz,sub_zero] at hf
  have ht := (Rat.cast_le (K := ℝ)).2 nativeSourceStrongTail_le
  have h := add_le_add hf ht
  simpa only [nativeSourceStrongHistory,← Rat.cast_add,nativeStrongHistoryReturnSum] using h

def nativeBufferHistoryReturn : ℚ := (29283161851698212453402831572768687242739494862345550184180984697325967826374695432191932784375666847/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

noncomputable def nativeSourceBufferHistory : ℝ := nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix41+(nativeSourceHistoryTail 49 : ℝ)

theorem nativeBufferHistoryReturnInitial : nativeHistoryBuffer0000Start = (1,0) := by
  decide +kernel

theorem nativeBufferHistoryReturnSum : nativeHistoryBuffer1280End.2+nativeBufferTail = nativeBufferHistoryReturn := by
  decide +kernel

theorem nativeBufferHistoryReturn_bound : nativeSourceBufferHistory ≤ (nativeBufferHistoryReturn : ℝ) := by
  have hf := nativeHistoryBufferCompletePrefix41_real
  have hz : (nativeHistoryBuffer0000Start.2 : ℝ) = 0 := by rw [nativeBufferHistoryReturnInitial]; norm_num
  rw [hz,sub_zero] at hf
  have ht := (Rat.cast_le (K := ℝ)).2 nativeSourceBufferTail_le
  have h := add_le_add hf ht
  simpa only [nativeSourceBufferHistory,← Rat.cast_add,nativeBufferHistoryReturnSum] using h

theorem nativeStrongHistoryReturn_caps : nativeStrongHistoryReturn < (9515063/10^7 : ℚ) ∧ (9515063/10^7 : ℚ) < 95151/100000 ∧ (95151/100000 : ℚ) < 2379/2500 := by
  decide +kernel

/-- The complete buffer-history endpoint certificate is sharper than the
six-digit return threshold used by NA-RETURNS. -/
theorem nativeBufferHistoryReturn_sharp :
    nativeBufferHistoryReturn < (5856633/10^6 : ℚ) := by
  decide +kernel

/-- The complete buffer-mean endpoint certificate is sharper than the
six-digit return threshold used by NA-RETURNS. -/
theorem nativeBufferMeanReturn_sharp :
    nativeBufferMeanReturn < (317279/10^6 : ℚ) := by
  decide +kernel

/-- The four endpoint replay values satisfy the strict source return
thresholds, with the two buffer outputs using their tighter rational caps. -/
theorem native_all_sharp_return_values :
    nativeSourceStrongHistory < (9515063/10^7 : ℝ) ∧
    nativeFrameReal (((11/10)*(2*nativeGamma*(9 : ℕ)) : ℚ) : ℝ)
      (nativeHeat009Result.1 : ℝ) < (2012545/10^7 : ℝ) ∧
    nativeSourceBufferHistory < (5856633/10^6 : ℝ) ∧
    (nativeE (98*nativeGamma) : ℝ)*(nativeHeat049Result.2 : ℝ) <
      (317279/10^6 : ℝ) := by
  have hs0 := nativeStrongHistoryReturn_bound.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 nativeStrongHistoryReturn_caps.1)
  have hs : nativeSourceStrongHistory < (9515063/10^7 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hs0
  have hr0 := nativeRootReturn_bound
  have hr := hr0.trans_lt ((Rat.cast_lt (K := ℝ)).2 nativeRootReturn_caps.1)
  have hb0 := nativeBufferHistoryReturn_bound
  have hb := hb0.trans_lt ((Rat.cast_lt (K := ℝ)).2 nativeBufferHistoryReturn_sharp)
  have hm0 := nativeBufferMeanReturn_bound
  have hm := hm0.trans_lt ((Rat.cast_lt (K := ℝ)).2 nativeBufferMeanReturn_sharp)
  refine ⟨hs, ?_, ?_, ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hr
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hb
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hm

theorem native_all_return_caps : nativeSourceStrongHistory < (2379/2500 : ℝ) ∧
    nativeFrameReal (((11/10)*(2*nativeGamma*(9 : ℕ)) : ℚ) : ℝ) (nativeHeat009Result.1 : ℝ) < 2013/10000 ∧
    nativeSourceBufferHistory < 61/10 ∧
    (nativeE (98*nativeGamma) : ℝ)*(nativeHeat049Result.2 : ℝ) < 8/25 := by
  have hs : nativeStrongHistoryReturn < (2379/2500 : ℚ) := by decide +kernel
  have hr : nativeRootReturn < (2013/10000 : ℚ) := by decide +kernel
  have hb : nativeBufferHistoryReturn < (61/10 : ℚ) := by decide +kernel
  have hm : nativeBufferMeanReturn < (8/25 : ℚ) := by decide +kernel
  refine ⟨?_,?_,?_,?_⟩
  · have h := nativeStrongHistoryReturn_bound.trans_lt ((Rat.cast_lt (K := ℝ)).2 hs)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  · have h := nativeRootReturn_bound.trans_lt ((Rat.cast_lt (K := ℝ)).2 hr)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  · have h := nativeBufferHistoryReturn_bound.trans_lt ((Rat.cast_lt (K := ℝ)).2 hb)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  · have h := nativeBufferMeanReturn_bound.trans_lt ((Rat.cast_lt (K := ℝ)).2 hm)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h

end ASDExplicitGamma.Numerics.Native
