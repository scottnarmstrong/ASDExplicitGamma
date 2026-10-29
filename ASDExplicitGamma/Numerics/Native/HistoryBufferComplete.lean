module
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0000
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0032
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0064
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0096
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0128
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0160
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0192
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0224
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0256
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0288
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0320
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0352
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0384
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0416
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0448
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0480
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0512
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0544
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0576
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0608
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0640
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0672
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0704
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0736
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0768
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0800
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0832
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0864
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0896
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0928
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0960
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer0992
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1024
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1056
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1088
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1120
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1152
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1184
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1216
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1248
public import ASDExplicitGamma.Numerics.Native.HistoryBuffer1280

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBufferCompletePrefix0 : List ℚ := []

theorem nativeHistoryBufferCompletePrefix0_length : nativeHistoryBufferCompletePrefix0.length = 0 := rfl

theorem nativeHistoryBufferCompletePrefix0_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix0 ≤ (nativeHistoryBuffer0000Start.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  simp only [nativeHistoryBufferCompletePrefix0,nativeHistoryReal,sub_self,le_refl]

def nativeHistoryBufferCompletePrefix1 : List ℚ := nativeHistoryBufferCompletePrefix0 ++ nativeHistoryBuffer0000Inputs

theorem nativeHistoryBufferCompletePrefix1_length : nativeHistoryBufferCompletePrefix1.length = 32 := by
  rw [nativeHistoryBufferCompletePrefix1,List.length_append,nativeHistoryBufferCompletePrefix0_length,nativeHistoryBuffer0000Inputs_length]

theorem nativeHistoryBufferCompletePrefix1_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix1 ≤ (nativeHistoryBuffer0000End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix1,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix0_length]
  have hs : nativeHistoryBuffer0000Start.2 = nativeHistoryBuffer0000Start.2 := by decide +kernel
  have hb := nativeHistoryBuffer0000Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix0_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix2 : List ℚ := nativeHistoryBufferCompletePrefix1 ++ nativeHistoryBuffer0032Inputs

theorem nativeHistoryBufferCompletePrefix2_length : nativeHistoryBufferCompletePrefix2.length = 64 := by
  rw [nativeHistoryBufferCompletePrefix2,List.length_append,nativeHistoryBufferCompletePrefix1_length,nativeHistoryBuffer0032Inputs_length]

theorem nativeHistoryBufferCompletePrefix2_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix2 ≤ (nativeHistoryBuffer0032End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix2,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix1_length]
  have hs : nativeHistoryBuffer0032Start.2 = nativeHistoryBuffer0000End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0032Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix1_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix3 : List ℚ := nativeHistoryBufferCompletePrefix2 ++ nativeHistoryBuffer0064Inputs

theorem nativeHistoryBufferCompletePrefix3_length : nativeHistoryBufferCompletePrefix3.length = 96 := by
  rw [nativeHistoryBufferCompletePrefix3,List.length_append,nativeHistoryBufferCompletePrefix2_length,nativeHistoryBuffer0064Inputs_length]

theorem nativeHistoryBufferCompletePrefix3_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix3 ≤ (nativeHistoryBuffer0064End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix3,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix2_length]
  have hs : nativeHistoryBuffer0064Start.2 = nativeHistoryBuffer0032End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0064Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix2_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix4 : List ℚ := nativeHistoryBufferCompletePrefix3 ++ nativeHistoryBuffer0096Inputs

theorem nativeHistoryBufferCompletePrefix4_length : nativeHistoryBufferCompletePrefix4.length = 128 := by
  rw [nativeHistoryBufferCompletePrefix4,List.length_append,nativeHistoryBufferCompletePrefix3_length,nativeHistoryBuffer0096Inputs_length]

theorem nativeHistoryBufferCompletePrefix4_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix4 ≤ (nativeHistoryBuffer0096End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix4,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix3_length]
  have hs : nativeHistoryBuffer0096Start.2 = nativeHistoryBuffer0064End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0096Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix3_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix5 : List ℚ := nativeHistoryBufferCompletePrefix4 ++ nativeHistoryBuffer0128Inputs

theorem nativeHistoryBufferCompletePrefix5_length : nativeHistoryBufferCompletePrefix5.length = 160 := by
  rw [nativeHistoryBufferCompletePrefix5,List.length_append,nativeHistoryBufferCompletePrefix4_length,nativeHistoryBuffer0128Inputs_length]

theorem nativeHistoryBufferCompletePrefix5_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix5 ≤ (nativeHistoryBuffer0128End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix5,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix4_length]
  have hs : nativeHistoryBuffer0128Start.2 = nativeHistoryBuffer0096End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0128Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix4_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix6 : List ℚ := nativeHistoryBufferCompletePrefix5 ++ nativeHistoryBuffer0160Inputs

theorem nativeHistoryBufferCompletePrefix6_length : nativeHistoryBufferCompletePrefix6.length = 192 := by
  rw [nativeHistoryBufferCompletePrefix6,List.length_append,nativeHistoryBufferCompletePrefix5_length,nativeHistoryBuffer0160Inputs_length]

theorem nativeHistoryBufferCompletePrefix6_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix6 ≤ (nativeHistoryBuffer0160End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix6,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix5_length]
  have hs : nativeHistoryBuffer0160Start.2 = nativeHistoryBuffer0128End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0160Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix5_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix7 : List ℚ := nativeHistoryBufferCompletePrefix6 ++ nativeHistoryBuffer0192Inputs

theorem nativeHistoryBufferCompletePrefix7_length : nativeHistoryBufferCompletePrefix7.length = 224 := by
  rw [nativeHistoryBufferCompletePrefix7,List.length_append,nativeHistoryBufferCompletePrefix6_length,nativeHistoryBuffer0192Inputs_length]

theorem nativeHistoryBufferCompletePrefix7_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix7 ≤ (nativeHistoryBuffer0192End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix7,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix6_length]
  have hs : nativeHistoryBuffer0192Start.2 = nativeHistoryBuffer0160End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0192Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix6_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix8 : List ℚ := nativeHistoryBufferCompletePrefix7 ++ nativeHistoryBuffer0224Inputs

theorem nativeHistoryBufferCompletePrefix8_length : nativeHistoryBufferCompletePrefix8.length = 256 := by
  rw [nativeHistoryBufferCompletePrefix8,List.length_append,nativeHistoryBufferCompletePrefix7_length,nativeHistoryBuffer0224Inputs_length]

theorem nativeHistoryBufferCompletePrefix8_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix8 ≤ (nativeHistoryBuffer0224End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix8,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix7_length]
  have hs : nativeHistoryBuffer0224Start.2 = nativeHistoryBuffer0192End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0224Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix7_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix9 : List ℚ := nativeHistoryBufferCompletePrefix8 ++ nativeHistoryBuffer0256Inputs

theorem nativeHistoryBufferCompletePrefix9_length : nativeHistoryBufferCompletePrefix9.length = 288 := by
  rw [nativeHistoryBufferCompletePrefix9,List.length_append,nativeHistoryBufferCompletePrefix8_length,nativeHistoryBuffer0256Inputs_length]

theorem nativeHistoryBufferCompletePrefix9_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix9 ≤ (nativeHistoryBuffer0256End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix9,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix8_length]
  have hs : nativeHistoryBuffer0256Start.2 = nativeHistoryBuffer0224End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0256Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix8_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix10 : List ℚ := nativeHistoryBufferCompletePrefix9 ++ nativeHistoryBuffer0288Inputs

theorem nativeHistoryBufferCompletePrefix10_length : nativeHistoryBufferCompletePrefix10.length = 320 := by
  rw [nativeHistoryBufferCompletePrefix10,List.length_append,nativeHistoryBufferCompletePrefix9_length,nativeHistoryBuffer0288Inputs_length]

theorem nativeHistoryBufferCompletePrefix10_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix10 ≤ (nativeHistoryBuffer0288End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix10,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix9_length]
  have hs : nativeHistoryBuffer0288Start.2 = nativeHistoryBuffer0256End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0288Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix9_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix11 : List ℚ := nativeHistoryBufferCompletePrefix10 ++ nativeHistoryBuffer0320Inputs

theorem nativeHistoryBufferCompletePrefix11_length : nativeHistoryBufferCompletePrefix11.length = 352 := by
  rw [nativeHistoryBufferCompletePrefix11,List.length_append,nativeHistoryBufferCompletePrefix10_length,nativeHistoryBuffer0320Inputs_length]

theorem nativeHistoryBufferCompletePrefix11_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix11 ≤ (nativeHistoryBuffer0320End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix11,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix10_length]
  have hs : nativeHistoryBuffer0320Start.2 = nativeHistoryBuffer0288End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0320Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix10_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix12 : List ℚ := nativeHistoryBufferCompletePrefix11 ++ nativeHistoryBuffer0352Inputs

theorem nativeHistoryBufferCompletePrefix12_length : nativeHistoryBufferCompletePrefix12.length = 384 := by
  rw [nativeHistoryBufferCompletePrefix12,List.length_append,nativeHistoryBufferCompletePrefix11_length,nativeHistoryBuffer0352Inputs_length]

theorem nativeHistoryBufferCompletePrefix12_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix12 ≤ (nativeHistoryBuffer0352End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix12,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix11_length]
  have hs : nativeHistoryBuffer0352Start.2 = nativeHistoryBuffer0320End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0352Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix11_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix13 : List ℚ := nativeHistoryBufferCompletePrefix12 ++ nativeHistoryBuffer0384Inputs

theorem nativeHistoryBufferCompletePrefix13_length : nativeHistoryBufferCompletePrefix13.length = 416 := by
  rw [nativeHistoryBufferCompletePrefix13,List.length_append,nativeHistoryBufferCompletePrefix12_length,nativeHistoryBuffer0384Inputs_length]

theorem nativeHistoryBufferCompletePrefix13_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix13 ≤ (nativeHistoryBuffer0384End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix13,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix12_length]
  have hs : nativeHistoryBuffer0384Start.2 = nativeHistoryBuffer0352End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0384Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix12_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix14 : List ℚ := nativeHistoryBufferCompletePrefix13 ++ nativeHistoryBuffer0416Inputs

theorem nativeHistoryBufferCompletePrefix14_length : nativeHistoryBufferCompletePrefix14.length = 448 := by
  rw [nativeHistoryBufferCompletePrefix14,List.length_append,nativeHistoryBufferCompletePrefix13_length,nativeHistoryBuffer0416Inputs_length]

theorem nativeHistoryBufferCompletePrefix14_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix14 ≤ (nativeHistoryBuffer0416End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix14,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix13_length]
  have hs : nativeHistoryBuffer0416Start.2 = nativeHistoryBuffer0384End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0416Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix13_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix15 : List ℚ := nativeHistoryBufferCompletePrefix14 ++ nativeHistoryBuffer0448Inputs

theorem nativeHistoryBufferCompletePrefix15_length : nativeHistoryBufferCompletePrefix15.length = 480 := by
  rw [nativeHistoryBufferCompletePrefix15,List.length_append,nativeHistoryBufferCompletePrefix14_length,nativeHistoryBuffer0448Inputs_length]

theorem nativeHistoryBufferCompletePrefix15_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix15 ≤ (nativeHistoryBuffer0448End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix15,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix14_length]
  have hs : nativeHistoryBuffer0448Start.2 = nativeHistoryBuffer0416End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0448Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix14_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix16 : List ℚ := nativeHistoryBufferCompletePrefix15 ++ nativeHistoryBuffer0480Inputs

theorem nativeHistoryBufferCompletePrefix16_length : nativeHistoryBufferCompletePrefix16.length = 512 := by
  rw [nativeHistoryBufferCompletePrefix16,List.length_append,nativeHistoryBufferCompletePrefix15_length,nativeHistoryBuffer0480Inputs_length]

theorem nativeHistoryBufferCompletePrefix16_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix16 ≤ (nativeHistoryBuffer0480End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix16,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix15_length]
  have hs : nativeHistoryBuffer0480Start.2 = nativeHistoryBuffer0448End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0480Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix15_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix17 : List ℚ := nativeHistoryBufferCompletePrefix16 ++ nativeHistoryBuffer0512Inputs

theorem nativeHistoryBufferCompletePrefix17_length : nativeHistoryBufferCompletePrefix17.length = 544 := by
  rw [nativeHistoryBufferCompletePrefix17,List.length_append,nativeHistoryBufferCompletePrefix16_length,nativeHistoryBuffer0512Inputs_length]

theorem nativeHistoryBufferCompletePrefix17_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix17 ≤ (nativeHistoryBuffer0512End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix17,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix16_length]
  have hs : nativeHistoryBuffer0512Start.2 = nativeHistoryBuffer0480End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0512Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix16_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix18 : List ℚ := nativeHistoryBufferCompletePrefix17 ++ nativeHistoryBuffer0544Inputs

theorem nativeHistoryBufferCompletePrefix18_length : nativeHistoryBufferCompletePrefix18.length = 576 := by
  rw [nativeHistoryBufferCompletePrefix18,List.length_append,nativeHistoryBufferCompletePrefix17_length,nativeHistoryBuffer0544Inputs_length]

theorem nativeHistoryBufferCompletePrefix18_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix18 ≤ (nativeHistoryBuffer0544End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix18,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix17_length]
  have hs : nativeHistoryBuffer0544Start.2 = nativeHistoryBuffer0512End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0544Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix17_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix19 : List ℚ := nativeHistoryBufferCompletePrefix18 ++ nativeHistoryBuffer0576Inputs

theorem nativeHistoryBufferCompletePrefix19_length : nativeHistoryBufferCompletePrefix19.length = 608 := by
  rw [nativeHistoryBufferCompletePrefix19,List.length_append,nativeHistoryBufferCompletePrefix18_length,nativeHistoryBuffer0576Inputs_length]

theorem nativeHistoryBufferCompletePrefix19_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix19 ≤ (nativeHistoryBuffer0576End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix19,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix18_length]
  have hs : nativeHistoryBuffer0576Start.2 = nativeHistoryBuffer0544End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0576Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix18_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix20 : List ℚ := nativeHistoryBufferCompletePrefix19 ++ nativeHistoryBuffer0608Inputs

theorem nativeHistoryBufferCompletePrefix20_length : nativeHistoryBufferCompletePrefix20.length = 640 := by
  rw [nativeHistoryBufferCompletePrefix20,List.length_append,nativeHistoryBufferCompletePrefix19_length,nativeHistoryBuffer0608Inputs_length]

theorem nativeHistoryBufferCompletePrefix20_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix20 ≤ (nativeHistoryBuffer0608End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix20,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix19_length]
  have hs : nativeHistoryBuffer0608Start.2 = nativeHistoryBuffer0576End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0608Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix19_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix21 : List ℚ := nativeHistoryBufferCompletePrefix20 ++ nativeHistoryBuffer0640Inputs

theorem nativeHistoryBufferCompletePrefix21_length : nativeHistoryBufferCompletePrefix21.length = 672 := by
  rw [nativeHistoryBufferCompletePrefix21,List.length_append,nativeHistoryBufferCompletePrefix20_length,nativeHistoryBuffer0640Inputs_length]

theorem nativeHistoryBufferCompletePrefix21_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix21 ≤ (nativeHistoryBuffer0640End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix21,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix20_length]
  have hs : nativeHistoryBuffer0640Start.2 = nativeHistoryBuffer0608End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0640Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix20_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix22 : List ℚ := nativeHistoryBufferCompletePrefix21 ++ nativeHistoryBuffer0672Inputs

theorem nativeHistoryBufferCompletePrefix22_length : nativeHistoryBufferCompletePrefix22.length = 704 := by
  rw [nativeHistoryBufferCompletePrefix22,List.length_append,nativeHistoryBufferCompletePrefix21_length,nativeHistoryBuffer0672Inputs_length]

theorem nativeHistoryBufferCompletePrefix22_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix22 ≤ (nativeHistoryBuffer0672End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix22,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix21_length]
  have hs : nativeHistoryBuffer0672Start.2 = nativeHistoryBuffer0640End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0672Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix21_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix23 : List ℚ := nativeHistoryBufferCompletePrefix22 ++ nativeHistoryBuffer0704Inputs

theorem nativeHistoryBufferCompletePrefix23_length : nativeHistoryBufferCompletePrefix23.length = 736 := by
  rw [nativeHistoryBufferCompletePrefix23,List.length_append,nativeHistoryBufferCompletePrefix22_length,nativeHistoryBuffer0704Inputs_length]

theorem nativeHistoryBufferCompletePrefix23_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix23 ≤ (nativeHistoryBuffer0704End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix23,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix22_length]
  have hs : nativeHistoryBuffer0704Start.2 = nativeHistoryBuffer0672End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0704Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix22_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix24 : List ℚ := nativeHistoryBufferCompletePrefix23 ++ nativeHistoryBuffer0736Inputs

theorem nativeHistoryBufferCompletePrefix24_length : nativeHistoryBufferCompletePrefix24.length = 768 := by
  rw [nativeHistoryBufferCompletePrefix24,List.length_append,nativeHistoryBufferCompletePrefix23_length,nativeHistoryBuffer0736Inputs_length]

theorem nativeHistoryBufferCompletePrefix24_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix24 ≤ (nativeHistoryBuffer0736End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix24,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix23_length]
  have hs : nativeHistoryBuffer0736Start.2 = nativeHistoryBuffer0704End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0736Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix23_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix25 : List ℚ := nativeHistoryBufferCompletePrefix24 ++ nativeHistoryBuffer0768Inputs

theorem nativeHistoryBufferCompletePrefix25_length : nativeHistoryBufferCompletePrefix25.length = 800 := by
  rw [nativeHistoryBufferCompletePrefix25,List.length_append,nativeHistoryBufferCompletePrefix24_length,nativeHistoryBuffer0768Inputs_length]

theorem nativeHistoryBufferCompletePrefix25_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix25 ≤ (nativeHistoryBuffer0768End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix25,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix24_length]
  have hs : nativeHistoryBuffer0768Start.2 = nativeHistoryBuffer0736End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0768Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix24_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix26 : List ℚ := nativeHistoryBufferCompletePrefix25 ++ nativeHistoryBuffer0800Inputs

theorem nativeHistoryBufferCompletePrefix26_length : nativeHistoryBufferCompletePrefix26.length = 832 := by
  rw [nativeHistoryBufferCompletePrefix26,List.length_append,nativeHistoryBufferCompletePrefix25_length,nativeHistoryBuffer0800Inputs_length]

theorem nativeHistoryBufferCompletePrefix26_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix26 ≤ (nativeHistoryBuffer0800End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix26,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix25_length]
  have hs : nativeHistoryBuffer0800Start.2 = nativeHistoryBuffer0768End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0800Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix25_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix27 : List ℚ := nativeHistoryBufferCompletePrefix26 ++ nativeHistoryBuffer0832Inputs

theorem nativeHistoryBufferCompletePrefix27_length : nativeHistoryBufferCompletePrefix27.length = 864 := by
  rw [nativeHistoryBufferCompletePrefix27,List.length_append,nativeHistoryBufferCompletePrefix26_length,nativeHistoryBuffer0832Inputs_length]

theorem nativeHistoryBufferCompletePrefix27_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix27 ≤ (nativeHistoryBuffer0832End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix27,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix26_length]
  have hs : nativeHistoryBuffer0832Start.2 = nativeHistoryBuffer0800End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0832Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix26_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix28 : List ℚ := nativeHistoryBufferCompletePrefix27 ++ nativeHistoryBuffer0864Inputs

theorem nativeHistoryBufferCompletePrefix28_length : nativeHistoryBufferCompletePrefix28.length = 896 := by
  rw [nativeHistoryBufferCompletePrefix28,List.length_append,nativeHistoryBufferCompletePrefix27_length,nativeHistoryBuffer0864Inputs_length]

theorem nativeHistoryBufferCompletePrefix28_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix28 ≤ (nativeHistoryBuffer0864End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix28,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix27_length]
  have hs : nativeHistoryBuffer0864Start.2 = nativeHistoryBuffer0832End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0864Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix27_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix29 : List ℚ := nativeHistoryBufferCompletePrefix28 ++ nativeHistoryBuffer0896Inputs

theorem nativeHistoryBufferCompletePrefix29_length : nativeHistoryBufferCompletePrefix29.length = 928 := by
  rw [nativeHistoryBufferCompletePrefix29,List.length_append,nativeHistoryBufferCompletePrefix28_length,nativeHistoryBuffer0896Inputs_length]

theorem nativeHistoryBufferCompletePrefix29_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix29 ≤ (nativeHistoryBuffer0896End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix29,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix28_length]
  have hs : nativeHistoryBuffer0896Start.2 = nativeHistoryBuffer0864End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0896Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix28_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix30 : List ℚ := nativeHistoryBufferCompletePrefix29 ++ nativeHistoryBuffer0928Inputs

theorem nativeHistoryBufferCompletePrefix30_length : nativeHistoryBufferCompletePrefix30.length = 960 := by
  rw [nativeHistoryBufferCompletePrefix30,List.length_append,nativeHistoryBufferCompletePrefix29_length,nativeHistoryBuffer0928Inputs_length]

theorem nativeHistoryBufferCompletePrefix30_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix30 ≤ (nativeHistoryBuffer0928End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix30,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix29_length]
  have hs : nativeHistoryBuffer0928Start.2 = nativeHistoryBuffer0896End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0928Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix29_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix31 : List ℚ := nativeHistoryBufferCompletePrefix30 ++ nativeHistoryBuffer0960Inputs

theorem nativeHistoryBufferCompletePrefix31_length : nativeHistoryBufferCompletePrefix31.length = 992 := by
  rw [nativeHistoryBufferCompletePrefix31,List.length_append,nativeHistoryBufferCompletePrefix30_length,nativeHistoryBuffer0960Inputs_length]

theorem nativeHistoryBufferCompletePrefix31_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix31 ≤ (nativeHistoryBuffer0960End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix31,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix30_length]
  have hs : nativeHistoryBuffer0960Start.2 = nativeHistoryBuffer0928End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0960Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix30_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix32 : List ℚ := nativeHistoryBufferCompletePrefix31 ++ nativeHistoryBuffer0992Inputs

theorem nativeHistoryBufferCompletePrefix32_length : nativeHistoryBufferCompletePrefix32.length = 1024 := by
  rw [nativeHistoryBufferCompletePrefix32,List.length_append,nativeHistoryBufferCompletePrefix31_length,nativeHistoryBuffer0992Inputs_length]

theorem nativeHistoryBufferCompletePrefix32_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix32 ≤ (nativeHistoryBuffer0992End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix32,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix31_length]
  have hs : nativeHistoryBuffer0992Start.2 = nativeHistoryBuffer0960End.2 := by decide +kernel
  have hb := nativeHistoryBuffer0992Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix31_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix33 : List ℚ := nativeHistoryBufferCompletePrefix32 ++ nativeHistoryBuffer1024Inputs

theorem nativeHistoryBufferCompletePrefix33_length : nativeHistoryBufferCompletePrefix33.length = 1056 := by
  rw [nativeHistoryBufferCompletePrefix33,List.length_append,nativeHistoryBufferCompletePrefix32_length,nativeHistoryBuffer1024Inputs_length]

theorem nativeHistoryBufferCompletePrefix33_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix33 ≤ (nativeHistoryBuffer1024End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix33,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix32_length]
  have hs : nativeHistoryBuffer1024Start.2 = nativeHistoryBuffer0992End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1024Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix32_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix34 : List ℚ := nativeHistoryBufferCompletePrefix33 ++ nativeHistoryBuffer1056Inputs

theorem nativeHistoryBufferCompletePrefix34_length : nativeHistoryBufferCompletePrefix34.length = 1088 := by
  rw [nativeHistoryBufferCompletePrefix34,List.length_append,nativeHistoryBufferCompletePrefix33_length,nativeHistoryBuffer1056Inputs_length]

theorem nativeHistoryBufferCompletePrefix34_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix34 ≤ (nativeHistoryBuffer1056End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix34,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix33_length]
  have hs : nativeHistoryBuffer1056Start.2 = nativeHistoryBuffer1024End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1056Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix33_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix35 : List ℚ := nativeHistoryBufferCompletePrefix34 ++ nativeHistoryBuffer1088Inputs

theorem nativeHistoryBufferCompletePrefix35_length : nativeHistoryBufferCompletePrefix35.length = 1120 := by
  rw [nativeHistoryBufferCompletePrefix35,List.length_append,nativeHistoryBufferCompletePrefix34_length,nativeHistoryBuffer1088Inputs_length]

theorem nativeHistoryBufferCompletePrefix35_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix35 ≤ (nativeHistoryBuffer1088End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix35,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix34_length]
  have hs : nativeHistoryBuffer1088Start.2 = nativeHistoryBuffer1056End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1088Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix34_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix36 : List ℚ := nativeHistoryBufferCompletePrefix35 ++ nativeHistoryBuffer1120Inputs

theorem nativeHistoryBufferCompletePrefix36_length : nativeHistoryBufferCompletePrefix36.length = 1152 := by
  rw [nativeHistoryBufferCompletePrefix36,List.length_append,nativeHistoryBufferCompletePrefix35_length,nativeHistoryBuffer1120Inputs_length]

theorem nativeHistoryBufferCompletePrefix36_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix36 ≤ (nativeHistoryBuffer1120End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix36,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix35_length]
  have hs : nativeHistoryBuffer1120Start.2 = nativeHistoryBuffer1088End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1120Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix35_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix37 : List ℚ := nativeHistoryBufferCompletePrefix36 ++ nativeHistoryBuffer1152Inputs

theorem nativeHistoryBufferCompletePrefix37_length : nativeHistoryBufferCompletePrefix37.length = 1184 := by
  rw [nativeHistoryBufferCompletePrefix37,List.length_append,nativeHistoryBufferCompletePrefix36_length,nativeHistoryBuffer1152Inputs_length]

theorem nativeHistoryBufferCompletePrefix37_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix37 ≤ (nativeHistoryBuffer1152End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix37,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix36_length]
  have hs : nativeHistoryBuffer1152Start.2 = nativeHistoryBuffer1120End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1152Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix36_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix38 : List ℚ := nativeHistoryBufferCompletePrefix37 ++ nativeHistoryBuffer1184Inputs

theorem nativeHistoryBufferCompletePrefix38_length : nativeHistoryBufferCompletePrefix38.length = 1216 := by
  rw [nativeHistoryBufferCompletePrefix38,List.length_append,nativeHistoryBufferCompletePrefix37_length,nativeHistoryBuffer1184Inputs_length]

theorem nativeHistoryBufferCompletePrefix38_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix38 ≤ (nativeHistoryBuffer1184End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix38,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix37_length]
  have hs : nativeHistoryBuffer1184Start.2 = nativeHistoryBuffer1152End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1184Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix37_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix39 : List ℚ := nativeHistoryBufferCompletePrefix38 ++ nativeHistoryBuffer1216Inputs

theorem nativeHistoryBufferCompletePrefix39_length : nativeHistoryBufferCompletePrefix39.length = 1248 := by
  rw [nativeHistoryBufferCompletePrefix39,List.length_append,nativeHistoryBufferCompletePrefix38_length,nativeHistoryBuffer1216Inputs_length]

theorem nativeHistoryBufferCompletePrefix39_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix39 ≤ (nativeHistoryBuffer1216End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix39,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix38_length]
  have hs : nativeHistoryBuffer1216Start.2 = nativeHistoryBuffer1184End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1216Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix38_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix40 : List ℚ := nativeHistoryBufferCompletePrefix39 ++ nativeHistoryBuffer1248Inputs

theorem nativeHistoryBufferCompletePrefix40_length : nativeHistoryBufferCompletePrefix40.length = 1280 := by
  rw [nativeHistoryBufferCompletePrefix40,List.length_append,nativeHistoryBufferCompletePrefix39_length,nativeHistoryBuffer1248Inputs_length]

theorem nativeHistoryBufferCompletePrefix40_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix40 ≤ (nativeHistoryBuffer1248End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix40,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix39_length]
  have hs : nativeHistoryBuffer1248Start.2 = nativeHistoryBuffer1216End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1248Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix39_real hb
  apply h.trans_eq
  ring

def nativeHistoryBufferCompletePrefix41 : List ℚ := nativeHistoryBufferCompletePrefix40 ++ nativeHistoryBuffer1280Inputs

theorem nativeHistoryBufferCompletePrefix41_length : nativeHistoryBufferCompletePrefix41.length = 1286 := by
  rw [nativeHistoryBufferCompletePrefix41,List.length_append,nativeHistoryBufferCompletePrefix40_length,nativeHistoryBuffer1280Inputs_length]

theorem nativeHistoryBufferCompletePrefix41_real : nativeHistoryReal 49 0 nativeHistoryBufferCompletePrefix41 ≤ (nativeHistoryBuffer1280End.2 : ℝ)-(nativeHistoryBuffer0000Start.2 : ℝ) := by
  rw [nativeHistoryBufferCompletePrefix41,nativeHistoryReal_append,nativeHistoryBufferCompletePrefix40_length]
  have hs : nativeHistoryBuffer1280Start.2 = nativeHistoryBuffer1248End.2 := by decide +kernel
  have hb := nativeHistoryBuffer1280Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryBufferCompletePrefix40_real hb
  apply h.trans_eq
  ring

end ASDExplicitGamma.Numerics.Native
