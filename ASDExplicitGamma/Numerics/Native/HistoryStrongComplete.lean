module
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0000
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0032
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0064
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0096
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0128
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0160
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0192
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0224
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0256
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0288
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0320
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0352
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0384
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0416
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0448
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0480
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0512
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0544
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0576
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0608
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0640
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0672
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0704
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0736
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0768
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0800
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0832
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0864
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0896
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0928
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0960
public import ASDExplicitGamma.Numerics.Native.HistoryStrong0992
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1024
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1056
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1088
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1120
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1152
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1184
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1216
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1248
public import ASDExplicitGamma.Numerics.Native.HistoryStrong1280

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrongCompletePrefix0 : List ℚ := []

theorem nativeHistoryStrongCompletePrefix0_length : nativeHistoryStrongCompletePrefix0.length = 0 := rfl

theorem nativeHistoryStrongCompletePrefix0_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix0 ≤ (nativeHistoryStrong0000Start.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  simp only [nativeHistoryStrongCompletePrefix0,nativeHistoryReal,sub_self,le_refl]

def nativeHistoryStrongCompletePrefix1 : List ℚ := nativeHistoryStrongCompletePrefix0 ++ nativeHistoryStrong0000Inputs

theorem nativeHistoryStrongCompletePrefix1_length : nativeHistoryStrongCompletePrefix1.length = 32 := by
  rw [nativeHistoryStrongCompletePrefix1,List.length_append,nativeHistoryStrongCompletePrefix0_length,nativeHistoryStrong0000Inputs_length]

theorem nativeHistoryStrongCompletePrefix1_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix1 ≤ (nativeHistoryStrong0000End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix1,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix0_length]
  have hs : nativeHistoryStrong0000Start.2 = nativeHistoryStrong0000Start.2 := by decide +kernel
  have hb := nativeHistoryStrong0000Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix0_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix2 : List ℚ := nativeHistoryStrongCompletePrefix1 ++ nativeHistoryStrong0032Inputs

theorem nativeHistoryStrongCompletePrefix2_length : nativeHistoryStrongCompletePrefix2.length = 64 := by
  rw [nativeHistoryStrongCompletePrefix2,List.length_append,nativeHistoryStrongCompletePrefix1_length,nativeHistoryStrong0032Inputs_length]

theorem nativeHistoryStrongCompletePrefix2_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix2 ≤ (nativeHistoryStrong0032End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix2,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix1_length]
  have hs : nativeHistoryStrong0032Start.2 = nativeHistoryStrong0000End.2 := by decide +kernel
  have hb := nativeHistoryStrong0032Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix1_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix3 : List ℚ := nativeHistoryStrongCompletePrefix2 ++ nativeHistoryStrong0064Inputs

theorem nativeHistoryStrongCompletePrefix3_length : nativeHistoryStrongCompletePrefix3.length = 96 := by
  rw [nativeHistoryStrongCompletePrefix3,List.length_append,nativeHistoryStrongCompletePrefix2_length,nativeHistoryStrong0064Inputs_length]

theorem nativeHistoryStrongCompletePrefix3_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix3 ≤ (nativeHistoryStrong0064End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix3,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix2_length]
  have hs : nativeHistoryStrong0064Start.2 = nativeHistoryStrong0032End.2 := by decide +kernel
  have hb := nativeHistoryStrong0064Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix2_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix4 : List ℚ := nativeHistoryStrongCompletePrefix3 ++ nativeHistoryStrong0096Inputs

theorem nativeHistoryStrongCompletePrefix4_length : nativeHistoryStrongCompletePrefix4.length = 128 := by
  rw [nativeHistoryStrongCompletePrefix4,List.length_append,nativeHistoryStrongCompletePrefix3_length,nativeHistoryStrong0096Inputs_length]

theorem nativeHistoryStrongCompletePrefix4_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix4 ≤ (nativeHistoryStrong0096End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix4,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix3_length]
  have hs : nativeHistoryStrong0096Start.2 = nativeHistoryStrong0064End.2 := by decide +kernel
  have hb := nativeHistoryStrong0096Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix3_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix5 : List ℚ := nativeHistoryStrongCompletePrefix4 ++ nativeHistoryStrong0128Inputs

theorem nativeHistoryStrongCompletePrefix5_length : nativeHistoryStrongCompletePrefix5.length = 160 := by
  rw [nativeHistoryStrongCompletePrefix5,List.length_append,nativeHistoryStrongCompletePrefix4_length,nativeHistoryStrong0128Inputs_length]

theorem nativeHistoryStrongCompletePrefix5_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix5 ≤ (nativeHistoryStrong0128End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix5,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix4_length]
  have hs : nativeHistoryStrong0128Start.2 = nativeHistoryStrong0096End.2 := by decide +kernel
  have hb := nativeHistoryStrong0128Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix4_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix6 : List ℚ := nativeHistoryStrongCompletePrefix5 ++ nativeHistoryStrong0160Inputs

theorem nativeHistoryStrongCompletePrefix6_length : nativeHistoryStrongCompletePrefix6.length = 192 := by
  rw [nativeHistoryStrongCompletePrefix6,List.length_append,nativeHistoryStrongCompletePrefix5_length,nativeHistoryStrong0160Inputs_length]

theorem nativeHistoryStrongCompletePrefix6_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix6 ≤ (nativeHistoryStrong0160End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix6,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix5_length]
  have hs : nativeHistoryStrong0160Start.2 = nativeHistoryStrong0128End.2 := by decide +kernel
  have hb := nativeHistoryStrong0160Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix5_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix7 : List ℚ := nativeHistoryStrongCompletePrefix6 ++ nativeHistoryStrong0192Inputs

theorem nativeHistoryStrongCompletePrefix7_length : nativeHistoryStrongCompletePrefix7.length = 224 := by
  rw [nativeHistoryStrongCompletePrefix7,List.length_append,nativeHistoryStrongCompletePrefix6_length,nativeHistoryStrong0192Inputs_length]

theorem nativeHistoryStrongCompletePrefix7_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix7 ≤ (nativeHistoryStrong0192End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix7,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix6_length]
  have hs : nativeHistoryStrong0192Start.2 = nativeHistoryStrong0160End.2 := by decide +kernel
  have hb := nativeHistoryStrong0192Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix6_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix8 : List ℚ := nativeHistoryStrongCompletePrefix7 ++ nativeHistoryStrong0224Inputs

theorem nativeHistoryStrongCompletePrefix8_length : nativeHistoryStrongCompletePrefix8.length = 256 := by
  rw [nativeHistoryStrongCompletePrefix8,List.length_append,nativeHistoryStrongCompletePrefix7_length,nativeHistoryStrong0224Inputs_length]

theorem nativeHistoryStrongCompletePrefix8_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix8 ≤ (nativeHistoryStrong0224End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix8,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix7_length]
  have hs : nativeHistoryStrong0224Start.2 = nativeHistoryStrong0192End.2 := by decide +kernel
  have hb := nativeHistoryStrong0224Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix7_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix9 : List ℚ := nativeHistoryStrongCompletePrefix8 ++ nativeHistoryStrong0256Inputs

theorem nativeHistoryStrongCompletePrefix9_length : nativeHistoryStrongCompletePrefix9.length = 288 := by
  rw [nativeHistoryStrongCompletePrefix9,List.length_append,nativeHistoryStrongCompletePrefix8_length,nativeHistoryStrong0256Inputs_length]

theorem nativeHistoryStrongCompletePrefix9_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix9 ≤ (nativeHistoryStrong0256End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix9,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix8_length]
  have hs : nativeHistoryStrong0256Start.2 = nativeHistoryStrong0224End.2 := by decide +kernel
  have hb := nativeHistoryStrong0256Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix8_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix10 : List ℚ := nativeHistoryStrongCompletePrefix9 ++ nativeHistoryStrong0288Inputs

theorem nativeHistoryStrongCompletePrefix10_length : nativeHistoryStrongCompletePrefix10.length = 320 := by
  rw [nativeHistoryStrongCompletePrefix10,List.length_append,nativeHistoryStrongCompletePrefix9_length,nativeHistoryStrong0288Inputs_length]

theorem nativeHistoryStrongCompletePrefix10_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix10 ≤ (nativeHistoryStrong0288End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix10,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix9_length]
  have hs : nativeHistoryStrong0288Start.2 = nativeHistoryStrong0256End.2 := by decide +kernel
  have hb := nativeHistoryStrong0288Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix9_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix11 : List ℚ := nativeHistoryStrongCompletePrefix10 ++ nativeHistoryStrong0320Inputs

theorem nativeHistoryStrongCompletePrefix11_length : nativeHistoryStrongCompletePrefix11.length = 352 := by
  rw [nativeHistoryStrongCompletePrefix11,List.length_append,nativeHistoryStrongCompletePrefix10_length,nativeHistoryStrong0320Inputs_length]

theorem nativeHistoryStrongCompletePrefix11_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix11 ≤ (nativeHistoryStrong0320End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix11,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix10_length]
  have hs : nativeHistoryStrong0320Start.2 = nativeHistoryStrong0288End.2 := by decide +kernel
  have hb := nativeHistoryStrong0320Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix10_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix12 : List ℚ := nativeHistoryStrongCompletePrefix11 ++ nativeHistoryStrong0352Inputs

theorem nativeHistoryStrongCompletePrefix12_length : nativeHistoryStrongCompletePrefix12.length = 384 := by
  rw [nativeHistoryStrongCompletePrefix12,List.length_append,nativeHistoryStrongCompletePrefix11_length,nativeHistoryStrong0352Inputs_length]

theorem nativeHistoryStrongCompletePrefix12_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix12 ≤ (nativeHistoryStrong0352End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix12,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix11_length]
  have hs : nativeHistoryStrong0352Start.2 = nativeHistoryStrong0320End.2 := by decide +kernel
  have hb := nativeHistoryStrong0352Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix11_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix13 : List ℚ := nativeHistoryStrongCompletePrefix12 ++ nativeHistoryStrong0384Inputs

theorem nativeHistoryStrongCompletePrefix13_length : nativeHistoryStrongCompletePrefix13.length = 416 := by
  rw [nativeHistoryStrongCompletePrefix13,List.length_append,nativeHistoryStrongCompletePrefix12_length,nativeHistoryStrong0384Inputs_length]

theorem nativeHistoryStrongCompletePrefix13_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix13 ≤ (nativeHistoryStrong0384End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix13,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix12_length]
  have hs : nativeHistoryStrong0384Start.2 = nativeHistoryStrong0352End.2 := by decide +kernel
  have hb := nativeHistoryStrong0384Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix12_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix14 : List ℚ := nativeHistoryStrongCompletePrefix13 ++ nativeHistoryStrong0416Inputs

theorem nativeHistoryStrongCompletePrefix14_length : nativeHistoryStrongCompletePrefix14.length = 448 := by
  rw [nativeHistoryStrongCompletePrefix14,List.length_append,nativeHistoryStrongCompletePrefix13_length,nativeHistoryStrong0416Inputs_length]

theorem nativeHistoryStrongCompletePrefix14_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix14 ≤ (nativeHistoryStrong0416End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix14,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix13_length]
  have hs : nativeHistoryStrong0416Start.2 = nativeHistoryStrong0384End.2 := by decide +kernel
  have hb := nativeHistoryStrong0416Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix13_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix15 : List ℚ := nativeHistoryStrongCompletePrefix14 ++ nativeHistoryStrong0448Inputs

theorem nativeHistoryStrongCompletePrefix15_length : nativeHistoryStrongCompletePrefix15.length = 480 := by
  rw [nativeHistoryStrongCompletePrefix15,List.length_append,nativeHistoryStrongCompletePrefix14_length,nativeHistoryStrong0448Inputs_length]

theorem nativeHistoryStrongCompletePrefix15_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix15 ≤ (nativeHistoryStrong0448End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix15,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix14_length]
  have hs : nativeHistoryStrong0448Start.2 = nativeHistoryStrong0416End.2 := by decide +kernel
  have hb := nativeHistoryStrong0448Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix14_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix16 : List ℚ := nativeHistoryStrongCompletePrefix15 ++ nativeHistoryStrong0480Inputs

theorem nativeHistoryStrongCompletePrefix16_length : nativeHistoryStrongCompletePrefix16.length = 512 := by
  rw [nativeHistoryStrongCompletePrefix16,List.length_append,nativeHistoryStrongCompletePrefix15_length,nativeHistoryStrong0480Inputs_length]

theorem nativeHistoryStrongCompletePrefix16_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix16 ≤ (nativeHistoryStrong0480End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix16,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix15_length]
  have hs : nativeHistoryStrong0480Start.2 = nativeHistoryStrong0448End.2 := by decide +kernel
  have hb := nativeHistoryStrong0480Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix15_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix17 : List ℚ := nativeHistoryStrongCompletePrefix16 ++ nativeHistoryStrong0512Inputs

theorem nativeHistoryStrongCompletePrefix17_length : nativeHistoryStrongCompletePrefix17.length = 544 := by
  rw [nativeHistoryStrongCompletePrefix17,List.length_append,nativeHistoryStrongCompletePrefix16_length,nativeHistoryStrong0512Inputs_length]

theorem nativeHistoryStrongCompletePrefix17_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix17 ≤ (nativeHistoryStrong0512End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix17,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix16_length]
  have hs : nativeHistoryStrong0512Start.2 = nativeHistoryStrong0480End.2 := by decide +kernel
  have hb := nativeHistoryStrong0512Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix16_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix18 : List ℚ := nativeHistoryStrongCompletePrefix17 ++ nativeHistoryStrong0544Inputs

theorem nativeHistoryStrongCompletePrefix18_length : nativeHistoryStrongCompletePrefix18.length = 576 := by
  rw [nativeHistoryStrongCompletePrefix18,List.length_append,nativeHistoryStrongCompletePrefix17_length,nativeHistoryStrong0544Inputs_length]

theorem nativeHistoryStrongCompletePrefix18_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix18 ≤ (nativeHistoryStrong0544End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix18,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix17_length]
  have hs : nativeHistoryStrong0544Start.2 = nativeHistoryStrong0512End.2 := by decide +kernel
  have hb := nativeHistoryStrong0544Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix17_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix19 : List ℚ := nativeHistoryStrongCompletePrefix18 ++ nativeHistoryStrong0576Inputs

theorem nativeHistoryStrongCompletePrefix19_length : nativeHistoryStrongCompletePrefix19.length = 608 := by
  rw [nativeHistoryStrongCompletePrefix19,List.length_append,nativeHistoryStrongCompletePrefix18_length,nativeHistoryStrong0576Inputs_length]

theorem nativeHistoryStrongCompletePrefix19_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix19 ≤ (nativeHistoryStrong0576End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix19,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix18_length]
  have hs : nativeHistoryStrong0576Start.2 = nativeHistoryStrong0544End.2 := by decide +kernel
  have hb := nativeHistoryStrong0576Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix18_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix20 : List ℚ := nativeHistoryStrongCompletePrefix19 ++ nativeHistoryStrong0608Inputs

theorem nativeHistoryStrongCompletePrefix20_length : nativeHistoryStrongCompletePrefix20.length = 640 := by
  rw [nativeHistoryStrongCompletePrefix20,List.length_append,nativeHistoryStrongCompletePrefix19_length,nativeHistoryStrong0608Inputs_length]

theorem nativeHistoryStrongCompletePrefix20_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix20 ≤ (nativeHistoryStrong0608End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix20,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix19_length]
  have hs : nativeHistoryStrong0608Start.2 = nativeHistoryStrong0576End.2 := by decide +kernel
  have hb := nativeHistoryStrong0608Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix19_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix21 : List ℚ := nativeHistoryStrongCompletePrefix20 ++ nativeHistoryStrong0640Inputs

theorem nativeHistoryStrongCompletePrefix21_length : nativeHistoryStrongCompletePrefix21.length = 672 := by
  rw [nativeHistoryStrongCompletePrefix21,List.length_append,nativeHistoryStrongCompletePrefix20_length,nativeHistoryStrong0640Inputs_length]

theorem nativeHistoryStrongCompletePrefix21_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix21 ≤ (nativeHistoryStrong0640End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix21,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix20_length]
  have hs : nativeHistoryStrong0640Start.2 = nativeHistoryStrong0608End.2 := by decide +kernel
  have hb := nativeHistoryStrong0640Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix20_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix22 : List ℚ := nativeHistoryStrongCompletePrefix21 ++ nativeHistoryStrong0672Inputs

theorem nativeHistoryStrongCompletePrefix22_length : nativeHistoryStrongCompletePrefix22.length = 704 := by
  rw [nativeHistoryStrongCompletePrefix22,List.length_append,nativeHistoryStrongCompletePrefix21_length,nativeHistoryStrong0672Inputs_length]

theorem nativeHistoryStrongCompletePrefix22_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix22 ≤ (nativeHistoryStrong0672End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix22,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix21_length]
  have hs : nativeHistoryStrong0672Start.2 = nativeHistoryStrong0640End.2 := by decide +kernel
  have hb := nativeHistoryStrong0672Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix21_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix23 : List ℚ := nativeHistoryStrongCompletePrefix22 ++ nativeHistoryStrong0704Inputs

theorem nativeHistoryStrongCompletePrefix23_length : nativeHistoryStrongCompletePrefix23.length = 736 := by
  rw [nativeHistoryStrongCompletePrefix23,List.length_append,nativeHistoryStrongCompletePrefix22_length,nativeHistoryStrong0704Inputs_length]

theorem nativeHistoryStrongCompletePrefix23_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix23 ≤ (nativeHistoryStrong0704End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix23,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix22_length]
  have hs : nativeHistoryStrong0704Start.2 = nativeHistoryStrong0672End.2 := by decide +kernel
  have hb := nativeHistoryStrong0704Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix22_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix24 : List ℚ := nativeHistoryStrongCompletePrefix23 ++ nativeHistoryStrong0736Inputs

theorem nativeHistoryStrongCompletePrefix24_length : nativeHistoryStrongCompletePrefix24.length = 768 := by
  rw [nativeHistoryStrongCompletePrefix24,List.length_append,nativeHistoryStrongCompletePrefix23_length,nativeHistoryStrong0736Inputs_length]

theorem nativeHistoryStrongCompletePrefix24_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix24 ≤ (nativeHistoryStrong0736End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix24,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix23_length]
  have hs : nativeHistoryStrong0736Start.2 = nativeHistoryStrong0704End.2 := by decide +kernel
  have hb := nativeHistoryStrong0736Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix23_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix25 : List ℚ := nativeHistoryStrongCompletePrefix24 ++ nativeHistoryStrong0768Inputs

theorem nativeHistoryStrongCompletePrefix25_length : nativeHistoryStrongCompletePrefix25.length = 800 := by
  rw [nativeHistoryStrongCompletePrefix25,List.length_append,nativeHistoryStrongCompletePrefix24_length,nativeHistoryStrong0768Inputs_length]

theorem nativeHistoryStrongCompletePrefix25_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix25 ≤ (nativeHistoryStrong0768End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix25,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix24_length]
  have hs : nativeHistoryStrong0768Start.2 = nativeHistoryStrong0736End.2 := by decide +kernel
  have hb := nativeHistoryStrong0768Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix24_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix26 : List ℚ := nativeHistoryStrongCompletePrefix25 ++ nativeHistoryStrong0800Inputs

theorem nativeHistoryStrongCompletePrefix26_length : nativeHistoryStrongCompletePrefix26.length = 832 := by
  rw [nativeHistoryStrongCompletePrefix26,List.length_append,nativeHistoryStrongCompletePrefix25_length,nativeHistoryStrong0800Inputs_length]

theorem nativeHistoryStrongCompletePrefix26_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix26 ≤ (nativeHistoryStrong0800End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix26,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix25_length]
  have hs : nativeHistoryStrong0800Start.2 = nativeHistoryStrong0768End.2 := by decide +kernel
  have hb := nativeHistoryStrong0800Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix25_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix27 : List ℚ := nativeHistoryStrongCompletePrefix26 ++ nativeHistoryStrong0832Inputs

theorem nativeHistoryStrongCompletePrefix27_length : nativeHistoryStrongCompletePrefix27.length = 864 := by
  rw [nativeHistoryStrongCompletePrefix27,List.length_append,nativeHistoryStrongCompletePrefix26_length,nativeHistoryStrong0832Inputs_length]

theorem nativeHistoryStrongCompletePrefix27_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix27 ≤ (nativeHistoryStrong0832End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix27,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix26_length]
  have hs : nativeHistoryStrong0832Start.2 = nativeHistoryStrong0800End.2 := by decide +kernel
  have hb := nativeHistoryStrong0832Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix26_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix28 : List ℚ := nativeHistoryStrongCompletePrefix27 ++ nativeHistoryStrong0864Inputs

theorem nativeHistoryStrongCompletePrefix28_length : nativeHistoryStrongCompletePrefix28.length = 896 := by
  rw [nativeHistoryStrongCompletePrefix28,List.length_append,nativeHistoryStrongCompletePrefix27_length,nativeHistoryStrong0864Inputs_length]

theorem nativeHistoryStrongCompletePrefix28_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix28 ≤ (nativeHistoryStrong0864End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix28,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix27_length]
  have hs : nativeHistoryStrong0864Start.2 = nativeHistoryStrong0832End.2 := by decide +kernel
  have hb := nativeHistoryStrong0864Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix27_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix29 : List ℚ := nativeHistoryStrongCompletePrefix28 ++ nativeHistoryStrong0896Inputs

theorem nativeHistoryStrongCompletePrefix29_length : nativeHistoryStrongCompletePrefix29.length = 928 := by
  rw [nativeHistoryStrongCompletePrefix29,List.length_append,nativeHistoryStrongCompletePrefix28_length,nativeHistoryStrong0896Inputs_length]

theorem nativeHistoryStrongCompletePrefix29_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix29 ≤ (nativeHistoryStrong0896End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix29,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix28_length]
  have hs : nativeHistoryStrong0896Start.2 = nativeHistoryStrong0864End.2 := by decide +kernel
  have hb := nativeHistoryStrong0896Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix28_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix30 : List ℚ := nativeHistoryStrongCompletePrefix29 ++ nativeHistoryStrong0928Inputs

theorem nativeHistoryStrongCompletePrefix30_length : nativeHistoryStrongCompletePrefix30.length = 960 := by
  rw [nativeHistoryStrongCompletePrefix30,List.length_append,nativeHistoryStrongCompletePrefix29_length,nativeHistoryStrong0928Inputs_length]

theorem nativeHistoryStrongCompletePrefix30_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix30 ≤ (nativeHistoryStrong0928End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix30,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix29_length]
  have hs : nativeHistoryStrong0928Start.2 = nativeHistoryStrong0896End.2 := by decide +kernel
  have hb := nativeHistoryStrong0928Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix29_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix31 : List ℚ := nativeHistoryStrongCompletePrefix30 ++ nativeHistoryStrong0960Inputs

theorem nativeHistoryStrongCompletePrefix31_length : nativeHistoryStrongCompletePrefix31.length = 992 := by
  rw [nativeHistoryStrongCompletePrefix31,List.length_append,nativeHistoryStrongCompletePrefix30_length,nativeHistoryStrong0960Inputs_length]

theorem nativeHistoryStrongCompletePrefix31_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix31 ≤ (nativeHistoryStrong0960End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix31,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix30_length]
  have hs : nativeHistoryStrong0960Start.2 = nativeHistoryStrong0928End.2 := by decide +kernel
  have hb := nativeHistoryStrong0960Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix30_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix32 : List ℚ := nativeHistoryStrongCompletePrefix31 ++ nativeHistoryStrong0992Inputs

theorem nativeHistoryStrongCompletePrefix32_length : nativeHistoryStrongCompletePrefix32.length = 1024 := by
  rw [nativeHistoryStrongCompletePrefix32,List.length_append,nativeHistoryStrongCompletePrefix31_length,nativeHistoryStrong0992Inputs_length]

theorem nativeHistoryStrongCompletePrefix32_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix32 ≤ (nativeHistoryStrong0992End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix32,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix31_length]
  have hs : nativeHistoryStrong0992Start.2 = nativeHistoryStrong0960End.2 := by decide +kernel
  have hb := nativeHistoryStrong0992Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix31_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix33 : List ℚ := nativeHistoryStrongCompletePrefix32 ++ nativeHistoryStrong1024Inputs

theorem nativeHistoryStrongCompletePrefix33_length : nativeHistoryStrongCompletePrefix33.length = 1056 := by
  rw [nativeHistoryStrongCompletePrefix33,List.length_append,nativeHistoryStrongCompletePrefix32_length,nativeHistoryStrong1024Inputs_length]

theorem nativeHistoryStrongCompletePrefix33_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix33 ≤ (nativeHistoryStrong1024End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix33,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix32_length]
  have hs : nativeHistoryStrong1024Start.2 = nativeHistoryStrong0992End.2 := by decide +kernel
  have hb := nativeHistoryStrong1024Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix32_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix34 : List ℚ := nativeHistoryStrongCompletePrefix33 ++ nativeHistoryStrong1056Inputs

theorem nativeHistoryStrongCompletePrefix34_length : nativeHistoryStrongCompletePrefix34.length = 1088 := by
  rw [nativeHistoryStrongCompletePrefix34,List.length_append,nativeHistoryStrongCompletePrefix33_length,nativeHistoryStrong1056Inputs_length]

theorem nativeHistoryStrongCompletePrefix34_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix34 ≤ (nativeHistoryStrong1056End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix34,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix33_length]
  have hs : nativeHistoryStrong1056Start.2 = nativeHistoryStrong1024End.2 := by decide +kernel
  have hb := nativeHistoryStrong1056Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix33_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix35 : List ℚ := nativeHistoryStrongCompletePrefix34 ++ nativeHistoryStrong1088Inputs

theorem nativeHistoryStrongCompletePrefix35_length : nativeHistoryStrongCompletePrefix35.length = 1120 := by
  rw [nativeHistoryStrongCompletePrefix35,List.length_append,nativeHistoryStrongCompletePrefix34_length,nativeHistoryStrong1088Inputs_length]

theorem nativeHistoryStrongCompletePrefix35_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix35 ≤ (nativeHistoryStrong1088End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix35,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix34_length]
  have hs : nativeHistoryStrong1088Start.2 = nativeHistoryStrong1056End.2 := by decide +kernel
  have hb := nativeHistoryStrong1088Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix34_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix36 : List ℚ := nativeHistoryStrongCompletePrefix35 ++ nativeHistoryStrong1120Inputs

theorem nativeHistoryStrongCompletePrefix36_length : nativeHistoryStrongCompletePrefix36.length = 1152 := by
  rw [nativeHistoryStrongCompletePrefix36,List.length_append,nativeHistoryStrongCompletePrefix35_length,nativeHistoryStrong1120Inputs_length]

theorem nativeHistoryStrongCompletePrefix36_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix36 ≤ (nativeHistoryStrong1120End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix36,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix35_length]
  have hs : nativeHistoryStrong1120Start.2 = nativeHistoryStrong1088End.2 := by decide +kernel
  have hb := nativeHistoryStrong1120Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix35_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix37 : List ℚ := nativeHistoryStrongCompletePrefix36 ++ nativeHistoryStrong1152Inputs

theorem nativeHistoryStrongCompletePrefix37_length : nativeHistoryStrongCompletePrefix37.length = 1184 := by
  rw [nativeHistoryStrongCompletePrefix37,List.length_append,nativeHistoryStrongCompletePrefix36_length,nativeHistoryStrong1152Inputs_length]

theorem nativeHistoryStrongCompletePrefix37_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix37 ≤ (nativeHistoryStrong1152End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix37,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix36_length]
  have hs : nativeHistoryStrong1152Start.2 = nativeHistoryStrong1120End.2 := by decide +kernel
  have hb := nativeHistoryStrong1152Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix36_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix38 : List ℚ := nativeHistoryStrongCompletePrefix37 ++ nativeHistoryStrong1184Inputs

theorem nativeHistoryStrongCompletePrefix38_length : nativeHistoryStrongCompletePrefix38.length = 1216 := by
  rw [nativeHistoryStrongCompletePrefix38,List.length_append,nativeHistoryStrongCompletePrefix37_length,nativeHistoryStrong1184Inputs_length]

theorem nativeHistoryStrongCompletePrefix38_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix38 ≤ (nativeHistoryStrong1184End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix38,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix37_length]
  have hs : nativeHistoryStrong1184Start.2 = nativeHistoryStrong1152End.2 := by decide +kernel
  have hb := nativeHistoryStrong1184Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix37_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix39 : List ℚ := nativeHistoryStrongCompletePrefix38 ++ nativeHistoryStrong1216Inputs

theorem nativeHistoryStrongCompletePrefix39_length : nativeHistoryStrongCompletePrefix39.length = 1248 := by
  rw [nativeHistoryStrongCompletePrefix39,List.length_append,nativeHistoryStrongCompletePrefix38_length,nativeHistoryStrong1216Inputs_length]

theorem nativeHistoryStrongCompletePrefix39_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix39 ≤ (nativeHistoryStrong1216End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix39,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix38_length]
  have hs : nativeHistoryStrong1216Start.2 = nativeHistoryStrong1184End.2 := by decide +kernel
  have hb := nativeHistoryStrong1216Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix38_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix40 : List ℚ := nativeHistoryStrongCompletePrefix39 ++ nativeHistoryStrong1248Inputs

theorem nativeHistoryStrongCompletePrefix40_length : nativeHistoryStrongCompletePrefix40.length = 1280 := by
  rw [nativeHistoryStrongCompletePrefix40,List.length_append,nativeHistoryStrongCompletePrefix39_length,nativeHistoryStrong1248Inputs_length]

theorem nativeHistoryStrongCompletePrefix40_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix40 ≤ (nativeHistoryStrong1248End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix40,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix39_length]
  have hs : nativeHistoryStrong1248Start.2 = nativeHistoryStrong1216End.2 := by decide +kernel
  have hb := nativeHistoryStrong1248Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix39_real hb
  apply h.trans_eq
  ring

def nativeHistoryStrongCompletePrefix41 : List ℚ := nativeHistoryStrongCompletePrefix40 ++ nativeHistoryStrong1280Inputs

theorem nativeHistoryStrongCompletePrefix41_length : nativeHistoryStrongCompletePrefix41.length = 1286 := by
  rw [nativeHistoryStrongCompletePrefix41,List.length_append,nativeHistoryStrongCompletePrefix40_length,nativeHistoryStrong1280Inputs_length]

theorem nativeHistoryStrongCompletePrefix41_real : nativeHistoryReal 9 0 nativeHistoryStrongCompletePrefix41 ≤ (nativeHistoryStrong1280End.2 : ℝ)-(nativeHistoryStrong0000Start.2 : ℝ) := by
  rw [nativeHistoryStrongCompletePrefix41,nativeHistoryReal_append,nativeHistoryStrongCompletePrefix40_length]
  have hs : nativeHistoryStrong1280Start.2 = nativeHistoryStrong1248End.2 := by decide +kernel
  have hb := nativeHistoryStrong1280Real_bound
  rw [hs] at hb
  have h := add_le_add nativeHistoryStrongCompletePrefix40_real hb
  apply h.trans_eq
  ring

end ASDExplicitGamma.Numerics.Native
