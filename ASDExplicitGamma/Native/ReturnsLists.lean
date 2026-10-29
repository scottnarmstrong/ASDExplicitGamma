module

public import ASDExplicitGamma.Native.ReturnsHeatTable

/-! NA-RETURNS: the entries of the two certified history lists are the heat returns (depths
`9 ≤ g ≤ 160`) and the rational OLD raw envelopes (`g > 160`). Checked block by block. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The certified input of the history at total gap `g`: the heat return up to `160`, the OLD raw
envelope afterwards. -/
def nativeReturnsEntry (g : ℕ) : ℚ :=
  if g ≤ 160 then (nativeReturnsHeatTable.getD (g - 9) (0, 0)).1
  else nativeAvg * nativeA + (nativeRaw g).2.2

theorem nativeReturns_entries_append (e : ℕ → ℚ) (xs ys : List ℚ) (n m : ℕ)
    (hx : xs.length = n) (Px : ∀ i < n, xs.getD i 0 = e i)
    (Py : ∀ i < m, ys.getD i 0 = e (n + i)) :
    ∀ i < n + m, (xs ++ ys).getD i 0 = e i := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by rw [hx]; exact h)]
    exact Px i h
  · have h := not_lt.mp h
    rw [List.getD_append_right _ _ _ _ (by rw [hx]; exact h), hx]
    have := Py (i - n) (by omega)
    rwa [show n + (i - n) = i by omega] at this

theorem nativeReturns_strong_block_0000 : ∀ i : Fin 32,
    nativeHistoryStrong0000Inputs.getD i.val 0 = nativeReturnsEntry (9 + (0 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_1 : ∀ i < 32,
    nativeHistoryStrongCompletePrefix1.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 0 32
    (nativeHistoryStrongCompletePrefix0_length)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => nativeReturns_strong_block_0000 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix1]
  exact h

theorem nativeReturns_strong_block_0032 : ∀ i : Fin 32,
    nativeHistoryStrong0032Inputs.getD i.val 0 = nativeReturnsEntry (9 + (32 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_2 : ∀ i < 64,
    nativeHistoryStrongCompletePrefix2.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 32 32
    (nativeHistoryStrongCompletePrefix1_length)
    nativeReturns_strong_prefix_1
    (fun i hi => nativeReturns_strong_block_0032 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix2]
  exact h

theorem nativeReturns_strong_block_0064 : ∀ i : Fin 32,
    nativeHistoryStrong0064Inputs.getD i.val 0 = nativeReturnsEntry (9 + (64 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_3 : ∀ i < 96,
    nativeHistoryStrongCompletePrefix3.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 64 32
    (nativeHistoryStrongCompletePrefix2_length)
    nativeReturns_strong_prefix_2
    (fun i hi => nativeReturns_strong_block_0064 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix3]
  exact h

theorem nativeReturns_strong_block_0096 : ∀ i : Fin 32,
    nativeHistoryStrong0096Inputs.getD i.val 0 = nativeReturnsEntry (9 + (96 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_4 : ∀ i < 128,
    nativeHistoryStrongCompletePrefix4.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 96 32
    (nativeHistoryStrongCompletePrefix3_length)
    nativeReturns_strong_prefix_3
    (fun i hi => nativeReturns_strong_block_0096 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix4]
  exact h

theorem nativeReturns_strong_block_0128 : ∀ i : Fin 32,
    nativeHistoryStrong0128Inputs.getD i.val 0 = nativeReturnsEntry (9 + (128 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_5 : ∀ i < 160,
    nativeHistoryStrongCompletePrefix5.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 128 32
    (nativeHistoryStrongCompletePrefix4_length)
    nativeReturns_strong_prefix_4
    (fun i hi => nativeReturns_strong_block_0128 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix5]
  exact h

theorem nativeReturns_strong_block_0160 : ∀ i : Fin 32,
    nativeHistoryStrong0160Inputs.getD i.val 0 = nativeReturnsEntry (9 + (160 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_6 : ∀ i < 192,
    nativeHistoryStrongCompletePrefix6.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 160 32
    (nativeHistoryStrongCompletePrefix5_length)
    nativeReturns_strong_prefix_5
    (fun i hi => nativeReturns_strong_block_0160 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix6]
  exact h

theorem nativeReturns_strong_block_0192 : ∀ i : Fin 32,
    nativeHistoryStrong0192Inputs.getD i.val 0 = nativeReturnsEntry (9 + (192 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_7 : ∀ i < 224,
    nativeHistoryStrongCompletePrefix7.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 192 32
    (nativeHistoryStrongCompletePrefix6_length)
    nativeReturns_strong_prefix_6
    (fun i hi => nativeReturns_strong_block_0192 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix7]
  exact h

theorem nativeReturns_strong_block_0224 : ∀ i : Fin 32,
    nativeHistoryStrong0224Inputs.getD i.val 0 = nativeReturnsEntry (9 + (224 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_8 : ∀ i < 256,
    nativeHistoryStrongCompletePrefix8.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 224 32
    (nativeHistoryStrongCompletePrefix7_length)
    nativeReturns_strong_prefix_7
    (fun i hi => nativeReturns_strong_block_0224 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix8]
  exact h

theorem nativeReturns_strong_block_0256 : ∀ i : Fin 32,
    nativeHistoryStrong0256Inputs.getD i.val 0 = nativeReturnsEntry (9 + (256 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_9 : ∀ i < 288,
    nativeHistoryStrongCompletePrefix9.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 256 32
    (nativeHistoryStrongCompletePrefix8_length)
    nativeReturns_strong_prefix_8
    (fun i hi => nativeReturns_strong_block_0256 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix9]
  exact h

theorem nativeReturns_strong_block_0288 : ∀ i : Fin 32,
    nativeHistoryStrong0288Inputs.getD i.val 0 = nativeReturnsEntry (9 + (288 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_10 : ∀ i < 320,
    nativeHistoryStrongCompletePrefix10.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 288 32
    (nativeHistoryStrongCompletePrefix9_length)
    nativeReturns_strong_prefix_9
    (fun i hi => nativeReturns_strong_block_0288 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix10]
  exact h

theorem nativeReturns_strong_block_0320 : ∀ i : Fin 32,
    nativeHistoryStrong0320Inputs.getD i.val 0 = nativeReturnsEntry (9 + (320 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_11 : ∀ i < 352,
    nativeHistoryStrongCompletePrefix11.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 320 32
    (nativeHistoryStrongCompletePrefix10_length)
    nativeReturns_strong_prefix_10
    (fun i hi => nativeReturns_strong_block_0320 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix11]
  exact h

theorem nativeReturns_strong_block_0352 : ∀ i : Fin 32,
    nativeHistoryStrong0352Inputs.getD i.val 0 = nativeReturnsEntry (9 + (352 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_12 : ∀ i < 384,
    nativeHistoryStrongCompletePrefix12.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 352 32
    (nativeHistoryStrongCompletePrefix11_length)
    nativeReturns_strong_prefix_11
    (fun i hi => nativeReturns_strong_block_0352 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix12]
  exact h

theorem nativeReturns_strong_block_0384 : ∀ i : Fin 32,
    nativeHistoryStrong0384Inputs.getD i.val 0 = nativeReturnsEntry (9 + (384 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_13 : ∀ i < 416,
    nativeHistoryStrongCompletePrefix13.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 384 32
    (nativeHistoryStrongCompletePrefix12_length)
    nativeReturns_strong_prefix_12
    (fun i hi => nativeReturns_strong_block_0384 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix13]
  exact h

theorem nativeReturns_strong_block_0416 : ∀ i : Fin 32,
    nativeHistoryStrong0416Inputs.getD i.val 0 = nativeReturnsEntry (9 + (416 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_14 : ∀ i < 448,
    nativeHistoryStrongCompletePrefix14.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 416 32
    (nativeHistoryStrongCompletePrefix13_length)
    nativeReturns_strong_prefix_13
    (fun i hi => nativeReturns_strong_block_0416 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix14]
  exact h

theorem nativeReturns_strong_block_0448 : ∀ i : Fin 32,
    nativeHistoryStrong0448Inputs.getD i.val 0 = nativeReturnsEntry (9 + (448 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_15 : ∀ i < 480,
    nativeHistoryStrongCompletePrefix15.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 448 32
    (nativeHistoryStrongCompletePrefix14_length)
    nativeReturns_strong_prefix_14
    (fun i hi => nativeReturns_strong_block_0448 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix15]
  exact h

theorem nativeReturns_strong_block_0480 : ∀ i : Fin 32,
    nativeHistoryStrong0480Inputs.getD i.val 0 = nativeReturnsEntry (9 + (480 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_16 : ∀ i < 512,
    nativeHistoryStrongCompletePrefix16.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 480 32
    (nativeHistoryStrongCompletePrefix15_length)
    nativeReturns_strong_prefix_15
    (fun i hi => nativeReturns_strong_block_0480 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix16]
  exact h

theorem nativeReturns_strong_block_0512 : ∀ i : Fin 32,
    nativeHistoryStrong0512Inputs.getD i.val 0 = nativeReturnsEntry (9 + (512 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_17 : ∀ i < 544,
    nativeHistoryStrongCompletePrefix17.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 512 32
    (nativeHistoryStrongCompletePrefix16_length)
    nativeReturns_strong_prefix_16
    (fun i hi => nativeReturns_strong_block_0512 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix17]
  exact h

theorem nativeReturns_strong_block_0544 : ∀ i : Fin 32,
    nativeHistoryStrong0544Inputs.getD i.val 0 = nativeReturnsEntry (9 + (544 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_18 : ∀ i < 576,
    nativeHistoryStrongCompletePrefix18.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 544 32
    (nativeHistoryStrongCompletePrefix17_length)
    nativeReturns_strong_prefix_17
    (fun i hi => nativeReturns_strong_block_0544 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix18]
  exact h

theorem nativeReturns_strong_block_0576 : ∀ i : Fin 32,
    nativeHistoryStrong0576Inputs.getD i.val 0 = nativeReturnsEntry (9 + (576 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_19 : ∀ i < 608,
    nativeHistoryStrongCompletePrefix19.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 576 32
    (nativeHistoryStrongCompletePrefix18_length)
    nativeReturns_strong_prefix_18
    (fun i hi => nativeReturns_strong_block_0576 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix19]
  exact h

theorem nativeReturns_strong_block_0608 : ∀ i : Fin 32,
    nativeHistoryStrong0608Inputs.getD i.val 0 = nativeReturnsEntry (9 + (608 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_20 : ∀ i < 640,
    nativeHistoryStrongCompletePrefix20.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 608 32
    (nativeHistoryStrongCompletePrefix19_length)
    nativeReturns_strong_prefix_19
    (fun i hi => nativeReturns_strong_block_0608 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix20]
  exact h

theorem nativeReturns_strong_block_0640 : ∀ i : Fin 32,
    nativeHistoryStrong0640Inputs.getD i.val 0 = nativeReturnsEntry (9 + (640 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_21 : ∀ i < 672,
    nativeHistoryStrongCompletePrefix21.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 640 32
    (nativeHistoryStrongCompletePrefix20_length)
    nativeReturns_strong_prefix_20
    (fun i hi => nativeReturns_strong_block_0640 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix21]
  exact h

theorem nativeReturns_strong_block_0672 : ∀ i : Fin 32,
    nativeHistoryStrong0672Inputs.getD i.val 0 = nativeReturnsEntry (9 + (672 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_22 : ∀ i < 704,
    nativeHistoryStrongCompletePrefix22.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 672 32
    (nativeHistoryStrongCompletePrefix21_length)
    nativeReturns_strong_prefix_21
    (fun i hi => nativeReturns_strong_block_0672 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix22]
  exact h

theorem nativeReturns_strong_block_0704 : ∀ i : Fin 32,
    nativeHistoryStrong0704Inputs.getD i.val 0 = nativeReturnsEntry (9 + (704 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_23 : ∀ i < 736,
    nativeHistoryStrongCompletePrefix23.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 704 32
    (nativeHistoryStrongCompletePrefix22_length)
    nativeReturns_strong_prefix_22
    (fun i hi => nativeReturns_strong_block_0704 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix23]
  exact h

theorem nativeReturns_strong_block_0736 : ∀ i : Fin 32,
    nativeHistoryStrong0736Inputs.getD i.val 0 = nativeReturnsEntry (9 + (736 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_24 : ∀ i < 768,
    nativeHistoryStrongCompletePrefix24.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 736 32
    (nativeHistoryStrongCompletePrefix23_length)
    nativeReturns_strong_prefix_23
    (fun i hi => nativeReturns_strong_block_0736 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix24]
  exact h

theorem nativeReturns_strong_block_0768 : ∀ i : Fin 32,
    nativeHistoryStrong0768Inputs.getD i.val 0 = nativeReturnsEntry (9 + (768 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_25 : ∀ i < 800,
    nativeHistoryStrongCompletePrefix25.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 768 32
    (nativeHistoryStrongCompletePrefix24_length)
    nativeReturns_strong_prefix_24
    (fun i hi => nativeReturns_strong_block_0768 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix25]
  exact h

theorem nativeReturns_strong_block_0800 : ∀ i : Fin 32,
    nativeHistoryStrong0800Inputs.getD i.val 0 = nativeReturnsEntry (9 + (800 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_26 : ∀ i < 832,
    nativeHistoryStrongCompletePrefix26.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 800 32
    (nativeHistoryStrongCompletePrefix25_length)
    nativeReturns_strong_prefix_25
    (fun i hi => nativeReturns_strong_block_0800 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix26]
  exact h

theorem nativeReturns_strong_block_0832 : ∀ i : Fin 32,
    nativeHistoryStrong0832Inputs.getD i.val 0 = nativeReturnsEntry (9 + (832 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_27 : ∀ i < 864,
    nativeHistoryStrongCompletePrefix27.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 832 32
    (nativeHistoryStrongCompletePrefix26_length)
    nativeReturns_strong_prefix_26
    (fun i hi => nativeReturns_strong_block_0832 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix27]
  exact h

theorem nativeReturns_strong_block_0864 : ∀ i : Fin 32,
    nativeHistoryStrong0864Inputs.getD i.val 0 = nativeReturnsEntry (9 + (864 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_28 : ∀ i < 896,
    nativeHistoryStrongCompletePrefix28.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 864 32
    (nativeHistoryStrongCompletePrefix27_length)
    nativeReturns_strong_prefix_27
    (fun i hi => nativeReturns_strong_block_0864 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix28]
  exact h

theorem nativeReturns_strong_block_0896 : ∀ i : Fin 32,
    nativeHistoryStrong0896Inputs.getD i.val 0 = nativeReturnsEntry (9 + (896 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_29 : ∀ i < 928,
    nativeHistoryStrongCompletePrefix29.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 896 32
    (nativeHistoryStrongCompletePrefix28_length)
    nativeReturns_strong_prefix_28
    (fun i hi => nativeReturns_strong_block_0896 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix29]
  exact h

theorem nativeReturns_strong_block_0928 : ∀ i : Fin 32,
    nativeHistoryStrong0928Inputs.getD i.val 0 = nativeReturnsEntry (9 + (928 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_30 : ∀ i < 960,
    nativeHistoryStrongCompletePrefix30.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 928 32
    (nativeHistoryStrongCompletePrefix29_length)
    nativeReturns_strong_prefix_29
    (fun i hi => nativeReturns_strong_block_0928 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix30]
  exact h

theorem nativeReturns_strong_block_0960 : ∀ i : Fin 32,
    nativeHistoryStrong0960Inputs.getD i.val 0 = nativeReturnsEntry (9 + (960 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_31 : ∀ i < 992,
    nativeHistoryStrongCompletePrefix31.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 960 32
    (nativeHistoryStrongCompletePrefix30_length)
    nativeReturns_strong_prefix_30
    (fun i hi => nativeReturns_strong_block_0960 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix31]
  exact h

theorem nativeReturns_strong_block_0992 : ∀ i : Fin 32,
    nativeHistoryStrong0992Inputs.getD i.val 0 = nativeReturnsEntry (9 + (992 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_32 : ∀ i < 1024,
    nativeHistoryStrongCompletePrefix32.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 992 32
    (nativeHistoryStrongCompletePrefix31_length)
    nativeReturns_strong_prefix_31
    (fun i hi => nativeReturns_strong_block_0992 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix32]
  exact h

theorem nativeReturns_strong_block_1024 : ∀ i : Fin 32,
    nativeHistoryStrong1024Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1024 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_33 : ∀ i < 1056,
    nativeHistoryStrongCompletePrefix33.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1024 32
    (nativeHistoryStrongCompletePrefix32_length)
    nativeReturns_strong_prefix_32
    (fun i hi => nativeReturns_strong_block_1024 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix33]
  exact h

theorem nativeReturns_strong_block_1056 : ∀ i : Fin 32,
    nativeHistoryStrong1056Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1056 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_34 : ∀ i < 1088,
    nativeHistoryStrongCompletePrefix34.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1056 32
    (nativeHistoryStrongCompletePrefix33_length)
    nativeReturns_strong_prefix_33
    (fun i hi => nativeReturns_strong_block_1056 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix34]
  exact h

theorem nativeReturns_strong_block_1088 : ∀ i : Fin 32,
    nativeHistoryStrong1088Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1088 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_35 : ∀ i < 1120,
    nativeHistoryStrongCompletePrefix35.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1088 32
    (nativeHistoryStrongCompletePrefix34_length)
    nativeReturns_strong_prefix_34
    (fun i hi => nativeReturns_strong_block_1088 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix35]
  exact h

theorem nativeReturns_strong_block_1120 : ∀ i : Fin 32,
    nativeHistoryStrong1120Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1120 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_36 : ∀ i < 1152,
    nativeHistoryStrongCompletePrefix36.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1120 32
    (nativeHistoryStrongCompletePrefix35_length)
    nativeReturns_strong_prefix_35
    (fun i hi => nativeReturns_strong_block_1120 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix36]
  exact h

theorem nativeReturns_strong_block_1152 : ∀ i : Fin 32,
    nativeHistoryStrong1152Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1152 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_37 : ∀ i < 1184,
    nativeHistoryStrongCompletePrefix37.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1152 32
    (nativeHistoryStrongCompletePrefix36_length)
    nativeReturns_strong_prefix_36
    (fun i hi => nativeReturns_strong_block_1152 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix37]
  exact h

theorem nativeReturns_strong_block_1184 : ∀ i : Fin 32,
    nativeHistoryStrong1184Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1184 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_38 : ∀ i < 1216,
    nativeHistoryStrongCompletePrefix38.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1184 32
    (nativeHistoryStrongCompletePrefix37_length)
    nativeReturns_strong_prefix_37
    (fun i hi => nativeReturns_strong_block_1184 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix38]
  exact h

theorem nativeReturns_strong_block_1216 : ∀ i : Fin 32,
    nativeHistoryStrong1216Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1216 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_39 : ∀ i < 1248,
    nativeHistoryStrongCompletePrefix39.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1216 32
    (nativeHistoryStrongCompletePrefix38_length)
    nativeReturns_strong_prefix_38
    (fun i hi => nativeReturns_strong_block_1216 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix39]
  exact h

theorem nativeReturns_strong_block_1248 : ∀ i : Fin 32,
    nativeHistoryStrong1248Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1248 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_40 : ∀ i < 1280,
    nativeHistoryStrongCompletePrefix40.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1248 32
    (nativeHistoryStrongCompletePrefix39_length)
    nativeReturns_strong_prefix_39
    (fun i hi => nativeReturns_strong_block_1248 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix40]
  exact h

theorem nativeReturns_strong_block_1280 : ∀ i : Fin 6,
    nativeHistoryStrong1280Inputs.getD i.val 0 = nativeReturnsEntry (9 + (1280 + i.val)) := by
  decide +kernel

theorem nativeReturns_strong_prefix_41 : ∀ i < 1286,
    nativeHistoryStrongCompletePrefix41.getD i 0 = nativeReturnsEntry (9 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (9 + i)) _ _ 1280 6
    (nativeHistoryStrongCompletePrefix40_length)
    nativeReturns_strong_prefix_40
    (fun i hi => nativeReturns_strong_block_1280 ⟨i, hi⟩)
  rw [nativeHistoryStrongCompletePrefix41]
  exact h

theorem nativeReturns_buffer_block_0000 : ∀ i : Fin 32,
    nativeHistoryBuffer0000Inputs.getD i.val 0 = nativeReturnsEntry (49 + (0 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_1 : ∀ i < 32,
    nativeHistoryBufferCompletePrefix1.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 0 32
    (nativeHistoryBufferCompletePrefix0_length)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => nativeReturns_buffer_block_0000 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix1]
  exact h

theorem nativeReturns_buffer_block_0032 : ∀ i : Fin 32,
    nativeHistoryBuffer0032Inputs.getD i.val 0 = nativeReturnsEntry (49 + (32 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_2 : ∀ i < 64,
    nativeHistoryBufferCompletePrefix2.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 32 32
    (nativeHistoryBufferCompletePrefix1_length)
    nativeReturns_buffer_prefix_1
    (fun i hi => nativeReturns_buffer_block_0032 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix2]
  exact h

theorem nativeReturns_buffer_block_0064 : ∀ i : Fin 32,
    nativeHistoryBuffer0064Inputs.getD i.val 0 = nativeReturnsEntry (49 + (64 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_3 : ∀ i < 96,
    nativeHistoryBufferCompletePrefix3.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 64 32
    (nativeHistoryBufferCompletePrefix2_length)
    nativeReturns_buffer_prefix_2
    (fun i hi => nativeReturns_buffer_block_0064 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix3]
  exact h

theorem nativeReturns_buffer_block_0096 : ∀ i : Fin 32,
    nativeHistoryBuffer0096Inputs.getD i.val 0 = nativeReturnsEntry (49 + (96 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_4 : ∀ i < 128,
    nativeHistoryBufferCompletePrefix4.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 96 32
    (nativeHistoryBufferCompletePrefix3_length)
    nativeReturns_buffer_prefix_3
    (fun i hi => nativeReturns_buffer_block_0096 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix4]
  exact h

theorem nativeReturns_buffer_block_0128 : ∀ i : Fin 32,
    nativeHistoryBuffer0128Inputs.getD i.val 0 = nativeReturnsEntry (49 + (128 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_5 : ∀ i < 160,
    nativeHistoryBufferCompletePrefix5.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 128 32
    (nativeHistoryBufferCompletePrefix4_length)
    nativeReturns_buffer_prefix_4
    (fun i hi => nativeReturns_buffer_block_0128 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix5]
  exact h

theorem nativeReturns_buffer_block_0160 : ∀ i : Fin 32,
    nativeHistoryBuffer0160Inputs.getD i.val 0 = nativeReturnsEntry (49 + (160 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_6 : ∀ i < 192,
    nativeHistoryBufferCompletePrefix6.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 160 32
    (nativeHistoryBufferCompletePrefix5_length)
    nativeReturns_buffer_prefix_5
    (fun i hi => nativeReturns_buffer_block_0160 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix6]
  exact h

theorem nativeReturns_buffer_block_0192 : ∀ i : Fin 32,
    nativeHistoryBuffer0192Inputs.getD i.val 0 = nativeReturnsEntry (49 + (192 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_7 : ∀ i < 224,
    nativeHistoryBufferCompletePrefix7.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 192 32
    (nativeHistoryBufferCompletePrefix6_length)
    nativeReturns_buffer_prefix_6
    (fun i hi => nativeReturns_buffer_block_0192 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix7]
  exact h

theorem nativeReturns_buffer_block_0224 : ∀ i : Fin 32,
    nativeHistoryBuffer0224Inputs.getD i.val 0 = nativeReturnsEntry (49 + (224 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_8 : ∀ i < 256,
    nativeHistoryBufferCompletePrefix8.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 224 32
    (nativeHistoryBufferCompletePrefix7_length)
    nativeReturns_buffer_prefix_7
    (fun i hi => nativeReturns_buffer_block_0224 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix8]
  exact h

theorem nativeReturns_buffer_block_0256 : ∀ i : Fin 32,
    nativeHistoryBuffer0256Inputs.getD i.val 0 = nativeReturnsEntry (49 + (256 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_9 : ∀ i < 288,
    nativeHistoryBufferCompletePrefix9.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 256 32
    (nativeHistoryBufferCompletePrefix8_length)
    nativeReturns_buffer_prefix_8
    (fun i hi => nativeReturns_buffer_block_0256 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix9]
  exact h

theorem nativeReturns_buffer_block_0288 : ∀ i : Fin 32,
    nativeHistoryBuffer0288Inputs.getD i.val 0 = nativeReturnsEntry (49 + (288 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_10 : ∀ i < 320,
    nativeHistoryBufferCompletePrefix10.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 288 32
    (nativeHistoryBufferCompletePrefix9_length)
    nativeReturns_buffer_prefix_9
    (fun i hi => nativeReturns_buffer_block_0288 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix10]
  exact h

theorem nativeReturns_buffer_block_0320 : ∀ i : Fin 32,
    nativeHistoryBuffer0320Inputs.getD i.val 0 = nativeReturnsEntry (49 + (320 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_11 : ∀ i < 352,
    nativeHistoryBufferCompletePrefix11.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 320 32
    (nativeHistoryBufferCompletePrefix10_length)
    nativeReturns_buffer_prefix_10
    (fun i hi => nativeReturns_buffer_block_0320 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix11]
  exact h

theorem nativeReturns_buffer_block_0352 : ∀ i : Fin 32,
    nativeHistoryBuffer0352Inputs.getD i.val 0 = nativeReturnsEntry (49 + (352 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_12 : ∀ i < 384,
    nativeHistoryBufferCompletePrefix12.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 352 32
    (nativeHistoryBufferCompletePrefix11_length)
    nativeReturns_buffer_prefix_11
    (fun i hi => nativeReturns_buffer_block_0352 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix12]
  exact h

theorem nativeReturns_buffer_block_0384 : ∀ i : Fin 32,
    nativeHistoryBuffer0384Inputs.getD i.val 0 = nativeReturnsEntry (49 + (384 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_13 : ∀ i < 416,
    nativeHistoryBufferCompletePrefix13.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 384 32
    (nativeHistoryBufferCompletePrefix12_length)
    nativeReturns_buffer_prefix_12
    (fun i hi => nativeReturns_buffer_block_0384 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix13]
  exact h

theorem nativeReturns_buffer_block_0416 : ∀ i : Fin 32,
    nativeHistoryBuffer0416Inputs.getD i.val 0 = nativeReturnsEntry (49 + (416 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_14 : ∀ i < 448,
    nativeHistoryBufferCompletePrefix14.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 416 32
    (nativeHistoryBufferCompletePrefix13_length)
    nativeReturns_buffer_prefix_13
    (fun i hi => nativeReturns_buffer_block_0416 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix14]
  exact h

theorem nativeReturns_buffer_block_0448 : ∀ i : Fin 32,
    nativeHistoryBuffer0448Inputs.getD i.val 0 = nativeReturnsEntry (49 + (448 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_15 : ∀ i < 480,
    nativeHistoryBufferCompletePrefix15.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 448 32
    (nativeHistoryBufferCompletePrefix14_length)
    nativeReturns_buffer_prefix_14
    (fun i hi => nativeReturns_buffer_block_0448 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix15]
  exact h

theorem nativeReturns_buffer_block_0480 : ∀ i : Fin 32,
    nativeHistoryBuffer0480Inputs.getD i.val 0 = nativeReturnsEntry (49 + (480 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_16 : ∀ i < 512,
    nativeHistoryBufferCompletePrefix16.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 480 32
    (nativeHistoryBufferCompletePrefix15_length)
    nativeReturns_buffer_prefix_15
    (fun i hi => nativeReturns_buffer_block_0480 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix16]
  exact h

theorem nativeReturns_buffer_block_0512 : ∀ i : Fin 32,
    nativeHistoryBuffer0512Inputs.getD i.val 0 = nativeReturnsEntry (49 + (512 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_17 : ∀ i < 544,
    nativeHistoryBufferCompletePrefix17.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 512 32
    (nativeHistoryBufferCompletePrefix16_length)
    nativeReturns_buffer_prefix_16
    (fun i hi => nativeReturns_buffer_block_0512 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix17]
  exact h

theorem nativeReturns_buffer_block_0544 : ∀ i : Fin 32,
    nativeHistoryBuffer0544Inputs.getD i.val 0 = nativeReturnsEntry (49 + (544 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_18 : ∀ i < 576,
    nativeHistoryBufferCompletePrefix18.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 544 32
    (nativeHistoryBufferCompletePrefix17_length)
    nativeReturns_buffer_prefix_17
    (fun i hi => nativeReturns_buffer_block_0544 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix18]
  exact h

theorem nativeReturns_buffer_block_0576 : ∀ i : Fin 32,
    nativeHistoryBuffer0576Inputs.getD i.val 0 = nativeReturnsEntry (49 + (576 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_19 : ∀ i < 608,
    nativeHistoryBufferCompletePrefix19.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 576 32
    (nativeHistoryBufferCompletePrefix18_length)
    nativeReturns_buffer_prefix_18
    (fun i hi => nativeReturns_buffer_block_0576 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix19]
  exact h

theorem nativeReturns_buffer_block_0608 : ∀ i : Fin 32,
    nativeHistoryBuffer0608Inputs.getD i.val 0 = nativeReturnsEntry (49 + (608 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_20 : ∀ i < 640,
    nativeHistoryBufferCompletePrefix20.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 608 32
    (nativeHistoryBufferCompletePrefix19_length)
    nativeReturns_buffer_prefix_19
    (fun i hi => nativeReturns_buffer_block_0608 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix20]
  exact h

theorem nativeReturns_buffer_block_0640 : ∀ i : Fin 32,
    nativeHistoryBuffer0640Inputs.getD i.val 0 = nativeReturnsEntry (49 + (640 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_21 : ∀ i < 672,
    nativeHistoryBufferCompletePrefix21.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 640 32
    (nativeHistoryBufferCompletePrefix20_length)
    nativeReturns_buffer_prefix_20
    (fun i hi => nativeReturns_buffer_block_0640 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix21]
  exact h

theorem nativeReturns_buffer_block_0672 : ∀ i : Fin 32,
    nativeHistoryBuffer0672Inputs.getD i.val 0 = nativeReturnsEntry (49 + (672 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_22 : ∀ i < 704,
    nativeHistoryBufferCompletePrefix22.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 672 32
    (nativeHistoryBufferCompletePrefix21_length)
    nativeReturns_buffer_prefix_21
    (fun i hi => nativeReturns_buffer_block_0672 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix22]
  exact h

theorem nativeReturns_buffer_block_0704 : ∀ i : Fin 32,
    nativeHistoryBuffer0704Inputs.getD i.val 0 = nativeReturnsEntry (49 + (704 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_23 : ∀ i < 736,
    nativeHistoryBufferCompletePrefix23.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 704 32
    (nativeHistoryBufferCompletePrefix22_length)
    nativeReturns_buffer_prefix_22
    (fun i hi => nativeReturns_buffer_block_0704 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix23]
  exact h

theorem nativeReturns_buffer_block_0736 : ∀ i : Fin 32,
    nativeHistoryBuffer0736Inputs.getD i.val 0 = nativeReturnsEntry (49 + (736 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_24 : ∀ i < 768,
    nativeHistoryBufferCompletePrefix24.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 736 32
    (nativeHistoryBufferCompletePrefix23_length)
    nativeReturns_buffer_prefix_23
    (fun i hi => nativeReturns_buffer_block_0736 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix24]
  exact h

theorem nativeReturns_buffer_block_0768 : ∀ i : Fin 32,
    nativeHistoryBuffer0768Inputs.getD i.val 0 = nativeReturnsEntry (49 + (768 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_25 : ∀ i < 800,
    nativeHistoryBufferCompletePrefix25.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 768 32
    (nativeHistoryBufferCompletePrefix24_length)
    nativeReturns_buffer_prefix_24
    (fun i hi => nativeReturns_buffer_block_0768 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix25]
  exact h

theorem nativeReturns_buffer_block_0800 : ∀ i : Fin 32,
    nativeHistoryBuffer0800Inputs.getD i.val 0 = nativeReturnsEntry (49 + (800 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_26 : ∀ i < 832,
    nativeHistoryBufferCompletePrefix26.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 800 32
    (nativeHistoryBufferCompletePrefix25_length)
    nativeReturns_buffer_prefix_25
    (fun i hi => nativeReturns_buffer_block_0800 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix26]
  exact h

theorem nativeReturns_buffer_block_0832 : ∀ i : Fin 32,
    nativeHistoryBuffer0832Inputs.getD i.val 0 = nativeReturnsEntry (49 + (832 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_27 : ∀ i < 864,
    nativeHistoryBufferCompletePrefix27.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 832 32
    (nativeHistoryBufferCompletePrefix26_length)
    nativeReturns_buffer_prefix_26
    (fun i hi => nativeReturns_buffer_block_0832 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix27]
  exact h

theorem nativeReturns_buffer_block_0864 : ∀ i : Fin 32,
    nativeHistoryBuffer0864Inputs.getD i.val 0 = nativeReturnsEntry (49 + (864 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_28 : ∀ i < 896,
    nativeHistoryBufferCompletePrefix28.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 864 32
    (nativeHistoryBufferCompletePrefix27_length)
    nativeReturns_buffer_prefix_27
    (fun i hi => nativeReturns_buffer_block_0864 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix28]
  exact h

theorem nativeReturns_buffer_block_0896 : ∀ i : Fin 32,
    nativeHistoryBuffer0896Inputs.getD i.val 0 = nativeReturnsEntry (49 + (896 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_29 : ∀ i < 928,
    nativeHistoryBufferCompletePrefix29.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 896 32
    (nativeHistoryBufferCompletePrefix28_length)
    nativeReturns_buffer_prefix_28
    (fun i hi => nativeReturns_buffer_block_0896 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix29]
  exact h

theorem nativeReturns_buffer_block_0928 : ∀ i : Fin 32,
    nativeHistoryBuffer0928Inputs.getD i.val 0 = nativeReturnsEntry (49 + (928 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_30 : ∀ i < 960,
    nativeHistoryBufferCompletePrefix30.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 928 32
    (nativeHistoryBufferCompletePrefix29_length)
    nativeReturns_buffer_prefix_29
    (fun i hi => nativeReturns_buffer_block_0928 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix30]
  exact h

theorem nativeReturns_buffer_block_0960 : ∀ i : Fin 32,
    nativeHistoryBuffer0960Inputs.getD i.val 0 = nativeReturnsEntry (49 + (960 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_31 : ∀ i < 992,
    nativeHistoryBufferCompletePrefix31.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 960 32
    (nativeHistoryBufferCompletePrefix30_length)
    nativeReturns_buffer_prefix_30
    (fun i hi => nativeReturns_buffer_block_0960 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix31]
  exact h

theorem nativeReturns_buffer_block_0992 : ∀ i : Fin 32,
    nativeHistoryBuffer0992Inputs.getD i.val 0 = nativeReturnsEntry (49 + (992 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_32 : ∀ i < 1024,
    nativeHistoryBufferCompletePrefix32.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 992 32
    (nativeHistoryBufferCompletePrefix31_length)
    nativeReturns_buffer_prefix_31
    (fun i hi => nativeReturns_buffer_block_0992 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix32]
  exact h

theorem nativeReturns_buffer_block_1024 : ∀ i : Fin 32,
    nativeHistoryBuffer1024Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1024 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_33 : ∀ i < 1056,
    nativeHistoryBufferCompletePrefix33.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1024 32
    (nativeHistoryBufferCompletePrefix32_length)
    nativeReturns_buffer_prefix_32
    (fun i hi => nativeReturns_buffer_block_1024 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix33]
  exact h

theorem nativeReturns_buffer_block_1056 : ∀ i : Fin 32,
    nativeHistoryBuffer1056Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1056 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_34 : ∀ i < 1088,
    nativeHistoryBufferCompletePrefix34.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1056 32
    (nativeHistoryBufferCompletePrefix33_length)
    nativeReturns_buffer_prefix_33
    (fun i hi => nativeReturns_buffer_block_1056 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix34]
  exact h

theorem nativeReturns_buffer_block_1088 : ∀ i : Fin 32,
    nativeHistoryBuffer1088Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1088 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_35 : ∀ i < 1120,
    nativeHistoryBufferCompletePrefix35.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1088 32
    (nativeHistoryBufferCompletePrefix34_length)
    nativeReturns_buffer_prefix_34
    (fun i hi => nativeReturns_buffer_block_1088 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix35]
  exact h

theorem nativeReturns_buffer_block_1120 : ∀ i : Fin 32,
    nativeHistoryBuffer1120Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1120 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_36 : ∀ i < 1152,
    nativeHistoryBufferCompletePrefix36.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1120 32
    (nativeHistoryBufferCompletePrefix35_length)
    nativeReturns_buffer_prefix_35
    (fun i hi => nativeReturns_buffer_block_1120 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix36]
  exact h

theorem nativeReturns_buffer_block_1152 : ∀ i : Fin 32,
    nativeHistoryBuffer1152Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1152 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_37 : ∀ i < 1184,
    nativeHistoryBufferCompletePrefix37.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1152 32
    (nativeHistoryBufferCompletePrefix36_length)
    nativeReturns_buffer_prefix_36
    (fun i hi => nativeReturns_buffer_block_1152 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix37]
  exact h

theorem nativeReturns_buffer_block_1184 : ∀ i : Fin 32,
    nativeHistoryBuffer1184Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1184 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_38 : ∀ i < 1216,
    nativeHistoryBufferCompletePrefix38.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1184 32
    (nativeHistoryBufferCompletePrefix37_length)
    nativeReturns_buffer_prefix_37
    (fun i hi => nativeReturns_buffer_block_1184 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix38]
  exact h

theorem nativeReturns_buffer_block_1216 : ∀ i : Fin 32,
    nativeHistoryBuffer1216Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1216 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_39 : ∀ i < 1248,
    nativeHistoryBufferCompletePrefix39.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1216 32
    (nativeHistoryBufferCompletePrefix38_length)
    nativeReturns_buffer_prefix_38
    (fun i hi => nativeReturns_buffer_block_1216 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix39]
  exact h

theorem nativeReturns_buffer_block_1248 : ∀ i : Fin 32,
    nativeHistoryBuffer1248Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1248 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_40 : ∀ i < 1280,
    nativeHistoryBufferCompletePrefix40.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1248 32
    (nativeHistoryBufferCompletePrefix39_length)
    nativeReturns_buffer_prefix_39
    (fun i hi => nativeReturns_buffer_block_1248 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix40]
  exact h

theorem nativeReturns_buffer_block_1280 : ∀ i : Fin 6,
    nativeHistoryBuffer1280Inputs.getD i.val 0 = nativeReturnsEntry (49 + (1280 + i.val)) := by
  decide +kernel

theorem nativeReturns_buffer_prefix_41 : ∀ i < 1286,
    nativeHistoryBufferCompletePrefix41.getD i 0 = nativeReturnsEntry (49 + i) := by
  have h := nativeReturns_entries_append (fun i => nativeReturnsEntry (49 + i)) _ _ 1280 6
    (nativeHistoryBufferCompletePrefix40_length)
    nativeReturns_buffer_prefix_40
    (fun i hi => nativeReturns_buffer_block_1280 ⟨i, hi⟩)
  rw [nativeHistoryBufferCompletePrefix41]
  exact h

end ASDExplicitGamma.Native
