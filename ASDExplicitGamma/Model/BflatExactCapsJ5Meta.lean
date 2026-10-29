module

public import ASDExplicitGamma.Model.BflatExactCapsData

@[expose] public section

namespace ASDExplicitGamma.Model

open ASDExplicitGamma.Numerics.Model

private theorem bflatSingletonModeBlocks_lowerSum (es : List (ℕ × ModeData)) :
    ((es.map bflatSingletonModeBlock).map ModeBlockData.sineLower).sum =
      (es.map (fun e => e.2.enclosure.sine.lo)).sum := by
  simp [bflatSingletonModeBlock, Function.comp_def]

theorem bflat_lowerSum_le_singletonBlocks {bs : List ModeBlockData}
    (hm : ∀ b ∈ bs, blockMassCheck b = true) :
    blockLowerSum bs ≤ blockLowerSum (bflatSingletonModeBlocks bs) := by
  induction bs with
  | nil => simp [blockLowerSum, bflatSingletonModeBlocks]
  | cons b bs ih =>
    have hb : b.sineLower ≤ (b.entries.map (fun e => e.2.enclosure.sine.lo)).sum := by
      simpa [entrySum] using (of_decide_eq_true (hm b (by simp))).2.2.1
    have hmTail : ∀ c ∈ bs, blockMassCheck c = true := by
      intro c hc
      exact hm c (by simp [hc])
    simp only [bflatSingletonModeBlocks, List.flatMap_cons, List.map_append,
      List.sum_append, blockLowerSum, List.map_cons, List.sum_cons]
    rw [bflatSingletonModeBlocks_lowerSum]
    exact add_le_add hb (ih hmTail)

def bflatExactSingletonBlocksJ5Seg0 : List ModeBlockData :=
  bflatSingletonModeBlocks (bflatBlocksJ5.take 85)

def bflatExactSingletonBlocksJ5Seg1 : List ModeBlockData :=
  bflatSingletonModeBlocks ((bflatBlocksJ5.drop 85).take 7)

def bflatExactSingletonBlocksJ5Seg2 : List ModeBlockData :=
  bflatSingletonModeBlocks ((bflatBlocksJ5.drop 92).take 4)

def bflatExactSingletonBlocksJ5Seg3 : List ModeBlockData :=
  bflatSingletonModeBlocks ((bflatBlocksJ5.drop 96).take 3)

def bflatExactSingletonBlocksJ5Seg4 : List ModeBlockData :=
  bflatSingletonModeBlocks (bflatBlocksJ5.drop 99)

theorem bflatBlocksJ5_partition :
    bflatBlocksJ5 = bflatBlocksJ5.take 85 ++
      (bflatBlocksJ5.drop 85).take 7 ++
      (bflatBlocksJ5.drop 92).take 4 ++
      (bflatBlocksJ5.drop 96).take 3 ++
      bflatBlocksJ5.drop 99 := by
  rfl

theorem bflatExactSingletonBlocksJ5_partition :
    bflatExactSingletonBlocksJ5 =
      bflatExactSingletonBlocksJ5Seg0 ++ bflatExactSingletonBlocksJ5Seg1 ++
        bflatExactSingletonBlocksJ5Seg2 ++ bflatExactSingletonBlocksJ5Seg3 ++
        bflatExactSingletonBlocksJ5Seg4 := by
  rw [bflatExactSingletonBlocksJ5, bflatBlocksJ5_partition]
  simp [bflatSingletonModeBlocks, List.flatMap_append,
    bflatExactSingletonBlocksJ5Seg0, bflatExactSingletonBlocksJ5Seg1,
    bflatExactSingletonBlocksJ5Seg2, bflatExactSingletonBlocksJ5Seg3,
    bflatExactSingletonBlocksJ5Seg4]

def bflatBlocksJ5R00 : List ModeBlockData := bflatBlocksJ5.take 32
def bflatBlocksJ5R01 : List ModeBlockData := (bflatBlocksJ5.drop 32).take 32
def bflatBlocksJ5R02 : List ModeBlockData := (bflatBlocksJ5.drop 64).take 1
def bflatBlocksJ5R03 : List ModeBlockData := (bflatBlocksJ5.drop 65).take 1
def bflatBlocksJ5R04 : List ModeBlockData := (bflatBlocksJ5.drop 66).take 1
def bflatBlocksJ5R05 : List ModeBlockData := (bflatBlocksJ5.drop 67).take 1
def bflatBlocksJ5R06 : List ModeBlockData := (bflatBlocksJ5.drop 68).take 1
def bflatBlocksJ5R07 : List ModeBlockData := (bflatBlocksJ5.drop 69).take 1
def bflatBlocksJ5R08 : List ModeBlockData := (bflatBlocksJ5.drop 70).take 1
def bflatBlocksJ5R09 : List ModeBlockData := (bflatBlocksJ5.drop 71).take 1
def bflatBlocksJ5R10 : List ModeBlockData := (bflatBlocksJ5.drop 72).take 1
def bflatBlocksJ5R11 : List ModeBlockData := (bflatBlocksJ5.drop 73).take 1
def bflatBlocksJ5R12 : List ModeBlockData := (bflatBlocksJ5.drop 74).take 1
def bflatBlocksJ5R13 : List ModeBlockData := (bflatBlocksJ5.drop 75).take 1
def bflatBlocksJ5R14 : List ModeBlockData := (bflatBlocksJ5.drop 76).take 1
def bflatBlocksJ5R15 : List ModeBlockData := (bflatBlocksJ5.drop 77).take 1
def bflatBlocksJ5R16 : List ModeBlockData := (bflatBlocksJ5.drop 78).take 1
def bflatBlocksJ5R17 : List ModeBlockData := (bflatBlocksJ5.drop 79).take 1
def bflatBlocksJ5R18 : List ModeBlockData := (bflatBlocksJ5.drop 80).take 1
def bflatBlocksJ5R19 : List ModeBlockData := (bflatBlocksJ5.drop 81).take 1
def bflatBlocksJ5R20 : List ModeBlockData := (bflatBlocksJ5.drop 82).take 1
def bflatBlocksJ5R21 : List ModeBlockData := (bflatBlocksJ5.drop 83).take 1
def bflatBlocksJ5R22 : List ModeBlockData := (bflatBlocksJ5.drop 84).take 1
def bflatBlocksJ5R23 : List ModeBlockData := (bflatBlocksJ5.drop 85).take 1
def bflatBlocksJ5R24 : List ModeBlockData := (bflatBlocksJ5.drop 86).take 1
def bflatBlocksJ5R25 : List ModeBlockData := (bflatBlocksJ5.drop 87).take 1
def bflatBlocksJ5R26 : List ModeBlockData := (bflatBlocksJ5.drop 88).take 1
def bflatBlocksJ5R27 : List ModeBlockData := (bflatBlocksJ5.drop 89).take 1
def bflatBlocksJ5R28 : List ModeBlockData := (bflatBlocksJ5.drop 90).take 1
def bflatBlocksJ5R29 : List ModeBlockData := (bflatBlocksJ5.drop 91).take 1
def bflatBlocksJ5R30 : List ModeBlockData := (bflatBlocksJ5.drop 92).take 1
def bflatBlocksJ5R31 : List ModeBlockData := (bflatBlocksJ5.drop 93).take 1
def bflatBlocksJ5R32 : List ModeBlockData := (bflatBlocksJ5.drop 94).take 1
def bflatBlocksJ5R33 : List ModeBlockData := (bflatBlocksJ5.drop 95).take 1
def bflatBlocksJ5R34 : List ModeBlockData := (bflatBlocksJ5.drop 96).take 1
def bflatBlocksJ5R35 : List ModeBlockData := (bflatBlocksJ5.drop 97).take 1
def bflatBlocksJ5R36 : List ModeBlockData := (bflatBlocksJ5.drop 98).take 1
def bflatBlocksJ5R37 : List ModeBlockData := (bflatBlocksJ5.drop 99).take 1

theorem bflatBlocksJ5R00_eq : bflatBlocksJ5R00 = [bflatBlockJ5B0, bflatBlockJ5B1, bflatBlockJ5B2, bflatBlockJ5B3, bflatBlockJ5B4, bflatBlockJ5B5, bflatBlockJ5B6, bflatBlockJ5B7, bflatBlockJ5B8, bflatBlockJ5B9, bflatBlockJ5B10, bflatBlockJ5B11, bflatBlockJ5B12, bflatBlockJ5B13, bflatBlockJ5B14, bflatBlockJ5B15, bflatBlockJ5B16, bflatBlockJ5B17, bflatBlockJ5B18, bflatBlockJ5B19, bflatBlockJ5B20, bflatBlockJ5B21, bflatBlockJ5B22, bflatBlockJ5B23, bflatBlockJ5B24, bflatBlockJ5B25, bflatBlockJ5B26, bflatBlockJ5B27, bflatBlockJ5B28, bflatBlockJ5B29, bflatBlockJ5B30, bflatBlockJ5B31] := by
  rfl

theorem bflatBlocksJ5R01_eq : bflatBlocksJ5R01 = [bflatBlockJ5B32, bflatBlockJ5B33, bflatBlockJ5B34, bflatBlockJ5B35, bflatBlockJ5B36, bflatBlockJ5B37, bflatBlockJ5B38, bflatBlockJ5B39, bflatBlockJ5B40, bflatBlockJ5B41, bflatBlockJ5B42, bflatBlockJ5B43, bflatBlockJ5B44, bflatBlockJ5B45, bflatBlockJ5B46, bflatBlockJ5B47, bflatBlockJ5B48, bflatBlockJ5B49, bflatBlockJ5B50, bflatBlockJ5B51, bflatBlockJ5B52, bflatBlockJ5B53, bflatBlockJ5B54, bflatBlockJ5B55, bflatBlockJ5B56, bflatBlockJ5B57, bflatBlockJ5B58, bflatBlockJ5B59, bflatBlockJ5B60, bflatBlockJ5B61, bflatBlockJ5B62, bflatBlockJ5B63] := by
  rfl

theorem bflatBlocksJ5R02_eq : bflatBlocksJ5R02 = [bflatBlockJ5B64] := by
  rfl

theorem bflatBlocksJ5R03_eq : bflatBlocksJ5R03 = [bflatBlockJ5B65] := by
  rfl

theorem bflatBlocksJ5R04_eq : bflatBlocksJ5R04 = [bflatBlockJ5B66] := by
  rfl

theorem bflatBlocksJ5R05_eq : bflatBlocksJ5R05 = [bflatBlockJ5B67] := by
  rfl

theorem bflatBlocksJ5R06_eq : bflatBlocksJ5R06 = [bflatBlockJ5B68] := by
  rfl

theorem bflatBlocksJ5R07_eq : bflatBlocksJ5R07 = [bflatBlockJ5B69] := by
  rfl

theorem bflatBlocksJ5R08_eq : bflatBlocksJ5R08 = [bflatBlockJ5B70] := by
  rfl

theorem bflatBlocksJ5R09_eq : bflatBlocksJ5R09 = [bflatBlockJ5B71] := by
  rfl

theorem bflatBlocksJ5R10_eq : bflatBlocksJ5R10 = [bflatBlockJ5B72] := by
  rfl

theorem bflatBlocksJ5R11_eq : bflatBlocksJ5R11 = [bflatBlockJ5B73] := by
  rfl

theorem bflatBlocksJ5R12_eq : bflatBlocksJ5R12 = [bflatBlockJ5B74] := by
  rfl

theorem bflatBlocksJ5R13_eq : bflatBlocksJ5R13 = [bflatBlockJ5B75] := by
  rfl

theorem bflatBlocksJ5R14_eq : bflatBlocksJ5R14 = [bflatBlockJ5B76] := by
  rfl

theorem bflatBlocksJ5R15_eq : bflatBlocksJ5R15 = [bflatBlockJ5B77] := by
  rfl

theorem bflatBlocksJ5R16_eq : bflatBlocksJ5R16 = [bflatBlockJ5B78] := by
  rfl

theorem bflatBlocksJ5R17_eq : bflatBlocksJ5R17 = [bflatBlockJ5B79] := by
  rfl

theorem bflatBlocksJ5R18_eq : bflatBlocksJ5R18 = [bflatBlockJ5B80] := by
  rfl

theorem bflatBlocksJ5R19_eq : bflatBlocksJ5R19 = [bflatBlockJ5B81] := by
  rfl

theorem bflatBlocksJ5R20_eq : bflatBlocksJ5R20 = [bflatBlockJ5B82] := by
  rfl

theorem bflatBlocksJ5R21_eq : bflatBlocksJ5R21 = [bflatBlockJ5B83] := by
  rfl

theorem bflatBlocksJ5R22_eq : bflatBlocksJ5R22 = [bflatBlockJ5B84] := by
  rfl

theorem bflatBlocksJ5R23_eq : bflatBlocksJ5R23 = [bflatBlockJ5B85] := by
  rfl

theorem bflatBlocksJ5R24_eq : bflatBlocksJ5R24 = [bflatBlockJ5B86] := by
  rfl

theorem bflatBlocksJ5R25_eq : bflatBlocksJ5R25 = [bflatBlockJ5B87] := by
  rfl

theorem bflatBlocksJ5R26_eq : bflatBlocksJ5R26 = [bflatBlockJ5B88] := by
  rfl

theorem bflatBlocksJ5R27_eq : bflatBlocksJ5R27 = [bflatBlockJ5B89] := by
  rfl

theorem bflatBlocksJ5R28_eq : bflatBlocksJ5R28 = [bflatBlockJ5B90] := by
  rfl

theorem bflatBlocksJ5R29_eq : bflatBlocksJ5R29 = [bflatBlockJ5B91] := by
  rfl

theorem bflatBlocksJ5R30_eq : bflatBlocksJ5R30 = [bflatBlockJ5B92] := by
  rfl

theorem bflatBlocksJ5R31_eq : bflatBlocksJ5R31 = [bflatBlockJ5B93] := by
  rfl

theorem bflatBlocksJ5R32_eq : bflatBlocksJ5R32 = [bflatBlockJ5B94] := by
  rfl

theorem bflatBlocksJ5R33_eq : bflatBlocksJ5R33 = [bflatBlockJ5B95] := by
  rfl

theorem bflatBlocksJ5R34_eq : bflatBlocksJ5R34 = [bflatBlockJ5B96] := by
  rfl

theorem bflatBlocksJ5R35_eq : bflatBlocksJ5R35 = [bflatBlockJ5B97] := by
  rfl

theorem bflatBlocksJ5R36_eq : bflatBlocksJ5R36 = [bflatBlockJ5B98] := by
  rfl

theorem bflatBlocksJ5R37_eq : bflatBlocksJ5R37 = [bflatBlockJ5B99] := by
  rfl
theorem bflatBlocksJ5_r_partition :
    bflatBlocksJ5 =
      bflatBlocksJ5R00 ++ bflatBlocksJ5R01 ++ bflatBlocksJ5R02 ++ bflatBlocksJ5R03 ++ bflatBlocksJ5R04 ++ bflatBlocksJ5R05 ++ bflatBlocksJ5R06 ++ bflatBlocksJ5R07 ++ bflatBlocksJ5R08 ++ bflatBlocksJ5R09 ++ bflatBlocksJ5R10 ++ bflatBlocksJ5R11 ++ bflatBlocksJ5R12 ++ bflatBlocksJ5R13 ++ bflatBlocksJ5R14 ++ bflatBlocksJ5R15 ++ bflatBlocksJ5R16 ++ bflatBlocksJ5R17 ++ bflatBlocksJ5R18 ++ bflatBlocksJ5R19 ++ bflatBlocksJ5R20 ++ bflatBlocksJ5R21 ++ bflatBlocksJ5R22 ++ bflatBlocksJ5R23 ++ bflatBlocksJ5R24 ++ bflatBlocksJ5R25 ++ bflatBlocksJ5R26 ++ bflatBlocksJ5R27 ++ bflatBlocksJ5R28 ++ bflatBlocksJ5R29 ++ bflatBlocksJ5R30 ++ bflatBlocksJ5R31 ++ bflatBlocksJ5R32 ++ bflatBlocksJ5R33 ++ bflatBlocksJ5R34 ++ bflatBlocksJ5R35 ++ bflatBlocksJ5R36 ++ bflatBlocksJ5R37 := by
  rfl

theorem bflatExactSingletonBlocksJ5_r_partition :
    bflatExactSingletonBlocksJ5 =
      bflatSingletonModeBlocks bflatBlocksJ5R00 ++ bflatSingletonModeBlocks bflatBlocksJ5R01 ++ bflatSingletonModeBlocks bflatBlocksJ5R02 ++ bflatSingletonModeBlocks bflatBlocksJ5R03 ++ bflatSingletonModeBlocks bflatBlocksJ5R04 ++ bflatSingletonModeBlocks bflatBlocksJ5R05 ++ bflatSingletonModeBlocks bflatBlocksJ5R06 ++ bflatSingletonModeBlocks bflatBlocksJ5R07 ++ bflatSingletonModeBlocks bflatBlocksJ5R08 ++ bflatSingletonModeBlocks bflatBlocksJ5R09 ++ bflatSingletonModeBlocks bflatBlocksJ5R10 ++ bflatSingletonModeBlocks bflatBlocksJ5R11 ++ bflatSingletonModeBlocks bflatBlocksJ5R12 ++ bflatSingletonModeBlocks bflatBlocksJ5R13 ++ bflatSingletonModeBlocks bflatBlocksJ5R14 ++ bflatSingletonModeBlocks bflatBlocksJ5R15 ++ bflatSingletonModeBlocks bflatBlocksJ5R16 ++ bflatSingletonModeBlocks bflatBlocksJ5R17 ++ bflatSingletonModeBlocks bflatBlocksJ5R18 ++ bflatSingletonModeBlocks bflatBlocksJ5R19 ++ bflatSingletonModeBlocks bflatBlocksJ5R20 ++ bflatSingletonModeBlocks bflatBlocksJ5R21 ++ bflatSingletonModeBlocks bflatBlocksJ5R22 ++ bflatSingletonModeBlocks bflatBlocksJ5R23 ++ bflatSingletonModeBlocks bflatBlocksJ5R24 ++ bflatSingletonModeBlocks bflatBlocksJ5R25 ++ bflatSingletonModeBlocks bflatBlocksJ5R26 ++ bflatSingletonModeBlocks bflatBlocksJ5R27 ++ bflatSingletonModeBlocks bflatBlocksJ5R28 ++ bflatSingletonModeBlocks bflatBlocksJ5R29 ++ bflatSingletonModeBlocks bflatBlocksJ5R30 ++ bflatSingletonModeBlocks bflatBlocksJ5R31 ++ bflatSingletonModeBlocks bflatBlocksJ5R32 ++ bflatSingletonModeBlocks bflatBlocksJ5R33 ++ bflatSingletonModeBlocks bflatBlocksJ5R34 ++ bflatSingletonModeBlocks bflatBlocksJ5R35 ++ bflatSingletonModeBlocks bflatBlocksJ5R36 ++ bflatSingletonModeBlocks bflatBlocksJ5R37 := by
  rw [bflatExactSingletonBlocksJ5, bflatBlocksJ5_r_partition]
  simp [bflatSingletonModeBlocks, List.flatMap_append]
def bflatChargeRowsFor (rows cols : List ModeBlockData) : ℚ :=
  (rows.map (fun a => blockChargeRow a cols)).sum

theorem blockChargeRow_append_cols (a : ModeBlockData)
    (xs ys : List ModeBlockData) :
    blockChargeRow a (xs ++ ys) = blockChargeRow a xs + blockChargeRow a ys := by
  simp [blockChargeRow]

theorem bflatChargeRowsFor_append_cols (rows : List ModeBlockData)
    (xs ys : List ModeBlockData) :
    bflatChargeRowsFor rows (xs ++ ys) =
      bflatChargeRowsFor rows xs + bflatChargeRowsFor rows ys := by
  induction rows with
  | nil => simp [bflatChargeRowsFor]
  | cons a rows ih =>
    change blockChargeRow a (xs ++ ys) + bflatChargeRowsFor rows (xs ++ ys) =
      (blockChargeRow a xs + bflatChargeRowsFor rows xs) +
        (blockChargeRow a ys + bflatChargeRowsFor rows ys)
    rw [blockChargeRow_append_cols a xs ys, ih]
    ring

theorem bflatChargeRowsFor_append_rows (xs ys : List ModeBlockData)
    (cols : List ModeBlockData) :
    bflatChargeRowsFor (xs ++ ys) cols =
      bflatChargeRowsFor xs cols + bflatChargeRowsFor ys cols := by
  simp [bflatChargeRowsFor, List.map_append, List.sum_append]

theorem bflatChargeRowsFor_singletonBlocks_blocks (bs : List ModeBlockData)
    (cols : List ModeBlockData) :
    bflatChargeRowsFor (bflatSingletonModeBlocks bs) cols =
      (bs.map (fun b => bflatChargeRowsFor
        (b.entries.map bflatSingletonModeBlock) cols)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change bflatChargeRowsFor
        (b.entries.map bflatSingletonModeBlock ++ bflatSingletonModeBlocks bs) cols = _
    rw [bflatChargeRowsFor_append_rows]
    simp only [List.map_cons, List.sum_cons]
    rw [ih]

theorem bflatChargeRowsFor_split_rows (rows cols : List ModeBlockData) (n : ℕ) :
    bflatChargeRowsFor rows cols =
      bflatChargeRowsFor (rows.take n) cols + bflatChargeRowsFor (rows.drop n) cols := by
  unfold bflatChargeRowsFor
  rw [← List.sum_take_add_sum_drop (rows.map (fun a => blockChargeRow a cols)) n,
    ← List.map_take, ← List.map_drop]

theorem bflatChargeRowsFor_five_cols (rows : List ModeBlockData) :
    bflatChargeRowsFor rows
      (bflatExactSingletonBlocksJ5Seg0 ++ bflatExactSingletonBlocksJ5Seg1 ++
        bflatExactSingletonBlocksJ5Seg2 ++ bflatExactSingletonBlocksJ5Seg3 ++
        bflatExactSingletonBlocksJ5Seg4) =
      bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 := by
  simp only [bflatChargeRowsFor_append_cols]

theorem bflatChargeRowsFor_exactJ5_cols (rows : List ModeBlockData) :
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5 =
      bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 := by
  calc
    _ = bflatChargeRowsFor rows
        (bflatExactSingletonBlocksJ5Seg0 ++ bflatExactSingletonBlocksJ5Seg1 ++
          bflatExactSingletonBlocksJ5Seg2 ++ bflatExactSingletonBlocksJ5Seg3 ++
          bflatExactSingletonBlocksJ5Seg4) := by
            exact congrArg (bflatChargeRowsFor rows)
              bflatExactSingletonBlocksJ5_partition
    _ = _ := bflatChargeRowsFor_five_cols rows

theorem bflatChargeRowsFor_r_partition (cols : List ModeBlockData) :
    bflatChargeRowsFor bflatExactSingletonBlocksJ5 cols =
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00 ++
        bflatSingletonModeBlocks bflatBlocksJ5R01 ++
        bflatSingletonModeBlocks bflatBlocksJ5R02 ++
        bflatSingletonModeBlocks bflatBlocksJ5R03 ++
        bflatSingletonModeBlocks bflatBlocksJ5R04 ++
        bflatSingletonModeBlocks bflatBlocksJ5R05 ++
        bflatSingletonModeBlocks bflatBlocksJ5R06 ++
        bflatSingletonModeBlocks bflatBlocksJ5R07 ++
        bflatSingletonModeBlocks bflatBlocksJ5R08 ++
        bflatSingletonModeBlocks bflatBlocksJ5R09 ++
        bflatSingletonModeBlocks bflatBlocksJ5R10 ++
        bflatSingletonModeBlocks bflatBlocksJ5R11 ++
        bflatSingletonModeBlocks bflatBlocksJ5R12 ++
        bflatSingletonModeBlocks bflatBlocksJ5R13 ++
        bflatSingletonModeBlocks bflatBlocksJ5R14 ++
        bflatSingletonModeBlocks bflatBlocksJ5R15 ++
        bflatSingletonModeBlocks bflatBlocksJ5R16 ++
        bflatSingletonModeBlocks bflatBlocksJ5R17 ++
        bflatSingletonModeBlocks bflatBlocksJ5R18 ++
        bflatSingletonModeBlocks bflatBlocksJ5R19 ++
        bflatSingletonModeBlocks bflatBlocksJ5R20 ++
        bflatSingletonModeBlocks bflatBlocksJ5R21 ++
        bflatSingletonModeBlocks bflatBlocksJ5R22 ++
        bflatSingletonModeBlocks bflatBlocksJ5R23 ++
        bflatSingletonModeBlocks bflatBlocksJ5R24 ++
        bflatSingletonModeBlocks bflatBlocksJ5R25 ++
        bflatSingletonModeBlocks bflatBlocksJ5R26 ++
        bflatSingletonModeBlocks bflatBlocksJ5R27 ++
        bflatSingletonModeBlocks bflatBlocksJ5R28 ++
        bflatSingletonModeBlocks bflatBlocksJ5R29 ++
        bflatSingletonModeBlocks bflatBlocksJ5R30 ++
        bflatSingletonModeBlocks bflatBlocksJ5R31 ++
        bflatSingletonModeBlocks bflatBlocksJ5R32 ++
        bflatSingletonModeBlocks bflatBlocksJ5R33 ++
        bflatSingletonModeBlocks bflatBlocksJ5R34 ++
        bflatSingletonModeBlocks bflatBlocksJ5R35 ++
        bflatSingletonModeBlocks bflatBlocksJ5R36 ++
        bflatSingletonModeBlocks bflatBlocksJ5R37) cols := by
  rw [bflatExactSingletonBlocksJ5_r_partition]

theorem bflatExactChargeJ5_partition :
    blockCharge bflatExactSingletonBlocksJ5 =
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg4 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg0 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg1 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg2 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg3 +
      bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg4 := by
  calc
    blockCharge bflatExactSingletonBlocksJ5 =
        bflatChargeRowsFor bflatExactSingletonBlocksJ5 bflatExactSingletonBlocksJ5 := rfl
    _ = bflatChargeRowsFor (
        bflatSingletonModeBlocks bflatBlocksJ5R00 ++
        bflatSingletonModeBlocks bflatBlocksJ5R01 ++
        bflatSingletonModeBlocks bflatBlocksJ5R02 ++
        bflatSingletonModeBlocks bflatBlocksJ5R03 ++
        bflatSingletonModeBlocks bflatBlocksJ5R04 ++
        bflatSingletonModeBlocks bflatBlocksJ5R05 ++
        bflatSingletonModeBlocks bflatBlocksJ5R06 ++
        bflatSingletonModeBlocks bflatBlocksJ5R07 ++
        bflatSingletonModeBlocks bflatBlocksJ5R08 ++
        bflatSingletonModeBlocks bflatBlocksJ5R09 ++
        bflatSingletonModeBlocks bflatBlocksJ5R10 ++
        bflatSingletonModeBlocks bflatBlocksJ5R11 ++
        bflatSingletonModeBlocks bflatBlocksJ5R12 ++
        bflatSingletonModeBlocks bflatBlocksJ5R13 ++
        bflatSingletonModeBlocks bflatBlocksJ5R14 ++
        bflatSingletonModeBlocks bflatBlocksJ5R15 ++
        bflatSingletonModeBlocks bflatBlocksJ5R16 ++
        bflatSingletonModeBlocks bflatBlocksJ5R17 ++
        bflatSingletonModeBlocks bflatBlocksJ5R18 ++
        bflatSingletonModeBlocks bflatBlocksJ5R19 ++
        bflatSingletonModeBlocks bflatBlocksJ5R20 ++
        bflatSingletonModeBlocks bflatBlocksJ5R21 ++
        bflatSingletonModeBlocks bflatBlocksJ5R22 ++
        bflatSingletonModeBlocks bflatBlocksJ5R23 ++
        bflatSingletonModeBlocks bflatBlocksJ5R24 ++
        bflatSingletonModeBlocks bflatBlocksJ5R25 ++
        bflatSingletonModeBlocks bflatBlocksJ5R26 ++
        bflatSingletonModeBlocks bflatBlocksJ5R27 ++
        bflatSingletonModeBlocks bflatBlocksJ5R28 ++
        bflatSingletonModeBlocks bflatBlocksJ5R29 ++
        bflatSingletonModeBlocks bflatBlocksJ5R30 ++
        bflatSingletonModeBlocks bflatBlocksJ5R31 ++
        bflatSingletonModeBlocks bflatBlocksJ5R32 ++
        bflatSingletonModeBlocks bflatBlocksJ5R33 ++
        bflatSingletonModeBlocks bflatBlocksJ5R34 ++
        bflatSingletonModeBlocks bflatBlocksJ5R35 ++
        bflatSingletonModeBlocks bflatBlocksJ5R36 ++
        bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5 :=
      bflatChargeRowsFor_r_partition bflatExactSingletonBlocksJ5
    _ = bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5 := by
      simp only [bflatChargeRowsFor_append_rows]
    _ = bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R00) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R01) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36) bflatExactSingletonBlocksJ5Seg4 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg0 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg1 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg2 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg3 +
        bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37) bflatExactSingletonBlocksJ5Seg4 := by
      simp only [bflatChargeRowsFor_exactJ5_cols]
      ring

end ASDExplicitGamma.Model
