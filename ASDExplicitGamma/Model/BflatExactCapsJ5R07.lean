module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b69_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (12869215215709635631131/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3746409497387819396897/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (4792858238010417063/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (33742662772420133/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (38474855475737833/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (159532265270328614886457/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (61418312090393556771/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1969408143677192029/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (221931897229052473/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b69_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B69.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (7909149048991753/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b69_c0 :
    bflatChargeRowsFor (bflatBlockJ5B69.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (571347152173036955082649/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B69.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 11 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (12869215215709635631131/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b69_r000_c0]
    _ = (571347152173036955082649/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b69_r008_c0,
        List.drop_drop]
      ring
    _ = (571347152173036955082649/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b69_c1 :
    bflatChargeRowsFor (bflatBlockJ5B69.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (1320466824911914579043/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B69.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 11 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (3746409497387819396897/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b69_r000_c1]
    _ = (1320466824911914579043/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b69_r008_c1,
        List.drop_drop]
      ring
    _ = (1320466824911914579043/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b69_c2 :
    bflatChargeRowsFor (bflatBlockJ5B69.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (1690566595421902273/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B69.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 11 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (4792858238010417063/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b69_r000_c2]
    _ = (1690566595421902273/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b69_r008_c2,
        List.drop_drop]
      ring
    _ = (1690566595421902273/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b69_c3 :
    bflatChargeRowsFor (bflatBlockJ5B69.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (761814501587774601/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B69.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 11 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (33742662772420133/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b69_r000_c3]
    _ = (761814501587774601/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b69_r008_c3,
        List.drop_drop]
      ring
    _ = (761814501587774601/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b69_c4 :
    bflatChargeRowsFor (bflatBlockJ5B69.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (54293153573721339/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B69.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 11 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (38474855475737833/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b69_r000_c4]
    _ = (54293153573721339/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b69_r008_c4,
        List.drop_drop]
      ring
    _ = (54293153573721339/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R07C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07)
      bflatExactSingletonBlocksJ5Seg0 =
      (571347152173036955082649/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R07_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b69_c0]
  norm_num

theorem bflatExactChargeJ5R07C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07)
      bflatExactSingletonBlocksJ5Seg1 =
      (1320466824911914579043/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R07_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b69_c1]
  norm_num

theorem bflatExactChargeJ5R07C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07)
      bflatExactSingletonBlocksJ5Seg2 =
      (1690566595421902273/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R07_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b69_c2]
  norm_num

theorem bflatExactChargeJ5R07C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07)
      bflatExactSingletonBlocksJ5Seg3 =
      (761814501587774601/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R07_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b69_c3]
  norm_num

theorem bflatExactChargeJ5R07C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R07)
      bflatExactSingletonBlocksJ5Seg4 =
      (54293153573721339/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R07_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b69_c4]
  norm_num

end ASDExplicitGamma.Model
