module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b66_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (333531445854556031973009/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2168826422744131908073/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1371410588582934179/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (15419722987776291/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (21963817137136069/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (10851181086996176103481/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (149795497621569319109/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (379482938026012201/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2133930999916537/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b66_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B66.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (3039831080139357/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b66_c0 :
    bflatChargeRowsFor (bflatBlockJ5B66.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (376936170202540736386933/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B66.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (333531445854556031973009/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b66_r000_c0]
    _ = (376936170202540736386933/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b66_r008_c0,
        List.drop_drop]
      ring
    _ = (376936170202540736386933/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b66_c1 :
    bflatChargeRowsFor (bflatBlockJ5B66.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (2468417417987270546291/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B66.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (2168826422744131908073/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b66_r000_c1]
    _ = (2468417417987270546291/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b66_r008_c1,
        List.drop_drop]
      ring
    _ = (2468417417987270546291/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b66_c2 :
    bflatChargeRowsFor (bflatBlockJ5B66.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (3122304115191880559/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B66.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (1371410588582934179/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b66_r000_c2]
    _ = (3122304115191880559/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b66_r008_c2,
        List.drop_drop]
      ring
    _ = (3122304115191880559/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b66_c3 :
    bflatChargeRowsFor (bflatBlockJ5B66.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (4388413496923207/125000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B66.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (15419722987776291/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b66_r000_c3]
    _ = (4388413496923207/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b66_r008_c3,
        List.drop_drop]
      ring
    _ = (4388413496923207/125000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b66_c4 :
    bflatChargeRowsFor (bflatBlockJ5B66.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (12501824108637713/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B66.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (21963817137136069/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b66_r000_c4]
    _ = (12501824108637713/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b66_r008_c4,
        List.drop_drop]
      ring
    _ = (12501824108637713/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R04C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04)
      bflatExactSingletonBlocksJ5Seg0 =
      (376936170202540736386933/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R04_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b66_c0]
  norm_num

theorem bflatExactChargeJ5R04C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04)
      bflatExactSingletonBlocksJ5Seg1 =
      (2468417417987270546291/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R04_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b66_c1]
  norm_num

theorem bflatExactChargeJ5R04C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04)
      bflatExactSingletonBlocksJ5Seg2 =
      (3122304115191880559/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R04_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b66_c2]
  norm_num

theorem bflatExactChargeJ5R04C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04)
      bflatExactSingletonBlocksJ5Seg3 =
      (4388413496923207/125000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R04_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b66_c3]
  norm_num

theorem bflatExactChargeJ5R04C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R04)
      bflatExactSingletonBlocksJ5Seg4 =
      (12501824108637713/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R04_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b66_c4]
  norm_num

end ASDExplicitGamma.Model
