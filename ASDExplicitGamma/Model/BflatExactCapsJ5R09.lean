module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b71_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (464750286693477982064193/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (164927273747393716897/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (683127265271369853/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (385474396282705153/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (27488975911134383/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (71844188995873602243409/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (216646285285510401107/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1407606395419227731/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (127166299659774573/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b71_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B71.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (45352548931383327/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b71_c0 :
    bflatChargeRowsFor (bflatBlockJ5B71.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (411985615836422996640619/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B71.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 14 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (464750286693477982064193/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b71_r000_c0]
    _ = (411985615836422996640619/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b71_r008_c0,
        List.drop_drop]
      ring
    _ = (411985615836422996640619/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b71_c1 :
    bflatChargeRowsFor (bflatBlockJ5B71.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (2402649616406701740711/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B71.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 14 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (164927273747393716897/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b71_r000_c1]
    _ = (2402649616406701740711/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b71_r008_c1,
        List.drop_drop]
      ring
    _ = (2402649616406701740711/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b71_c2 :
    bflatChargeRowsFor (bflatBlockJ5B71.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (6230849117195304727/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B71.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 14 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (683127265271369853/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b71_r000_c2]
    _ = (6230849117195304727/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b71_r008_c2,
        List.drop_drop]
      ring
    _ = (6230849117195304727/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b71_c3 :
    bflatChargeRowsFor (bflatBlockJ5B71.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (1406780290864283171/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B71.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 14 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (385474396282705153/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b71_r000_c3]
    _ = (1406780290864283171/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b71_r008_c3,
        List.drop_drop]
      ring
    _ = (1406780290864283171/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b71_c4 :
    bflatChargeRowsFor (bflatBlockJ5B71.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (100330500753652093/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B71.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 14 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (27488975911134383/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b71_r000_c4]
    _ = (100330500753652093/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b71_r008_c4,
        List.drop_drop]
      ring
    _ = (100330500753652093/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R09C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09)
      bflatExactSingletonBlocksJ5Seg0 =
      (411985615836422996640619/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R09_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b71_c0]
  norm_num

theorem bflatExactChargeJ5R09C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09)
      bflatExactSingletonBlocksJ5Seg1 =
      (2402649616406701740711/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R09_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b71_c1]
  norm_num

theorem bflatExactChargeJ5R09C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09)
      bflatExactSingletonBlocksJ5Seg2 =
      (6230849117195304727/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R09_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b71_c2]
  norm_num

theorem bflatExactChargeJ5R09C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09)
      bflatExactSingletonBlocksJ5Seg3 =
      (1406780290864283171/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R09_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b71_c3]
  norm_num

theorem bflatExactChargeJ5R09C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R09)
      bflatExactSingletonBlocksJ5Seg4 =
      (100330500753652093/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R09_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b71_c4]
  norm_num

end ASDExplicitGamma.Model
