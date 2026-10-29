module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b73_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (518021563368653862598989/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7427363073930643558947/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (9782478751204724187/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1107168189167906931/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1580666984816591/200000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (530242144141062205936297/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8050367659571673182119/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10659201959132020047/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1207456874880107721/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (10777361080822997/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (33544326523521120963993/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (525279560078278126767/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (55808381530304741/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (39531702209866653/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b73_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B73.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (2823275059611687/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b73_c0 :
    bflatChargeRowsFor (bflatBlockJ5B73.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (139419045069594788807909/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B73.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 17 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (518021563368653862598989/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b73_r000_c0]
    _ = (524131853754858034267643/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b73_r008_c0,
        List.drop_drop]
      ring
    _ = (139419045069594788807909/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b73_r016_c0,
        List.drop_drop]
      ring
    _ = (139419045069594788807909/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b73_c1 :
    bflatChargeRowsFor (bflatBlockJ5B73.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (82641449268294364973/50000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B73.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 17 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (7427363073930643558947/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b73_r000_c1]
    _ = (7738865366751158370533/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b73_r008_c1,
        List.drop_drop]
      ring
    _ = (82641449268294364973/50000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b73_r016_c1,
        List.drop_drop]
      ring
    _ = (82641449268294364973/50000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b73_c2 :
    bflatChargeRowsFor (bflatBlockJ5B73.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (21836890248594362759/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B73.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 17 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (9782478751204724187/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b73_r000_c2]
    _ = (10220840355168372117/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b73_r008_c2,
        List.drop_drop]
      ring
    _ = (21836890248594362759/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b73_r016_c2,
        List.drop_drop]
      ring
    _ = (21836890248594362759/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b73_c3 :
    bflatChargeRowsFor (bflatBlockJ5B73.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (154546992055467579/625000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B73.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 17 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1107168189167906931/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b73_r000_c3]
    _ = (578656266012003663/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b73_r008_c3,
        List.drop_drop]
      ring
    _ = (154546992055467579/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b73_r016_c3,
        List.drop_drop]
      ring
    _ = (154546992055467579/625000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b73_c4 :
    bflatChargeRowsFor (bflatBlockJ5B73.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (88272669062930137/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B73.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 17 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (1580666984816591/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b73_r000_c4]
    _ = (82626118943706763/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b73_r008_c4,
        List.drop_drop]
      ring
    _ = (88272669062930137/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b73_r016_c4,
        List.drop_drop]
      ring
    _ = (88272669062930137/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R11C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11)
      bflatExactSingletonBlocksJ5Seg0 =
      (139419045069594788807909/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R11_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b73_c0]
  norm_num

theorem bflatExactChargeJ5R11C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11)
      bflatExactSingletonBlocksJ5Seg1 =
      (82641449268294364973/50000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R11_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b73_c1]
  norm_num

theorem bflatExactChargeJ5R11C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11)
      bflatExactSingletonBlocksJ5Seg2 =
      (21836890248594362759/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R11_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b73_c2]
  norm_num

theorem bflatExactChargeJ5R11C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11)
      bflatExactSingletonBlocksJ5Seg3 =
      (154546992055467579/625000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R11_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b73_c3]
  norm_num

theorem bflatExactChargeJ5R11C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R11)
      bflatExactSingletonBlocksJ5Seg4 =
      (88272669062930137/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R11_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b73_c4]
  norm_num

end ASDExplicitGamma.Model
