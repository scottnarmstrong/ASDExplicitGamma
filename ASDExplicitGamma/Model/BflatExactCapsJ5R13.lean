module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b75_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (282082377520110079785681/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5102065718727414592827/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13773572769265737451/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (782668817534160091/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (111901579984407263/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (114432324320836384169729/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (16951147835524724511/15625000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2946649910945452869/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (838079526264196893/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (23973642225424937/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (288801415179430780676283/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1416472861099119175849/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1207897372918683/1562500000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (440094954107876701/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b75_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B75.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (62963476418639657/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b75_c0 :
    bflatChargeRowsFor (bflatBlockJ5B75.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (142512779182383286109629/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B75.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 20 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (282082377520110079785681/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b75_r000_c0]
    _ = (1136326376644402080420007/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b75_r008_c0,
        List.drop_drop]
      ring
    _ = (142512779182383286109629/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b75_r016_c0,
        List.drop_drop]
      ring
    _ = (142512779182383286109629/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b75_c1 :
    bflatChargeRowsFor (bflatBlockJ5B75.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (2671875749658712957609/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B75.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 20 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (5102065718727414592827/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b75_r000_c1]
    _ = (10526433026095326436347/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b75_r008_c1,
        List.drop_drop]
      ring
    _ = (2671875749658712957609/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b75_r016_c1,
        List.drop_drop]
      ring
    _ = (2671875749658712957609/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b75_c2 :
    bflatChargeRowsFor (bflatBlockJ5B75.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (9059341377668143249/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B75.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 20 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (13773572769265737451/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b75_r000_c2]
    _ = (7126705580998250449/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b75_r008_c2,
        List.drop_drop]
      ring
    _ = (9059341377668143249/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b75_r016_c2,
        List.drop_drop]
      ring
    _ = (9059341377668143249/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b75_c3 :
    bflatChargeRowsFor (bflatBlockJ5B75.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (412168659581246737/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B75.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 20 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (782668817534160091/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b75_r000_c3]
    _ = (202593542974794623/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b75_r008_c3,
        List.drop_drop]
      ring
    _ = (412168659581246737/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b75_r016_c3,
        List.drop_drop]
      ring
    _ = (412168659581246737/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b75_c4 :
    bflatChargeRowsFor (bflatBlockJ5B75.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (58946653506034321/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B75.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 20 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (111901579984407263/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b75_r000_c4]
    _ = (57942447777882987/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b75_r008_c4,
        List.drop_drop]
      ring
    _ = (58946653506034321/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b75_r016_c4,
        List.drop_drop]
      ring
    _ = (58946653506034321/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R13C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13)
      bflatExactSingletonBlocksJ5Seg0 =
      (142512779182383286109629/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R13_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b75_c0]
  norm_num

theorem bflatExactChargeJ5R13C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13)
      bflatExactSingletonBlocksJ5Seg1 =
      (2671875749658712957609/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R13_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b75_c1]
  norm_num

theorem bflatExactChargeJ5R13C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13)
      bflatExactSingletonBlocksJ5Seg2 =
      (9059341377668143249/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R13_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b75_c2]
  norm_num

theorem bflatExactChargeJ5R13C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13)
      bflatExactSingletonBlocksJ5Seg3 =
      (412168659581246737/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R13_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b75_c3]
  norm_num

theorem bflatExactChargeJ5R13C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R13)
      bflatExactSingletonBlocksJ5Seg4 =
      (58946653506034321/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R13_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b75_c4]
  norm_num

end ASDExplicitGamma.Model
