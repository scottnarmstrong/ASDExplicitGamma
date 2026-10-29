module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b78_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (302710490998631861994457/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (15372465254843803426311/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21921315756081050243/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (628920327526800123/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (90230813496329293/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (121392367102041868627949/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (15952657641412906180449/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11457472539182736621/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2633240448324661437/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (188985445419412097/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (303925101927611111364237/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (16517344869487385924669/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (23902173983760615147/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2750465649029119321/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (24686997475067151/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (228044376854733994123689/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3168095702616802066747/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (9216161460947287797/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (530768810787716837/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b78_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B78.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (76249508841881561/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b78_c0 :
    bflatChargeRowsFor (bflatBlockJ5B78.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1024138699108714641990411/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B78.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 27 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (302710490998631861994457/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b78_r000_c0]
    _ = (1212382817507473067128659/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b78_r008_c0,
        List.drop_drop]
      ring
    _ = (1820233021362695289857133/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b78_r016_c0,
        List.drop_drop]
      ring
    _ = (1024138699108714641990411/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b78_r024_c0,
        List.drop_drop]
      ring
    _ = (1024138699108714641990411/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b78_c1 :
    bflatChargeRowsFor (bflatBlockJ5B78.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (54178659170977699664923/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B78.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 27 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (15372465254843803426311/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b78_r000_c1]
    _ = (783128072406417740169/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b78_r008_c1,
        List.drop_drop]
      ring
    _ = (47842467765744095531429/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b78_r016_c1,
        List.drop_drop]
      ring
    _ = (54178659170977699664923/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b78_r024_c1,
        List.drop_drop]
      ring
    _ = (54178659170977699664923/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b78_c2 :
    bflatChargeRowsFor (bflatBlockJ5B78.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (77954596279154426429/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B78.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 27 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (21921315756081050243/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b78_r000_c2]
    _ = (8967252166889304697/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b78_r008_c2,
        List.drop_drop]
      ring
    _ = (8592304352275892329/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b78_r016_c2,
        List.drop_drop]
      ring
    _ = (77954596279154426429/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b78_r024_c2,
        List.drop_drop]
      ring
    _ = (77954596279154426429/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b78_c3 :
    bflatChargeRowsFor (bflatBlockJ5B78.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (2240231257259103731/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B78.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 27 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (628920327526800123/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b78_r000_c3]
    _ = (5148921758431861929/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b78_r008_c3,
        List.drop_drop]
      ring
    _ = (1263901985193757/1600000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b78_r016_c3,
        List.drop_drop]
      ring
    _ = (2240231257259103731/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b78_r024_c3,
        List.drop_drop]
      ring
    _ = (2240231257259103731/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b78_c4 :
    bflatChargeRowsFor (bflatBlockJ5B78.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (160798140263622363/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B78.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 27 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (90230813496329293/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b78_r000_c4]
    _ = (369447072412070683/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b78_r008_c4,
        List.drop_drop]
      ring
    _ = (566943052212607891/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b78_r016_c4,
        List.drop_drop]
      ring
    _ = (160798140263622363/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b78_r024_c4,
        List.drop_drop]
      ring
    _ = (160798140263622363/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R16C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16)
      bflatExactSingletonBlocksJ5Seg0 =
      (1024138699108714641990411/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R16_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b78_c0]
  norm_num

theorem bflatExactChargeJ5R16C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16)
      bflatExactSingletonBlocksJ5Seg1 =
      (54178659170977699664923/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R16_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b78_c1]
  norm_num

theorem bflatExactChargeJ5R16C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16)
      bflatExactSingletonBlocksJ5Seg2 =
      (77954596279154426429/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R16_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b78_c2]
  norm_num

theorem bflatExactChargeJ5R16C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16)
      bflatExactSingletonBlocksJ5Seg3 =
      (2240231257259103731/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R16_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b78_c3]
  norm_num

theorem bflatExactChargeJ5R16C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R16)
      bflatExactSingletonBlocksJ5Seg4 =
      (160798140263622363/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R16_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b78_c4]
  norm_num

end ASDExplicitGamma.Model
