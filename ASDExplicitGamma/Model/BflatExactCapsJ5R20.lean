module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b82_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (569846083005648618356629/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (22083881794804303715739/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (17776838762109978831/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2089673595202348299/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (302438117309971079/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (564172667513523155591301/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (22330054421645801080117/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (36251179357498150309/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (16675684275056613/39062500000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (309129313764275353/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (13955511747106738073307/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (11275796459413021484789/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (18459243315339801919/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2177727527330391189/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (157802285603890031/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (552009920124293923705147/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5687163726598507163017/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (37554832348284024841/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4438681263478023943/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (321855944080945441/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (95545230448427471976727/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10023828504448017219261/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (4169704084217567307/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3949487345393669627/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b82_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B82.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (286570523702570959/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b82_c0 :
    bflatChargeRowsFor (bflatBlockJ5B82.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (10632715987382314767457/39062500000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B82.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 39 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (569846083005648618356629/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b82_r000_c0]
    _ = (113401875051917177394793/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b82_r008_c0,
        List.drop_drop]
      ring
    _ = (169223922040344129688021/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b82_r016_c0,
        List.drop_drop]
      ring
    _ = (2244249140527735220585357/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b82_r024_c0,
        List.drop_drop]
      ring
    _ = (10632715987382314767457/39062500000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b82_r032_c0,
        List.drop_drop]
      ring
    _ = (10632715987382314767457/39062500000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b82_c1 :
    bflatChargeRowsFor (bflatBlockJ5B82.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (13720230131320776357003/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B82.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 39 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (22083881794804303715739/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b82_r000_c1]
    _ = (2775871013528131549741/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b82_r008_c1,
        List.drop_drop]
      ring
    _ = (33482764567638073882717/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b82_r016_c1,
        List.drop_drop]
      ring
    _ = (44857092020835088208751/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b82_r024_c1,
        List.drop_drop]
      ring
    _ = (13720230131320776357003/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b82_r032_c1,
        List.drop_drop]
      ring
    _ = (13720230131320776357003/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b82_c2 :
    bflatChargeRowsFor (bflatBlockJ5B82.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (89817904267211137553/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B82.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 39 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (17776838762109978831/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b82_r000_c2]
    _ = (71804856881718107971/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b82_r008_c2,
        List.drop_drop]
      ring
    _ = (108723343512397711809/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b82_r016_c2,
        List.drop_drop]
      ring
    _ = (2925563517213634733/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b82_r024_c2,
        List.drop_drop]
      ring
    _ = (89817904267211137553/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b82_r032_c2,
        List.drop_drop]
      ring
    _ = (89817904267211137553/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b82_c3 :
    bflatChargeRowsFor (bflatBlockJ5B82.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (10595973014175832737/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B82.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 39 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (2089673595202348299/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b82_r000_c3]
    _ = (4224161182409594763/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b82_r008_c3,
        List.drop_drop]
      ring
    _ = (200059022179374561/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b82_r016_c3,
        List.drop_drop]
      ring
    _ = (17242458682957995847/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b82_r024_c3,
        List.drop_drop]
      ring
    _ = (10595973014175832737/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b82_r032_c3,
        List.drop_drop]
      ring
    _ = (10595973014175832737/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b82_c4 :
    bflatChargeRowsFor (bflatBlockJ5B82.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (767799235032771447/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B82.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 39 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (302438117309971079/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b82_r000_c4]
    _ = (19111482221070201/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b82_r008_c4,
        List.drop_drop]
      ring
    _ = (463586001141013247/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b82_r016_c4,
        List.drop_drop]
      ring
    _ = (249805589272594387/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b82_r024_c4,
        List.drop_drop]
      ring
    _ = (767799235032771447/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b82_r032_c4,
        List.drop_drop]
      ring
    _ = (767799235032771447/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R20C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20)
      bflatExactSingletonBlocksJ5Seg0 =
      (10632715987382314767457/39062500000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R20_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b82_c0]
  norm_num

theorem bflatExactChargeJ5R20C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20)
      bflatExactSingletonBlocksJ5Seg1 =
      (13720230131320776357003/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R20_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b82_c1]
  norm_num

theorem bflatExactChargeJ5R20C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20)
      bflatExactSingletonBlocksJ5Seg2 =
      (89817904267211137553/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R20_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b82_c2]
  norm_num

theorem bflatExactChargeJ5R20C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20)
      bflatExactSingletonBlocksJ5Seg3 =
      (10595973014175832737/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R20_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b82_c3]
  norm_num

theorem bflatExactChargeJ5R20C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R20)
      bflatExactSingletonBlocksJ5Seg4 =
      (767799235032771447/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R20_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b82_c4]
  norm_num

end ASDExplicitGamma.Model
