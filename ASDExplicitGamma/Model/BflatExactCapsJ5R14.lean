module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b76_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (582503521600898051158003/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (11813291519706638726807/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8097850917880715201/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (922783148642155579/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (33014943520254603/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (36771139150970612282493/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2490355900121624717953/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3436498927932508287/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (6125781395686773/31250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (70161335316746447/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (44459181057104002906539/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (9754343209865842403577/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13538569730282001009/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (19326493194734657/125000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b76_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B76.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (110717757886531663/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b76_c0 :
    bflatChargeRowsFor (bflatBlockJ5B76.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1615433558587467876743281/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B76.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 22 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (582503521600898051158003/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b76_r000_c0]
    _ = (1170841748016427847677891/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b76_r008_c0,
        List.drop_drop]
      ring
    _ = (1615433558587467876743281/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b76_r016_c0,
        List.drop_drop]
      ring
    _ = (1615433558587467876743281/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b76_c1 :
    bflatChargeRowsFor (bflatBlockJ5B76.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (34019414230180604720149/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B76.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 22 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (11813291519706638726807/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b76_r000_c1]
    _ = (6066267755078690579143/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b76_r008_c1,
        List.drop_drop]
      ring
    _ = (34019414230180604720149/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b76_r016_c1,
        List.drop_drop]
      ring
    _ = (34019414230180604720149/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b76_c2 :
    bflatChargeRowsFor (bflatBlockJ5B76.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (23458383102852986423/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B76.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 22 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (8097850917880715201/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b76_r000_c2]
    _ = (33378196475423971837/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b76_r008_c2,
        List.drop_drop]
      ring
    _ = (23458383102852986423/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b76_r016_c2,
        List.drop_drop]
      ring
    _ = (23458383102852986423/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b76_c3 :
    bflatChargeRowsFor (bflatBlockJ5B76.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (2675967899741425539/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B76.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 22 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (922783148642155579/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b76_r000_c3]
    _ = (1902908171952039259/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b76_r008_c3,
        List.drop_drop]
      ring
    _ = (2675967899741425539/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b76_r016_c3,
        List.drop_drop]
      ring
    _ = (2675967899741425539/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b76_c4 :
    bflatChargeRowsFor (bflatBlockJ5B76.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (383100202601042969/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B76.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 22 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (33014943520254603/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b76_r000_c4]
    _ = (136191222357255653/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b76_r008_c4,
        List.drop_drop]
      ring
    _ = (383100202601042969/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b76_r016_c4,
        List.drop_drop]
      ring
    _ = (383100202601042969/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R14C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14)
      bflatExactSingletonBlocksJ5Seg0 =
      (1615433558587467876743281/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R14_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b76_c0]
  norm_num

theorem bflatExactChargeJ5R14C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14)
      bflatExactSingletonBlocksJ5Seg1 =
      (34019414230180604720149/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R14_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b76_c1]
  norm_num

theorem bflatExactChargeJ5R14C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14)
      bflatExactSingletonBlocksJ5Seg2 =
      (23458383102852986423/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R14_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b76_c2]
  norm_num

theorem bflatExactChargeJ5R14C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14)
      bflatExactSingletonBlocksJ5Seg3 =
      (2675967899741425539/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R14_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b76_c3]
  norm_num

theorem bflatExactChargeJ5R14C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R14)
      bflatExactSingletonBlocksJ5Seg4 =
      (383100202601042969/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R14_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b76_c4]
  norm_num

end ASDExplicitGamma.Model
