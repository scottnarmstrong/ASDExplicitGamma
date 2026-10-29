module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b80_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (603444905955178093852657/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (953263539923090554961/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (28670153244518550939/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1661738643401887021/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (119637641572883871/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (60097743492107161367093/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4878163994048157906161/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14788328586307362449/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (343392274708717407/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (247367309156367957/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (299020173560333395735291/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (996871875574975690137/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15231671097275822673/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1771252437363224209/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (7979287964424251/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (148664542604388405424979/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10169511373947012988777/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (31328613168982380583/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (456129389163963713/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b80_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B80.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (263171427521312579/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b80_c0 :
    bflatChargeRowsFor (bflatBlockJ5B80.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (479424171682894024138817/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B80.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 32 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (603444905955178093852657/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b80_r000_c0]
    _ = (1204422340876249707523587/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b80_r008_c0,
        List.drop_drop]
      ring
    _ = (1802462687996916498994169/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b80_r016_c0,
        List.drop_drop]
      ring
    _ = (479424171682894024138817/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b80_r024_c0,
        List.drop_drop]
      ring
    _ = (479424171682894024138817/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b80_c1 :
    bflatChargeRowsFor (bflatBlockJ5B80.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (39427193517023991252079/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B80.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 32 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (953263539923090554961/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b80_r000_c1]
    _ = (4822240846831805340483/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b80_r008_c1,
        List.drop_drop]
      ring
    _ = (14628841071538489131651/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b80_r016_c1,
        List.drop_drop]
      ring
    _ = (39427193517023991252079/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b80_r024_c1,
        List.drop_drop]
      ring
    _ = (39427193517023991252079/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b80_c2 :
    bflatChargeRowsFor (bflatBlockJ5B80.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (60019382890333650883/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B80.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 32 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (28670153244518550939/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b80_r000_c2]
    _ = (58246810417133275837/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b80_r008_c2,
        List.drop_drop]
      ring
    _ = (88710152611684921183/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b80_r016_c2,
        List.drop_drop]
      ring
    _ = (60019382890333650883/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b80_r024_c2,
        List.drop_drop]
      ring
    _ = (60019382890333650883/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b80_c3 :
    bflatChargeRowsFor (bflatBlockJ5B80.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (6974470010964553117/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B80.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 32 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1661738643401887021/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b80_r000_c3]
    _ = (422337502118184257/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b80_r008_c3,
        List.drop_drop]
      ring
    _ = (1029990490861739653/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b80_r016_c3,
        List.drop_drop]
      ring
    _ = (6974470010964553117/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b80_r024_c3,
        List.drop_drop]
      ring
    _ = (6974470010964553117/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b80_c4 :
    bflatChargeRowsFor (bflatBlockJ5B80.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (100515123468502431/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B80.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 32 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (119637641572883871/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b80_r000_c4]
    _ = (486642592302135699/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b80_r008_c4,
        List.drop_drop]
      ring
    _ = (741979807163711731/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b80_r016_c4,
        List.drop_drop]
      ring
    _ = (100515123468502431/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b80_r024_c4,
        List.drop_drop]
      ring
    _ = (100515123468502431/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R18C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18)
      bflatExactSingletonBlocksJ5Seg0 =
      (479424171682894024138817/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R18_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b80_c0]
  norm_num

theorem bflatExactChargeJ5R18C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18)
      bflatExactSingletonBlocksJ5Seg1 =
      (39427193517023991252079/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R18_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b80_c1]
  norm_num

theorem bflatExactChargeJ5R18C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18)
      bflatExactSingletonBlocksJ5Seg2 =
      (60019382890333650883/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R18_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b80_c2]
  norm_num

theorem bflatExactChargeJ5R18C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18)
      bflatExactSingletonBlocksJ5Seg3 =
      (6974470010964553117/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R18_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b80_c3]
  norm_num

theorem bflatExactChargeJ5R18C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R18)
      bflatExactSingletonBlocksJ5Seg4 =
      (100515123468502431/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R18_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b80_c4]
  norm_num

end ASDExplicitGamma.Model
