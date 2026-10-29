module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b68_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (385656850554184495856379/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (785747735849393476797/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (800592944355077581/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (112646247458266801/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (32103077987548007/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (99757369915068550685719/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (42980846161192974683/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (548582212151416783/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (61770986161859361/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b68_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B68.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (4401552390076877/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b68_c0 :
    bflatChargeRowsFor (bflatBlockJ5B68.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (242707110234626523271049/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B68.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 10 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (385656850554184495856379/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b68_r000_c0]
    _ = (242707110234626523271049/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b68_r008_c0,
        List.drop_drop]
      ring
    _ = (242707110234626523271049/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b68_c1 :
    bflatChargeRowsFor (bflatBlockJ5B68.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (250162991663839587553/625000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B68.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 10 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (785747735849393476797/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b68_r000_c1]
    _ = (250162991663839587553/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b68_r008_c1,
        List.drop_drop]
      ring
    _ = (250162991663839587553/625000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b68_c2 :
    bflatChargeRowsFor (bflatBlockJ5B68.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (5100129146078221471/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B68.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 10 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (800592944355077581/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b68_r000_c2]
    _ = (5100129146078221471/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b68_r008_c2,
        List.drop_drop]
      ring
    _ = (5100129146078221471/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b68_c3 :
    bflatChargeRowsFor (bflatBlockJ5B68.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (287063481078392963/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B68.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 10 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (112646247458266801/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b68_r000_c3]
    _ = (287063481078392963/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b68_r008_c3,
        List.drop_drop]
      ring
    _ = (287063481078392963/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b68_c4 :
    bflatChargeRowsFor (bflatBlockJ5B68.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (40906182767701761/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B68.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 10 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (32103077987548007/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b68_r000_c4]
    _ = (40906182767701761/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b68_r008_c4,
        List.drop_drop]
      ring
    _ = (40906182767701761/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R06C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06)
      bflatExactSingletonBlocksJ5Seg0 =
      (242707110234626523271049/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R06_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b68_c0]
  norm_num

theorem bflatExactChargeJ5R06C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06)
      bflatExactSingletonBlocksJ5Seg1 =
      (250162991663839587553/625000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R06_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b68_c1]
  norm_num

theorem bflatExactChargeJ5R06C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06)
      bflatExactSingletonBlocksJ5Seg2 =
      (5100129146078221471/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R06_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b68_c2]
  norm_num

theorem bflatExactChargeJ5R06C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06)
      bflatExactSingletonBlocksJ5Seg3 =
      (287063481078392963/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R06_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b68_c3]
  norm_num

theorem bflatExactChargeJ5R06C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R06)
      bflatExactSingletonBlocksJ5Seg4 =
      (40906182767701761/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R06_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b68_c4]
  norm_num

end ASDExplicitGamma.Model
