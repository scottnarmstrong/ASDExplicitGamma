module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b70_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (438362690371823522797043/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1113926964498968240831/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1146173709180633123/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (12921964077650849/200000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (46058114097123877/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (11298075820479423733999/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1215045878034993158457/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3135159319056321617/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (8840826848193597/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b70_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B70.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1231134525723/488281250000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b70_c0 :
    bflatChargeRowsFor (bflatBlockJ5B70.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (664324206781411997477023/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B70.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 12 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (438362690371823522797043/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b70_r000_c0]
    _ = (664324206781411997477023/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b70_r008_c0,
        List.drop_drop]
      ring
    _ = (664324206781411997477023/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b70_c1 :
    bflatChargeRowsFor (bflatBlockJ5B70.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (3442899807032929640119/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B70.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 12 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (1113926964498968240831/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b70_r000_c1]
    _ = (3442899807032929640119/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b70_r008_c1,
        List.drop_drop]
      ring
    _ = (3442899807032929640119/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b70_c2 :
    bflatChargeRowsFor (bflatBlockJ5B70.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (34632921347497997/39062500000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B70.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 12 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (1146173709180633123/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b70_r000_c2]
    _ = (34632921347497997/39062500000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b70_r008_c2,
        List.drop_drop]
      ring
    _ = (34632921347497997/39062500000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b70_c3 :
    bflatChargeRowsFor (bflatBlockJ5B70.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (99973127781028633/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B70.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 12 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (12921964077650849/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b70_r000_c3]
    _ = (99973127781028633/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b70_r008_c3,
        List.drop_drop]
      ring
    _ = (99973127781028633/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b70_c4 :
    bflatChargeRowsFor (bflatBlockJ5B70.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (71271749183930917/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B70.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 12 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (46058114097123877/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b70_r000_c4]
    _ = (71271749183930917/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b70_r008_c4,
        List.drop_drop]
      ring
    _ = (71271749183930917/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R08C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08)
      bflatExactSingletonBlocksJ5Seg0 =
      (664324206781411997477023/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R08_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b70_c0]
  norm_num

theorem bflatExactChargeJ5R08C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08)
      bflatExactSingletonBlocksJ5Seg1 =
      (3442899807032929640119/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R08_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b70_c1]
  norm_num

theorem bflatExactChargeJ5R08C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08)
      bflatExactSingletonBlocksJ5Seg2 =
      (34632921347497997/39062500000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R08_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b70_c2]
  norm_num

theorem bflatExactChargeJ5R08C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08)
      bflatExactSingletonBlocksJ5Seg3 =
      (99973127781028633/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R08_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b70_c3]
  norm_num

theorem bflatExactChargeJ5R08C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R08)
      bflatExactSingletonBlocksJ5Seg4 =
      (71271749183930917/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R08_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b70_c4]
  norm_num

end ASDExplicitGamma.Model
