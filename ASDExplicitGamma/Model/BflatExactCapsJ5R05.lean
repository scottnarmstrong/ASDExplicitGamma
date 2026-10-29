module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b67_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (90104659137510212407789/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (659241088570483809533/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3346110196923122247/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (11763341242041717/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (26814038002741997/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (23330881698777623021367/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (36052750539980097861/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (458284922614826401/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5156994522518373/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b67_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B67.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1836919478416213/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b67_c0 :
    bflatChargeRowsFor (bflatBlockJ5B67.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (40708039994759609567389/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B67.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (90104659137510212407789/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b67_r000_c0]
    _ = (40708039994759609567389/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b67_r008_c0,
        List.drop_drop]
      ring
    _ = (40708039994759609567389/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b67_c1 :
    bflatChargeRowsFor (bflatBlockJ5B67.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (1498745929840868108371/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B67.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (659241088570483809533/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b67_r000_c1]
    _ = (1498745929840868108371/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b67_r008_c1,
        List.drop_drop]
      ring
    _ = (1498745929840868108371/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b67_c2 :
    bflatChargeRowsFor (bflatBlockJ5B67.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (475549389942243581/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B67.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (3346110196923122247/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b67_r000_c2]
    _ = (475549389942243581/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b67_r008_c2,
        List.drop_drop]
      ring
    _ = (475549389942243581/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b67_c3 :
    bflatChargeRowsFor (bflatBlockJ5B67.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (213998432485259337/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B67.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (11763341242041717/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b67_r000_c3]
    _ = (213998432485259337/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b67_r008_c3,
        List.drop_drop]
      ring
    _ = (213998432485259337/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b67_c4 :
    bflatChargeRowsFor (bflatBlockJ5B67.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (30487876959574423/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B67.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 9 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (26814038002741997/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b67_r000_c4]
    _ = (30487876959574423/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b67_r008_c4,
        List.drop_drop]
      ring
    _ = (30487876959574423/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R05C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05)
      bflatExactSingletonBlocksJ5Seg0 =
      (40708039994759609567389/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R05_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b67_c0]
  norm_num

theorem bflatExactChargeJ5R05C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05)
      bflatExactSingletonBlocksJ5Seg1 =
      (1498745929840868108371/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R05_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b67_c1]
  norm_num

theorem bflatExactChargeJ5R05C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05)
      bflatExactSingletonBlocksJ5Seg2 =
      (475549389942243581/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R05_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b67_c2]
  norm_num

theorem bflatExactChargeJ5R05C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05)
      bflatExactSingletonBlocksJ5Seg3 =
      (213998432485259337/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R05_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b67_c3]
  norm_num

theorem bflatExactChargeJ5R05C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R05)
      bflatExactSingletonBlocksJ5Seg4 =
      (30487876959574423/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R05_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b67_c4]
  norm_num

end ASDExplicitGamma.Model
