module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b72_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (123067396903010510324537/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3145303159519288609247/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (4104075198287070979/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (927554878893176487/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (13235239653012647/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (110605946299482403477707/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (599645743133530706003/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3930098597893641313/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (888903289268114267/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b72_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B72.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (247794134904537/39062500000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b72_c0 :
    bflatChargeRowsFor (bflatBlockJ5B72.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (58418335800623228450561/625000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B72.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 15 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (123067396903010510324537/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b72_r000_c0]
    _ = (58418335800623228450561/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b72_r008_c0,
        List.drop_drop]
      ring
    _ = (58418335800623228450561/625000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b72_c1 :
    bflatChargeRowsFor (bflatBlockJ5B72.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (3071765937593471069631/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B72.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 15 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (3145303159519288609247/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b72_r000_c1]
    _ = (3071765937593471069631/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b72_r008_c1,
        List.drop_drop]
      ring
    _ = (3071765937593471069631/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b72_c2 :
    bflatChargeRowsFor (bflatBlockJ5B72.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (2008543449045178073/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B72.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 15 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (4104075198287070979/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b72_r000_c2]
    _ = (2008543449045178073/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b72_r008_c2,
        List.drop_drop]
      ring
    _ = (2008543449045178073/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b72_c3 :
    bflatChargeRowsFor (bflatBlockJ5B72.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (908229084080645377/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B72.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 15 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (927554878893176487/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b72_r000_c3]
    _ = (908229084080645377/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b72_r008_c3,
        List.drop_drop]
      ring
    _ = (908229084080645377/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b72_c4 :
    bflatChargeRowsFor (bflatBlockJ5B72.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (129611496800624707/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B72.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 15 := by decide +kernel
  have hnil : rows.drop 16 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (13235239653012647/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b72_r000_c4]
    _ = (129611496800624707/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b72_r008_c4,
        List.drop_drop]
      ring
    _ = (129611496800624707/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R10C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10)
      bflatExactSingletonBlocksJ5Seg0 =
      (58418335800623228450561/625000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R10_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b72_c0]
  norm_num

theorem bflatExactChargeJ5R10C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10)
      bflatExactSingletonBlocksJ5Seg1 =
      (3071765937593471069631/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R10_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b72_c1]
  norm_num

theorem bflatExactChargeJ5R10C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10)
      bflatExactSingletonBlocksJ5Seg2 =
      (2008543449045178073/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R10_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b72_c2]
  norm_num

theorem bflatExactChargeJ5R10C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10)
      bflatExactSingletonBlocksJ5Seg3 =
      (908229084080645377/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R10_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b72_c3]
  norm_num

theorem bflatExactChargeJ5R10C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R10)
      bflatExactSingletonBlocksJ5Seg4 =
      (129611496800624707/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R10_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b72_c4]
  norm_num

end ASDExplicitGamma.Model
