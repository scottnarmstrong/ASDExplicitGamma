module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b64_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B64.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg0 =
      (6196234272267275848901/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b64_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B64.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg1 =
      (15949880982461675421/125000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b64_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B64.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg2 =
      (1605567636018774549/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b64_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B64.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg3 =
      (22547739291894009/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b64_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B64.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg4 =
      (1284324408481721/1000000000000000000000000000 : ℚ) := by decide +kernel

theorem bflatExactChargeJ5R02C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02)
      bflatExactSingletonBlocksJ5Seg0 =
      (6196234272267275848901/250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R02_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b64_r000_c0]
  norm_num

theorem bflatExactChargeJ5R02C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02)
      bflatExactSingletonBlocksJ5Seg1 =
      (15949880982461675421/125000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R02_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b64_r000_c1]
  norm_num

theorem bflatExactChargeJ5R02C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02)
      bflatExactSingletonBlocksJ5Seg2 =
      (1605567636018774549/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R02_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b64_r000_c2]
  norm_num

theorem bflatExactChargeJ5R02C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02)
      bflatExactSingletonBlocksJ5Seg3 =
      (22547739291894009/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R02_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b64_r000_c3]
  norm_num

theorem bflatExactChargeJ5R02C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R02)
      bflatExactSingletonBlocksJ5Seg4 =
      (1284324408481721/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R02_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b64_r000_c4]
  norm_num

end ASDExplicitGamma.Model
