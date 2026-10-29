module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b65_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B65.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg0 =
      (308214695741966260996087/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b65_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B65.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg1 =
      (893274043974816792271/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b65_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B65.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg2 =
      (450646343688620837/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b65_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B65.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg3 =
      (253237971576734339/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b65_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B65.entries.map bflatSingletonModeBlock)) bflatExactSingletonBlocksJ5Seg4 =
      (18032898427258897/10000000000000000000000000000 : ℚ) := by decide +kernel

theorem bflatExactChargeJ5R03C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03)
      bflatExactSingletonBlocksJ5Seg0 =
      (308214695741966260996087/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R03_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b65_r000_c0]
  norm_num

theorem bflatExactChargeJ5R03C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03)
      bflatExactSingletonBlocksJ5Seg1 =
      (893274043974816792271/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R03_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b65_r000_c1]
  norm_num

theorem bflatExactChargeJ5R03C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03)
      bflatExactSingletonBlocksJ5Seg2 =
      (450646343688620837/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R03_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b65_r000_c2]
  norm_num

theorem bflatExactChargeJ5R03C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03)
      bflatExactSingletonBlocksJ5Seg3 =
      (253237971576734339/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R03_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b65_r000_c3]
  norm_num

theorem bflatExactChargeJ5R03C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R03)
      bflatExactSingletonBlocksJ5Seg4 =
      (18032898427258897/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R03_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_tile_b65_r000_c4]
  norm_num

end ASDExplicitGamma.Model
