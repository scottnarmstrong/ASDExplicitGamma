module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b74_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (542778475475492620783193/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4380769283491930268863/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11672755097846352121/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (661821150314072753/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (94549562684312411/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (552877288057859733779889/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4700170931694177225169/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3148838267571354669/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (714818449750225307/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (12769434423744511/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (34921248115589323887233/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2450408735784739278139/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3295149911676415371/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2923797518184691/78125000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b74_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B74.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1069909417208847/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b74_c0 :
    bflatChargeRowsFor (bflatBlockJ5B74.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (617670377997854825056007/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B74.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 18 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (542778475475492620783193/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b74_r000_c0]
    _ = (547827881766676177281541/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b74_r008_c0,
        List.drop_drop]
      ring
    _ = (617670377997854825056007/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b74_r016_c0,
        List.drop_drop]
      ring
    _ = (617670377997854825056007/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b74_c1 :
    bflatChargeRowsFor (bflatBlockJ5B74.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (20612289166156954266203/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B74.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 18 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (4380769283491930268863/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b74_r000_c1]
    _ = (567558763449131718377/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b74_r008_c1,
        List.drop_drop]
      ring
    _ = (20612289166156954266203/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b74_r016_c1,
        List.drop_drop]
      ring
    _ = (20612289166156954266203/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b74_c2 :
    bflatChargeRowsFor (bflatBlockJ5B74.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (3445407259976023271/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B74.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 18 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (11672755097846352121/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b74_r000_c2]
    _ = (24268108168131770797/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b74_r008_c2,
        List.drop_drop]
      ring
    _ = (3445407259976023271/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b74_r016_c2,
        List.drop_drop]
      ring
    _ = (3445407259976023271/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b74_c3 :
    bflatChargeRowsFor (bflatBlockJ5B74.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (390940660307029571/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B74.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 18 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (661821150314072753/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b74_r000_c3]
    _ = (68831980003214903/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b74_r008_c3,
        List.drop_drop]
      ring
    _ = (390940660307029571/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b74_r016_c3,
        List.drop_drop]
      ring
    _ = (390940660307029571/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b74_c4 :
    bflatChargeRowsFor (bflatBlockJ5B74.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (111726386752244837/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B74.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 18 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (94549562684312411/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b74_r000_c4]
    _ = (196705038074268499/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b74_r008_c4,
        List.drop_drop]
      ring
    _ = (111726386752244837/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b74_r016_c4,
        List.drop_drop]
      ring
    _ = (111726386752244837/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R12C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12)
      bflatExactSingletonBlocksJ5Seg0 =
      (617670377997854825056007/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R12_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b74_c0]
  norm_num

theorem bflatExactChargeJ5R12C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12)
      bflatExactSingletonBlocksJ5Seg1 =
      (20612289166156954266203/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R12_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b74_c1]
  norm_num

theorem bflatExactChargeJ5R12C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12)
      bflatExactSingletonBlocksJ5Seg2 =
      (3445407259976023271/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R12_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b74_c2]
  norm_num

theorem bflatExactChargeJ5R12C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12)
      bflatExactSingletonBlocksJ5Seg3 =
      (390940660307029571/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R12_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b74_c3]
  norm_num

theorem bflatExactChargeJ5R12C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R12)
      bflatExactSingletonBlocksJ5Seg4 =
      (111726386752244837/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R12_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b74_c4]
  norm_num

end ASDExplicitGamma.Model
