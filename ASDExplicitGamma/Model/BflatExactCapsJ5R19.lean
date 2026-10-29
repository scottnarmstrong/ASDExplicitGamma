module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b81_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (295427493386502352269677/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1035846012408844582497/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6434193369239377369/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (150133350808298659/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (33857120917159941/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (586654418688409084402133/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4214147458265257239763/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16494497327030303893/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3855230384355277017/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (278381474449576533/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (582079616487196722024249/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (21400177009578089995843/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (527834141608239989/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3954564054940517459/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (4464581771214407/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (115430649287893878788939/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10852517603045503076373/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (134948927849433031/39062500000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4051183730358787141/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (146450597358567627/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (84021273838153919053/3906250000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8212945663893604006433/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13146789173474018459/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (61741009352046149/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b81_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B81.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (27911656217326901/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b81_c0 :
    bflatChargeRowsFor (bflatBlockJ5B81.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (2551836729413753937686111/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B81.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 35 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (295427493386502352269677/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b81_r000_c0]
    _ = (1177509405461413788941487/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b81_r008_c0,
        List.drop_drop]
      ring
    _ = (219948627743576313870717/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b81_r016_c0,
        List.drop_drop]
      ring
    _ = (2336742268388079904910431/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b81_r024_c0,
        List.drop_drop]
      ring
    _ = (2551836729413753937686111/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b81_r032_c0,
        List.drop_drop]
      ring
    _ = (2551836729413753937686111/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b81_c1 :
    bflatChargeRowsFor (bflatBlockJ5B81.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (93105815419065878003777/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B81.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 35 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (1035846012408844582497/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b81_r000_c1]
    _ = (8357531507900635569751/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b81_r008_c1,
        List.drop_drop]
      ring
    _ = (31593917274540633922299/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b81_r016_c1,
        List.drop_drop]
      ring
    _ = (2652902179849133562417/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b81_r024_c1,
        List.drop_drop]
      ring
    _ = (93105815419065878003777/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b81_r032_c1,
        List.drop_drop]
      ring
    _ = (93105815419065878003777/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b81_c2 :
    bflatChargeRowsFor (bflatBlockJ5B81.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (73317530633056864161/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B81.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 35 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (6434193369239377369/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b81_r000_c2]
    _ = (65159961500257494631/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b81_r008_c2,
        List.drop_drop]
      ring
    _ = (98941346563184853927/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b81_r016_c2,
        List.drop_drop]
      ring
    _ = (133488272092639709863/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b81_r024_c2,
        List.drop_drop]
      ring
    _ = (73317530633056864161/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b81_r032_c2,
        List.drop_drop]
      ring
    _ = (73317530633056864161/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b81_c3 :
    bflatChargeRowsFor (bflatBlockJ5B81.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (17157837173663201817/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B81.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 35 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (150133350808298659/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b81_r000_c3]
    _ = (1902141038640685873/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b81_r008_c3,
        List.drop_drop]
      ring
    _ = (11563128209503260951/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b81_r016_c3,
        List.drop_drop]
      ring
    _ = (3903577984965512023/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b81_r024_c3,
        List.drop_drop]
      ring
    _ = (17157837173663201817/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b81_r032_c3,
        List.drop_drop]
      ring
    _ = (17157837173663201817/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b81_c4 :
    bflatChargeRowsFor (bflatBlockJ5B81.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (1239519494731020967/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B81.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 35 := by decide +kernel
  have hnil : rows.drop 40 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (33857120917159941/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b81_r000_c4]
    _ = (549238441786856061/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b81_r008_c4,
        List.drop_drop]
      ring
    _ = (834971675144578109/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b81_r016_c4,
        List.drop_drop]
      ring
    _ = (1127872869861713363/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b81_r024_c4,
        List.drop_drop]
      ring
    _ = (1239519494731020967/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b81_r032_c4,
        List.drop_drop]
      ring
    _ = (1239519494731020967/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R19C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19)
      bflatExactSingletonBlocksJ5Seg0 =
      (2551836729413753937686111/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R19_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b81_c0]
  norm_num

theorem bflatExactChargeJ5R19C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19)
      bflatExactSingletonBlocksJ5Seg1 =
      (93105815419065878003777/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R19_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b81_c1]
  norm_num

theorem bflatExactChargeJ5R19C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19)
      bflatExactSingletonBlocksJ5Seg2 =
      (73317530633056864161/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R19_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b81_c2]
  norm_num

theorem bflatExactChargeJ5R19C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19)
      bflatExactSingletonBlocksJ5Seg3 =
      (17157837173663201817/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R19_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b81_c3]
  norm_num

theorem bflatExactChargeJ5R19C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R19)
      bflatExactSingletonBlocksJ5Seg4 =
      (1239519494731020967/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R19_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b81_c4]
  norm_num

end ASDExplicitGamma.Model
