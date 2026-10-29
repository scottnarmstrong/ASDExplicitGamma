module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b79_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (121611246695865282936683/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3453208657046891941949/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6311317042478544757/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1455335093508439609/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (209145532596059659/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (121500671670011336806117/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8894379532052682786121/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (5241777720533638979/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3026161358321490869/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (217557948588021243/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (15159711243875322603143/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (18291896427217305240173/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13579594099694129121/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3140540250287394187/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (56475481802160829/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (94546843326278834596281/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (729927496729352048237/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (17450380946530668137/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1010169430756483909/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b79_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B79.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (72694616814621517/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b79_c0 :
    bflatChargeRowsFor (bflatBlockJ5B79.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (550033853722377835306211/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B79.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 29 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (121611246695865282936683/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b79_r000_c0]
    _ = (607779795914691549357/5000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b79_r008_c0,
        List.drop_drop]
      ring
    _ = (45548701039609900070993/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b79_r016_c0,
        List.drop_drop]
      ring
    _ = (550033853722377835306211/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b79_r024_c0,
        List.drop_drop]
      ring
    _ = (550033853722377835306211/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b79_c1 :
    bflatChargeRowsFor (bflatBlockJ5B79.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (254006010641510794117/39062500000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B79.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 29 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (3453208657046891941949/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b79_r000_c1]
    _ = (35054802349339825281987/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b79_r008_c1,
        List.drop_drop]
      ring
    _ = (666833734706964131527/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b79_r016_c1,
        List.drop_drop]
      ring
    _ = (254006010641510794117/39062500000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b79_r024_c1,
        List.drop_drop]
      ring
    _ = (254006010641510794117/39062500000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b79_c2 :
    bflatChargeRowsFor (bflatBlockJ5B79.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (48031862959250650151/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B79.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 29 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (6311317042478544757/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b79_r000_c2]
    _ = (51454156772582373923/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b79_r008_c2,
        List.drop_drop]
      ring
    _ = (15722668994394126433/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b79_r016_c2,
        List.drop_drop]
      ring
    _ = (48031862959250650151/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b79_r024_c2,
        List.drop_drop]
      ring
    _ = (48031862959250650151/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b79_c3 :
    bflatChargeRowsFor (bflatBlockJ5B79.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (2774427664284683023/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B79.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 29 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1455335093508439609/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b79_r000_c3]
    _ = (5936831545338370087/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b79_r008_c3,
        List.drop_drop]
      ring
    _ = (4538685897812882137/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b79_r016_c3,
        List.drop_drop]
      ring
    _ = (2774427664284683023/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b79_r024_c3,
        List.drop_drop]
      ring
    _ = (2774427664284683023/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b79_c4 :
    bflatChargeRowsFor (bflatBlockJ5B79.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (199498660505491813/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B79.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 29 := by decide +kernel
  have hnil : rows.drop 32 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (209145532596059659/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b79_r000_c4]
    _ = (213351740592040451/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b79_r008_c4,
        List.drop_drop]
      ring
    _ = (326302704196362109/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b79_r016_c4,
        List.drop_drop]
      ring
    _ = (199498660505491813/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b79_r024_c4,
        List.drop_drop]
      ring
    _ = (199498660505491813/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R17C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17)
      bflatExactSingletonBlocksJ5Seg0 =
      (550033853722377835306211/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R17_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b79_c0]
  norm_num

theorem bflatExactChargeJ5R17C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17)
      bflatExactSingletonBlocksJ5Seg1 =
      (254006010641510794117/39062500000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R17_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b79_c1]
  norm_num

theorem bflatExactChargeJ5R17C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17)
      bflatExactSingletonBlocksJ5Seg2 =
      (48031862959250650151/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R17_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b79_c2]
  norm_num

theorem bflatExactChargeJ5R17C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17)
      bflatExactSingletonBlocksJ5Seg3 =
      (2774427664284683023/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R17_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b79_c3]
  norm_num

theorem bflatExactChargeJ5R17C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R17)
      bflatExactSingletonBlocksJ5Seg4 =
      (199498660505491813/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R17_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b79_c4]
  norm_num

end ASDExplicitGamma.Model
