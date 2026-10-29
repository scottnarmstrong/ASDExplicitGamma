module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b89_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (240331090856999946000391/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (16392106827561663734991/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (7612382776670399049/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4942075253571383851/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (372093355187961519/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (29360711218460408295117/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (806271852373150481329/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (18849727325782805463/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (981292944094041319/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (73956418470476579/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (229569166910299319879061/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7930619978007789876063/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (37333867410088975999/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4870255960892254643/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (45927753374091753/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (28047627544686271933161/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (15599781913797834589353/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (4620736041601915451/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2416769928383508689/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (365019800912967863/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (219320542457756214781101/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1917663340325467195269/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (7319243924132617991/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4796403809751033399/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (11330681909289921/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (107193416314262314390313/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (15086036228377969208733/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3622552891844643743/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4758931617997590993/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (360114249398225907/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (104789404921909622551753/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (14834170965693597744429/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (35854448894120782701/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (590150421528761007/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (89405748398773197/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (102447612467851594964461/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (14585890838772371378651/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (17741788487268083703/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2341647685376708613/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (177556849902875183/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (200334672669755546074371/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (14341355834213749111441/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (35113475231376100729/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4645280052965670753/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (352591746229901963/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (98495156958107974733659/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1416037330475160473653/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8709167568669165777/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (461673918547659463/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b89_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B89.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (43836896967836901/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b89_c0 :
    bflatChargeRowsFor (bflatBlockJ5B89.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (2076178207366139507107861/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B89.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 76 := by decide +kernel
  have hnil : rows.drop 80 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (240331090856999946000391/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b89_r000_c0]
    _ = (475216780604683212361327/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r008_c0,
        List.drop_drop]
      ring
    _ = (176196486878745633060097/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r016_c0,
        List.drop_drop]
      ring
    _ = (232291741968118176926419/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r024_c0,
        List.drop_drop]
      ring
    _ = (1148487510330228922486777/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r032_c0,
        List.drop_drop]
      ring
    _ = (1362874342958753551267403/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r040_c0,
        List.drop_drop]
      ring
    _ = (1572453152802572796370909/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r048_c0,
        List.drop_drop]
      ring
    _ = (1777348377738275986299831/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r056_c0,
        List.drop_drop]
      ring
    _ = (988841525204015766187101/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r064_c0,
        List.drop_drop]
      ring
    _ = (2076178207366139507107861/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b89_r072_c0,
        List.drop_drop]
      ring
    _ = (2076178207366139507107861/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b89_c1 :
    bflatChargeRowsFor (bflatBlockJ5B89.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (145247512986875315076721/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B89.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 76 := by decide +kernel
  have hnil : rows.drop 80 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (16392106827561663734991/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b89_r000_c1]
    _ = (32517543875024673361571/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r008_c1,
        List.drop_drop]
      ring
    _ = (48378783831040253113697/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r016_c1,
        List.drop_drop]
      ring
    _ = (1279571314896761754061/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r024_c1,
        List.drop_drop]
      ring
    _ = (39659936233720912632601/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r032_c1,
        List.drop_drop]
      ring
    _ = (18881181739163958894787/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r040_c1,
        List.drop_drop]
      ring
    _ = (27310019915378348054591/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r048_c1,
        List.drop_drop]
      ring
    _ = (24765194100057152719403/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r056_c1,
        List.drop_drop]
      ring
    _ = (17270915791812439088557/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r064_c1,
        List.drop_drop]
      ring
    _ = (145247512986875315076721/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b89_r072_c1,
        List.drop_drop]
      ring
    _ = (145247512986875315076721/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b89_c2 :
    bflatChargeRowsFor (bflatBlockJ5B89.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (346752709054302815553/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B89.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 76 := by decide +kernel
  have hnil : rows.drop 80 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (7612382776670399049/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b89_r000_c2]
    _ = (75761368534917606171/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r008_c2,
        List.drop_drop]
      ring
    _ = (11309523594500658217/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r016_c2,
        List.drop_drop]
      ring
    _ = (75030562138910952889/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r024_c2,
        List.drop_drop]
      ring
    _ = (186657343898484995733/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r032_c2,
        List.drop_drop]
      ring
    _ = (222882872816931433163/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r040_c2,
        List.drop_drop]
      ring
    _ = (32342165213881526983/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r048_c2,
        List.drop_drop]
      ring
    _ = (29422089868558838327/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r056_c2,
        List.drop_drop]
      ring
    _ = (329334373916964483999/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r064_c2,
        List.drop_drop]
      ring
    _ = (346752709054302815553/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b89_r072_c2,
        List.drop_drop]
      ring
    _ = (346752709054302815553/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b89_c3 :
    bflatChargeRowsFor (bflatBlockJ5B89.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (45465819608136960209/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B89.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 76 := by decide +kernel
  have hnil : rows.drop 80 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (4942075253571383851/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b89_r000_c3]
    _ = (4924269987020795223/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r008_c3,
        List.drop_drop]
      ring
    _ = (14718795934933845089/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r016_c3,
        List.drop_drop]
      ring
    _ = (19552335791700862467/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r024_c3,
        List.drop_drop]
      ring
    _ = (12174369800725947933/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r032_c3,
        List.drop_drop]
      ring
    _ = (29107671219449486859/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r040_c3,
        List.drop_drop]
      ring
    _ = (6765774918335914983/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r048_c3,
        List.drop_drop]
      ring
    _ = (38512169962432992141/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r056_c3,
        List.drop_drop]
      ring
    _ = (21578725007699331447/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r064_c3,
        List.drop_drop]
      ring
    _ = (45465819608136960209/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b89_r072_c3,
        List.drop_drop]
      ring
    _ = (45465819608136960209/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b89_c4 :
    bflatChargeRowsFor (bflatBlockJ5B89.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (3437689373443642401/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B89.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 76 := by decide +kernel
  have hnil : rows.drop 80 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (372093355187961519/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b89_r000_c4]
    _ = (370937723770172207/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r008_c4,
        List.drop_drop]
      ring
    _ = (554648737266539219/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r016_c4,
        List.drop_drop]
      ring
    _ = (1474317275446046301/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r024_c4,
        List.drop_drop]
      ring
    _ = (1836899096543323773/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r032_c4,
        List.drop_drop]
      ring
    _ = (27462666824269371/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r040_c4,
        List.drop_drop]
      ring
    _ = (638659084884160617/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r048_c4,
        List.drop_drop]
      ring
    _ = (1454875019671196417/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r056_c4,
        List.drop_drop]
      ring
    _ = (3262341785572294797/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r064_c4,
        List.drop_drop]
      ring
    _ = (3437689373443642401/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b89_r072_c4,
        List.drop_drop]
      ring
    _ = (3437689373443642401/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R27C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27)
      bflatExactSingletonBlocksJ5Seg0 =
      (2076178207366139507107861/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R27_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b89_c0]
  norm_num

theorem bflatExactChargeJ5R27C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27)
      bflatExactSingletonBlocksJ5Seg1 =
      (145247512986875315076721/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R27_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b89_c1]
  norm_num

theorem bflatExactChargeJ5R27C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27)
      bflatExactSingletonBlocksJ5Seg2 =
      (346752709054302815553/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R27_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b89_c2]
  norm_num

theorem bflatExactChargeJ5R27C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27)
      bflatExactSingletonBlocksJ5Seg3 =
      (45465819608136960209/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R27_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b89_c3]
  norm_num

theorem bflatExactChargeJ5R27C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R27)
      bflatExactSingletonBlocksJ5Seg4 =
      (3437689373443642401/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R27_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b89_c4]
  norm_num

end ASDExplicitGamma.Model
