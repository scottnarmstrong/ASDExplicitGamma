module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b83_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (539737657363527816787239/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5763256003982832788673/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (38662293232963347581/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (183425548115059919/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (332949299260514711/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (266446645644161768939893/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (28976530637042010169/12500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (39206275985430661189/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4659019662327372931/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (10578732395250351/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (525864645557268951238267/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (23286196856582853415243/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (39717285052036238979/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4728839224573206267/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (343841895830307361/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (129667373927924525488987/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4673681333837317352173/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (40195043521395991447/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4795044034877715551/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (348912346257764087/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (255662529954540186108793/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (23428369703493051945417/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (40639370557179496087/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4857591265858648381/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (353727193125896829/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (189825821424563526235951/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8796653034576255040871/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15347476650151123453/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1836969857029281161/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b83_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B83.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (133836346845419813/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b83_c0 :
    bflatChargeRowsFor (bflatBlockJ5B83.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (2818315971254462306314777/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B83.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 43 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (539737657363527816787239/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b83_r000_c0]
    _ = (42905237946074054186681/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b83_r008_c0,
        List.drop_drop]
      ring
    _ = (399623898552280076476323/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b83_r016_c0,
        List.drop_drop]
      ring
    _ = (52929127248020460196531/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b83_r024_c0,
        List.drop_drop]
      ring
    _ = (1314245074914949390039413/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b83_r032_c0,
        List.drop_drop]
      ring
    _ = (2818315971254462306314777/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b83_r040_c0,
        List.drop_drop]
      ring
    _ = (2818315971254462306314777/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b83_c1 :
    bflatChargeRowsFor (bflatBlockJ5B83.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (1954904293584432600817/156250000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B83.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 43 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (5763256003982832788673/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b83_r000_c1]
    _ = (11558562131391234822473/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b83_r008_c1,
        List.drop_drop]
      ring
    _ = (13904089076429558541027/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b83_r016_c1,
        List.drop_drop]
      ring
    _ = (46444426025667189733/5000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b83_r024_c1,
        List.drop_drop]
      ring
    _ = (116317221754827431411417/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b83_r032_c1,
        List.drop_drop]
      ring
    _ = (1954904293584432600817/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b83_r040_c1,
        List.drop_drop]
      ring
    _ = (1954904293584432600817/156250000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b83_c2 :
    bflatChargeRowsFor (bflatBlockJ5B83.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (13360484062447303671/625000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B83.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 43 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (38662293232963347581/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b83_r000_c2]
    _ = (7786856921839400877/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b83_r008_c2,
        List.drop_drop]
      ring
    _ = (117585854270430247749/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b83_r016_c2,
        List.drop_drop]
      ring
    _ = (39445224447956559799/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b83_r024_c2,
        List.drop_drop]
      ring
    _ = (198420268349005735283/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b83_r032_c2,
        List.drop_drop]
      ring
    _ = (13360484062447303671/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b83_r040_c2,
        List.drop_drop]
      ring
    _ = (13360484062447303671/625000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b83_c3 :
    bflatChargeRowsFor (bflatBlockJ5B83.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (12731551373771361133/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B83.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 43 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (183425548115059919/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b83_r000_c3]
    _ = (4622329182601935453/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b83_r008_c3,
        List.drop_drop]
      ring
    _ = (13973497589777077173/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b83_r016_c3,
        List.drop_drop]
      ring
    _ = (4692135406163698181/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b83_r024_c3,
        List.drop_drop]
      ring
    _ = (4725226578102688221/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b83_r032_c3,
        List.drop_drop]
      ring
    _ = (12731551373771361133/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b83_r040_c3,
        List.drop_drop]
      ring
    _ = (12731551373771361133/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b83_c4 :
    bflatChargeRowsFor (bflatBlockJ5B83.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (1851786517967914033/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B83.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 43 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (332949299260514711/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b83_r000_c4]
    _ = (671468735908525943/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b83_r008_c4,
        List.drop_drop]
      ring
    _ = (126913828967354163/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b83_r016_c4,
        List.drop_drop]
      ring
    _ = (1364222977996597391/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b83_r024_c4,
        List.drop_drop]
      ring
    _ = (85897508556124711/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b83_r032_c4,
        List.drop_drop]
      ring
    _ = (1851786517967914033/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b83_r040_c4,
        List.drop_drop]
      ring
    _ = (1851786517967914033/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R21C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21)
      bflatExactSingletonBlocksJ5Seg0 =
      (2818315971254462306314777/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R21_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b83_c0]
  norm_num

theorem bflatExactChargeJ5R21C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21)
      bflatExactSingletonBlocksJ5Seg1 =
      (1954904293584432600817/156250000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R21_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b83_c1]
  norm_num

theorem bflatExactChargeJ5R21C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21)
      bflatExactSingletonBlocksJ5Seg2 =
      (13360484062447303671/625000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R21_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b83_c2]
  norm_num

theorem bflatExactChargeJ5R21C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21)
      bflatExactSingletonBlocksJ5Seg3 =
      (12731551373771361133/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R21_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b83_c3]
  norm_num

theorem bflatExactChargeJ5R21C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R21)
      bflatExactSingletonBlocksJ5Seg4 =
      (1851786517967914033/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R21_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b83_c4]
  norm_num

end ASDExplicitGamma.Model
