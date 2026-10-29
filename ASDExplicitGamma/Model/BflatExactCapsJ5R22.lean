module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b84_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (501013207775265762981129/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (23475532676619340142499/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (20597794460830294859/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4937563733302726883/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (89981278241208157/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (98675989816506774924431/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (11742492596875056541497/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (20780167406609368367/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4991312900578674777/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (182061364726821307/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (60706421680297441365199/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (11737121940017070286791/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8378343266326378417/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5041335513609815393/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (368057922960632959/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (59730280145965401866281/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4688798561595376205729/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21094971467400321871/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2543816345423772373/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (371730198009206389/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (58745843850025220671391/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (23394943313149844734723/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (42455304992103906557/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5130214939838611709/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (375139727886515021/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (202359387321714941613781/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4083224106668899582009/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (37340514424597080281/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2260481575616057569/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b84_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B84.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (165419102039191291/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b84_c0 :
    bflatChargeRowsFor (bflatBlockJ5B84.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1416286148455767016026907/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B84.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 47 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (501013207775265762981129/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b84_r000_c0]
    _ = (248598289214449909400821/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b84_r008_c0,
        List.drop_drop]
      ring
    _ = (370011132575044792131219/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b84_r016_c0,
        List.drop_drop]
      ring
    _ = (489471692866975595863781/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b84_r024_c0,
        List.drop_drop]
      ring
    _ = (606963380567026037206563/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b84_r032_c0,
        List.drop_drop]
      ring
    _ = (1416286148455767016026907/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b84_r040_c0,
        List.drop_drop]
      ring
    _ = (1416286148455767016026907/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b84_c1 :
    bflatChargeRowsFor (bflatBlockJ5B84.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (17211227300609352184061/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B84.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 47 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (23475532676619340142499/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b84_r000_c1]
    _ = (46960517870369453225493/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b84_r008_c1,
        List.drop_drop]
      ring
    _ = (2817390470016143751963/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b84_r016_c1,
        List.drop_drop]
      ring
    _ = (2346968863959511870693/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b84_r024_c1,
        List.drop_drop]
      ring
    _ = (117273697871530319562443/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b84_r032_c1,
        List.drop_drop]
      ring
    _ = (17211227300609352184061/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b84_r040_c1,
        List.drop_drop]
      ring
    _ = (17211227300609352184061/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b84_c2 :
    bflatChargeRowsFor (bflatBlockJ5B84.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (246633402418012849117/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B84.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 47 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (20597794460830294859/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b84_r000_c2]
    _ = (20688980933719831613/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b84_r008_c2,
        List.drop_drop]
      ring
    _ = (124647640066511218537/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b84_r016_c2,
        List.drop_drop]
      ring
    _ = (166837583001311862279/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b84_r024_c2,
        List.drop_drop]
      ring
    _ = (52323221998353942209/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b84_r032_c2,
        List.drop_drop]
      ring
    _ = (246633402418012849117/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b84_r040_c2,
        List.drop_drop]
      ring
    _ = (246633402418012849117/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b84_c3 :
    bflatChargeRowsFor (bflatBlockJ5B84.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (14854511464704744323/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B84.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 47 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (4937563733302726883/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b84_r000_c3]
    _ = (496443831694070083/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b84_r008_c3,
        List.drop_drop]
      ring
    _ = (14970212147491217053/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b84_r016_c3,
        List.drop_drop]
      ring
    _ = (20057844838338761799/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b84_r024_c3,
        List.drop_drop]
      ring
    _ = (6297014944544343377/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b84_r032_c3,
        List.drop_drop]
      ring
    _ = (14854511464704744323/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b84_r040_c3,
        List.drop_drop]
      ring
    _ = (14854511464704744323/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b84_c4 :
    bflatChargeRowsFor (bflatBlockJ5B84.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (2169813895353212193/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B84.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 47 := by decide +kernel
  have hnil : rows.drop 48 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (89981278241208157/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b84_r000_c4]
    _ = (362023921209237621/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b84_r008_c4,
        List.drop_drop]
      ring
    _ = (1092105765379108201/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b84_r016_c4,
        List.drop_drop]
      ring
    _ = (146383596338831459/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b84_r024_c4,
        List.drop_drop]
      ring
    _ = (1838975691274829611/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b84_r032_c4,
        List.drop_drop]
      ring
    _ = (2169813895353212193/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b84_r040_c4,
        List.drop_drop]
      ring
    _ = (2169813895353212193/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R22C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22)
      bflatExactSingletonBlocksJ5Seg0 =
      (1416286148455767016026907/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R22_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b84_c0]
  norm_num

theorem bflatExactChargeJ5R22C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22)
      bflatExactSingletonBlocksJ5Seg1 =
      (17211227300609352184061/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R22_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b84_c1]
  norm_num

theorem bflatExactChargeJ5R22C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22)
      bflatExactSingletonBlocksJ5Seg2 =
      (246633402418012849117/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R22_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b84_c2]
  norm_num

theorem bflatExactChargeJ5R22C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22)
      bflatExactSingletonBlocksJ5Seg3 =
      (14854511464704744323/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R22_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b84_c3]
  norm_num

theorem bflatExactChargeJ5R22C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R22)
      bflatExactSingletonBlocksJ5Seg4 =
      (2169813895353212193/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R22_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b84_c4]
  norm_num

end ASDExplicitGamma.Model
