module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b91_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (77264732037347005186239/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5866734187616144318599/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (30889795796583073069/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (840349219503456807/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (322920876223022221/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (151389720951146674688051/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (721533066290032382223/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (30565356123455975103/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (104178854849635003/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (160299030897592359/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (74171518677722929088437/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2839980375096403710507/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (236297455525979069/78125000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4133065421738359831/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (159154550874652349/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (72693457887738071326001/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2235920274943208507309/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (29932047840337493541/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2049748478398993703/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (79013847724369803/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (5700754144331544296941/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (11003516946082236883973/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (7405837826997177251/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (813292602181393523/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (313838102803257857/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (139736349533526117066233/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1083160975564732513409/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1832502353563658637/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (403397496753963171/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (311658199057711479/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (137036909510691704988677/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3412420895162511273/3200000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14511069738024002293/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (500255190257306811/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (309516438934108627/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (67209026201426095578939/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10500063668556052102001/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (28729670282499716551/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3970668825174311063/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (61482677871928467/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (131877315230335183366989/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10340280195583300078099/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (28442625809647854717/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3939860628892257491/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (305349435143872931/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (25882451611779617323283/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10184386034386194800931/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (7040246321992794301/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1954809217075688249/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (303324789405024501/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (127020468527723495401887/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10032298744543126905607/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (174279454470754343/62500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (969985409849220131/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (301339504136986173/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (62635557430200716795031/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4960282982458468455609/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13840418317170733423/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1929018060830412139/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b91_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B91.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (4685548350245849/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b91_c0 :
    bflatChargeRowsFor (bflatBlockJ5B91.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (40107622561481969717651/250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B91.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 92 := by decide +kernel
  have hnil : rows.drop 96 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (77264732037347005186239/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b91_r000_c0]
    _ = (305919185025840685060529/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r008_c0,
        List.drop_drop]
      ring
    _ = (454262222381286543237403/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r016_c0,
        List.drop_drop]
      ring
    _ = (119929827631352537177881/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r024_c0,
        List.drop_drop]
      ring
    _ = (74216799176505129331293/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r032_c0,
        List.drop_drop]
      ring
    _ = (881904341298577410379163/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r040_c0,
        List.drop_drop]
      ring
    _ = (6368382817557931971049/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r048_c0,
        List.drop_drop]
      ring
    _ = (576679651606060653262859/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r056_c0,
        List.drop_drop]
      ring
    _ = (1285236618442456489892707/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r064_c0,
        List.drop_drop]
      ring
    _ = (707324438250677288254561/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r072_c0,
        List.drop_drop]
      ring
    _ = (1541669345029078071911009/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r080_c0,
        List.drop_drop]
      ring
    _ = (40107622561481969717651/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b91_r088_c0,
        List.drop_drop]
      ring
    _ = (40107622561481969717651/250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b91_c1 :
    bflatChargeRowsFor (bflatBlockJ5B91.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (62166886967807008109887/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B91.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 92 := by decide +kernel
  have hnil : rows.drop 96 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (5866734187616144318599/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b91_r000_c1]
    _ = (11638998717936403376383/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r008_c1,
        List.drop_drop]
      ring
    _ = (17318959468129210797397/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r016_c1,
        List.drop_drop]
      ring
    _ = (45817520310974464131339/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r024_c1,
        List.drop_drop]
      ring
    _ = (3551314828566043813457/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r032_c1,
        List.drop_drop]
      ring
    _ = (33826323506352013074701/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r040_c1,
        List.drop_drop]
      ring
    _ = (78316462310086873877527/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r048_c1,
        List.drop_drop]
      ring
    _ = (11102065747330365747441/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r056_c1,
        List.drop_drop]
      ring
    _ = (99156806174226226057627/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r064_c1,
        List.drop_drop]
      ring
    _ = (54670596104306210429279/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r072_c1,
        List.drop_drop]
      ring
    _ = (23874698190631109552833/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r080_c1,
        List.drop_drop]
      ring
    _ = (62166886967807008109887/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b91_r088_c1,
        List.drop_drop]
      ring
    _ = (62166886967807008109887/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b91_c2 :
    bflatChargeRowsFor (bflatBlockJ5B91.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (168328607460683645551/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B91.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 92 := by decide +kernel
  have hnil : rows.drop 96 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (30889795796583073069/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b91_r000_c2]
    _ = (15363787980009762043/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r008_c2,
        List.drop_drop]
      ring
    _ = (22925306556841092251/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r016_c2,
        List.drop_drop]
      ring
    _ = (24326654813540372509/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r024_c2,
        List.drop_drop]
      ring
    _ = (151256625375690571549/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r032_c2,
        List.drop_drop]
      ring
    _ = (180576663032709109741/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r040_c2,
        List.drop_drop]
      ring
    _ = (209598802508757114327/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r048_c2,
        List.drop_drop]
      ring
    _ = (119164236395628415439/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r056_c2,
        List.drop_drop]
      ring
    _ = (53354219720180937119/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r064_c2,
        List.drop_drop]
      ring
    _ = (294932083888875862799/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r072_c2,
        List.drop_drop]
      ring
    _ = (322816796604196557679/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r080_c2,
        List.drop_drop]
      ring
    _ = (168328607460683645551/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b91_r088_c2,
        List.drop_drop]
      ring
    _ = (168328607460683645551/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b91_c3 :
    bflatChargeRowsFor (bflatBlockJ5B91.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (1158326243974733073/250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B91.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 92 := by decide +kernel
  have hnil : rows.drop 96 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (840349219503456807/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b91_r000_c3]
    _ = (1673780058300536831/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r008_c3,
        List.drop_drop]
      ring
    _ = (6250982856620521993/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r016_c3,
        List.drop_drop]
      ring
    _ = (518795708438719731/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r024_c3,
        List.drop_drop]
      ring
    _ = (20667925680945999007/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r032_c3,
        List.drop_drop]
      ring
    _ = (24701900648485630717/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r040_c3,
        List.drop_drop]
      ring
    _ = (5740788434108817041/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r048_c3,
        List.drop_drop]
      ring
    _ = (8168652748929599067/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r056_c3,
        List.drop_drop]
      ring
    _ = (36614471624610653759/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r064_c3,
        List.drop_drop]
      ring
    _ = (40524090058762030257/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r072_c3,
        List.drop_drop]
      ring
    _ = (44404031698158910781/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r080_c3,
        List.drop_drop]
      ring
    _ = (1158326243974733073/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b91_r088_c3,
        List.drop_drop]
      ring
    _ = (1158326243974733073/250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b91_c4 :
    bflatChargeRowsFor (bflatBlockJ5B91.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (22376630229459137/62500000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B91.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 92 := by decide +kernel
  have hnil : rows.drop 96 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (322920876223022221/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b91_r000_c4]
    _ = (643518938018206939/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r008_c4,
        List.drop_drop]
      ring
    _ = (961828039767511637/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r016_c4,
        List.drop_drop]
      ring
    _ = (1277883430664990849/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r024_c4,
        List.drop_drop]
      ring
    _ = (795860766734124353/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r032_c4,
        List.drop_drop]
      ring
    _ = (380675946505192037/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r040_c4,
        List.drop_drop]
      ring
    _ = (553224042865017203/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r048_c4,
        List.drop_drop]
      ring
    _ = (2520309560819711147/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r056_c4,
        List.drop_drop]
      ring
    _ = (1412829497981792039/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r064_c4,
        List.drop_drop]
      ring
    _ = (3128983785368608579/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r072_c4,
        List.drop_drop]
      ring
    _ = (26799400699262459/78125000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r080_c4,
        List.drop_drop]
      ring
    _ = (22376630229459137/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b91_r088_c4,
        List.drop_drop]
      ring
    _ = (22376630229459137/62500000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R29C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29)
      bflatExactSingletonBlocksJ5Seg0 =
      (40107622561481969717651/250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R29_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b91_c0]
  norm_num

theorem bflatExactChargeJ5R29C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29)
      bflatExactSingletonBlocksJ5Seg1 =
      (62166886967807008109887/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R29_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b91_c1]
  norm_num

theorem bflatExactChargeJ5R29C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29)
      bflatExactSingletonBlocksJ5Seg2 =
      (168328607460683645551/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R29_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b91_c2]
  norm_num

theorem bflatExactChargeJ5R29C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29)
      bflatExactSingletonBlocksJ5Seg3 =
      (1158326243974733073/250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R29_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b91_c3]
  norm_num

theorem bflatExactChargeJ5R29C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R29)
      bflatExactSingletonBlocksJ5Seg4 =
      (22376630229459137/62500000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R29_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b91_c4]
  norm_num

end ASDExplicitGamma.Model
