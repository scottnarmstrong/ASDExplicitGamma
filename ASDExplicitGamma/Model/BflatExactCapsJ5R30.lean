module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b92_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (30891240773597470554423/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (9811117980443425019393/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3435031988628169911/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3836480484869949247/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (298435123182148741/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (60673003131020879575353/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4834084228419508742661/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (27217156991247712227/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (952050525410022543/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (148273752692073473/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (59596074049750308116741/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4764358299446565172711/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (26959197958038160727/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1890236298765855553/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (147349157565987247/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (58550573520252222964829/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (9392670162059098490681/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (66765723582728821/25000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1876641868951763697/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (18305438200032643/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (57535403935792953627031/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (9259935976911788657681/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1653645836368563629/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (465828248578028901/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (145556474759597999/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (113098984101755196967393/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1826084069086034836397/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (26215224200088427099/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3700488654549953969/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (144687696705437281/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (6948973752187498158593/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1125503676259296024253/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1623553110057160071/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3674860014376886093/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (143836761808156939/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (109322552556338446057617/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1776133899200672306217/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (5148618483883120637/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3649727451434109187/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (8937701502132441/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (21502782528508569308001/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8760247426869921925279/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (25513829971242683299/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1812538790012225629/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (284373211382361299/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (21151145321795497354029/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8642670814712087247493/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (25288936564400981551/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3600896366963912477/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (70693201008904573/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (26011529276067729570557/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8527848324536581879487/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2506828356253025853/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1788584624006360881/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (56240834240987229/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (6398953991547811826971/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2103922478564586890469/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (12425870179329673913/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (888470309733287321/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (2796662212429307/100000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (63165186212787288398899/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1040799759896904268443/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15424147450193828123/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1104769395584372629/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b92_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B92.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (17402358109593061/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b92_c0 :
    bflatChargeRowsFor (bflatBlockJ5B92.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1412744395494459753570911/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B92.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 101 := by decide +kernel
  have hnil : rows.drop 104 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (30891240773597470554423/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b92_r000_c0]
    _ = (122455484678215820684199/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r008_c0,
        List.drop_drop]
      ring
    _ = (9102577936398306440047/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r016_c0,
        List.drop_drop]
      ring
    _ = (240602132248218351765769/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r024_c0,
        List.drop_drop]
      ring
    _ = (372671920230014131741/6250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r032_c0,
        List.drop_drop]
      ring
    _ = (709374056469777807752993/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r040_c0,
        List.drop_drop]
      ring
    _ = (820557636504777778290481/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r048_c0,
        List.drop_drop]
      ring
    _ = (464940094530558112174049/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r056_c0,
        List.drop_drop]
      ring
    _ = (1037394101703659070888103/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r064_c0,
        List.drop_drop]
      ring
    _ = (142893728539079569707281/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r072_c0,
        List.drop_drop]
      ring
    _ = (311798986354226868985119/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r080_c0,
        List.drop_drop]
      ring
    _ = (337394802320418116293003/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r088_c0,
        List.drop_drop]
      ring
    _ = (1412744395494459753570911/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b92_r096_c0,
        List.drop_drop]
      ring
    _ = (1412744395494459753570911/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b92_c1 :
    bflatChargeRowsFor (bflatBlockJ5B92.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (114226183706515823861943/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B92.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 101 := by decide +kernel
  have hnil : rows.drop 104 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (9811117980443425019393/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b92_r000_c1]
    _ = (3895857287456488500943/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r008_c1,
        List.drop_drop]
      ring
    _ = (29008003036175572850137/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r016_c1,
        List.drop_drop]
      ring
    _ = (19200336599117335670409/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r024_c1,
        List.drop_drop]
      ring
    _ = (47660609175146459998499/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r032_c1,
        List.drop_drop]
      ring
    _ = (14197757380144158545121/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r040_c1,
        List.drop_drop]
      ring
    _ = (16448764732662750593627/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r048_c1,
        List.drop_drop]
      ring
    _ = (74675728426654363905593/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r056_c1,
        List.drop_drop]
      ring
    _ = (10429496981690535728859/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r064_c1,
        List.drop_drop]
      ring
    _ = (18415729333647274615673/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r072_c1,
        List.drop_drop]
      ring
    _ = (25151623748193238739463/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r080_c1,
        List.drop_drop]
      ring
    _ = (6813886556689456407483/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r088_c1,
        List.drop_drop]
      ring
    _ = (114226183706515823861943/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b92_r096_c1,
        List.drop_drop]
      ring
    _ = (114226183706515823861943/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b92_c2 :
    bflatChargeRowsFor (bflatBlockJ5B92.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (65780667592149093891/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B92.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 101 := by decide +kernel
  have hnil : rows.drop 104 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (3435031988628169911/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b92_r000_c2]
    _ = (10939482580054614303/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r008_c2,
        List.drop_drop]
      ring
    _ = (40828305429155616121/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r016_c2,
        List.drop_drop]
      ring
    _ = (54181450145701380321/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r024_c2,
        List.drop_drop]
      ring
    _ = (67410616836649889353/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r032_c2,
        List.drop_drop]
      ring
    _ = (32207291574677641161/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r040_c2,
        List.drop_drop]
      ring
    _ = (187013307634302766941/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r048_c2,
        List.drop_drop]
      ring
    _ = (106378200026859185063/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r056_c2,
        List.drop_drop]
      ring
    _ = (9530809200998442137/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r064_c2,
        List.drop_drop]
      ring
    _ = (8236223955917563593/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r072_c2,
        List.drop_drop]
      ring
    _ = (144313725075946146753/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r080_c2,
        List.drop_drop]
      ring
    _ = (78369797627637910333/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r088_c2,
        List.drop_drop]
      ring
    _ = (65780667592149093891/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b92_r096_c2,
        List.drop_drop]
      ring
    _ = (65780667592149093891/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b92_c3 :
    bflatChargeRowsFor (bflatBlockJ5B92.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (9299340851206687683/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B92.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 101 := by decide +kernel
  have hnil : rows.drop 104 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (3836480484869949247/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b92_r000_c3]
    _ = (7644682586510039419/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r008_c3,
        List.drop_drop]
      ring
    _ = (457006207361670021/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r016_c3,
        List.drop_drop]
      ring
    _ = (15178438921945277919/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r024_c3,
        List.drop_drop]
      ring
    _ = (18905064910569509127/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r032_c3,
        List.drop_drop]
      ring
    _ = (2825694195639932887/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r040_c3,
        List.drop_drop]
      ring
    _ = (26280413579496349189/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r048_c3,
        List.drop_drop]
      ring
    _ = (3741267628866307297/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r056_c3,
        List.drop_drop]
      ring
    _ = (16777609305477454817/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r064_c3,
        List.drop_drop]
      ring
    _ = (37156114977918822111/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r072_c3,
        List.drop_drop]
      ring
    _ = (40733284225931543873/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r080_c3,
        List.drop_drop]
      ring
    _ = (44287165464864693157/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r088_c3,
        List.drop_drop]
      ring
    _ = (9299340851206687683/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b92_r096_c3,
        List.drop_drop]
      ring
    _ = (9299340851206687683/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b92_c4 :
    bflatChargeRowsFor (bflatBlockJ5B92.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (727755251695038413/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B92.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 101 := by decide +kernel
  have hnil : rows.drop 104 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (298435123182148741/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b92_r000_c4]
    _ = (594982628566295687/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r008_c4,
        List.drop_drop]
      ring
    _ = (889680943698270181/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r016_c4,
        List.drop_drop]
      ring
    _ = (1182567954898792469/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r024_c4,
        List.drop_drop]
      ring
    _ = (1473680904417988467/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r032_c4,
        List.drop_drop]
      ring
    _ = (1763056297828863029/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r040_c4,
        List.drop_drop]
      ring
    _ = (2050729821445176907/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r048_c4,
        List.drop_drop]
      ring
    _ = (2336736269513415019/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r056_c4,
        List.drop_drop]
      ring
    _ = (1310554740447888159/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r064_c4,
        List.drop_drop]
      ring
    _ = (290388228493139461/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r072_c4,
        List.drop_drop]
      ring
    _ = (637017291227266151/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r080_c4,
        List.drop_drop]
      ring
    _ = (692950535475852291/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r088_c4,
        List.drop_drop]
      ring
    _ = (727755251695038413/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b92_r096_c4,
        List.drop_drop]
      ring
    _ = (727755251695038413/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R30C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30)
      bflatExactSingletonBlocksJ5Seg0 =
      (1412744395494459753570911/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R30_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b92_c0]
  norm_num

theorem bflatExactChargeJ5R30C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30)
      bflatExactSingletonBlocksJ5Seg1 =
      (114226183706515823861943/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R30_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b92_c1]
  norm_num

theorem bflatExactChargeJ5R30C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30)
      bflatExactSingletonBlocksJ5Seg2 =
      (65780667592149093891/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R30_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b92_c2]
  norm_num

theorem bflatExactChargeJ5R30C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30)
      bflatExactSingletonBlocksJ5Seg3 =
      (9299340851206687683/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R30_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b92_c3]
  norm_num

theorem bflatExactChargeJ5R30C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R30)
      bflatExactSingletonBlocksJ5Seg4 =
      (727755251695038413/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R30_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b92_c4]
  norm_num

end ASDExplicitGamma.Model
