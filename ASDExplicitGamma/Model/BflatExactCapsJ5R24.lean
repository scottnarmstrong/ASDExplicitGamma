module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b86_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (8062352359620927615373/200000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (698427021921697969921/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (43454616303731031361/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1336434636730462043/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (196820721517644689/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (395208540732355433781933/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (22161885957436301773147/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21719376034376663537/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2677771504816036301/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (197353575224687199/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (193674028993935603488493/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10981709662279314307531/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (43396868667360011379/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1072442077376163277/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (395545882625521763/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (379544259035833683143387/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (21755044373068258966529/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (43329897024590181121/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5365832061474802177/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (396163732675311287/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (371804738262258341496347/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5384382449413069738993/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21619398965166167157/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (536650387403453441/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (396567136015477123/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (364136604444239080414317/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4262326286457382735701/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (43124557778074107209/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1072865133272599593/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (198381419467118009/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (35654649051064765076047/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (21078090429079275694397/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21494092184880544207/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2679700412767580907/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (396757867045085297/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (44038760273737248115701/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (654497033366323885987/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (167589741832536767/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (334723077129081221/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b86_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B86.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (6198083839521669/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b86_c0 :
    bflatChargeRowsFor (bflatBlockJ5B86.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (2701745069227989025457791/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B86.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 57 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (8062352359620927615373/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b86_r000_c0]
    _ = (798326158713401814550583/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r008_c0,
        List.drop_drop]
      ring
    _ = (1185674216701273021527569/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r016_c0,
        List.drop_drop]
      ring
    _ = (391304618934276676167739/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r024_c0,
        List.drop_drop]
      ring
    _ = (1937023213999365046167303/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r032_c0,
        List.drop_drop]
      ring
    _ = (115057990922180206329081/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r040_c0,
        List.drop_drop]
      ring
    _ = (265770630895425177734209/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r048_c0,
        List.drop_drop]
      ring
    _ = (2701745069227989025457791/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b86_r056_c0,
        List.drop_drop]
      ring
    _ = (2701745069227989025457791/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b86_c1 :
    bflatChargeRowsFor (bflatBlockJ5B86.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (19346906768630161033129/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B86.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 57 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (698427021921697969921/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b86_r000_c1]
    _ = (44511550658930636810619/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r008_c1,
        List.drop_drop]
      ring
    _ = (66474969983489265425681/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r016_c1,
        List.drop_drop]
      ring
    _ = (8823001435655752439221/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r024_c1,
        List.drop_drop]
      ring
    _ = (54883772077104901674091/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r032_c1,
        List.drop_drop]
      ring
    _ = (131079175586496717026687/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r040_c1,
        List.drop_drop]
      ring
    _ = (38039316503893998180271/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r048_c1,
        List.drop_drop]
      ring
    _ = (19346906768630161033129/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b86_r056_c1,
        List.drop_drop]
      ring
    _ = (19346906768630161033129/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b86_c2 :
    bflatChargeRowsFor (bflatBlockJ5B86.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (38541818235155407177/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B86.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 57 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (43454616303731031361/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b86_r000_c2]
    _ = (17378673674496871687/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r008_c2,
        List.drop_drop]
      ring
    _ = (65145118519922184907/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r016_c2,
        List.drop_drop]
      ring
    _ = (34724026812886910187/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r024_c2,
        List.drop_drop]
      ring
    _ = (216858931994766885249/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r032_c2,
        List.drop_drop]
      ring
    _ = (129991744886420496229/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r040_c2,
        List.drop_drop]
      ring
    _ = (37871459267825260109/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r048_c2,
        List.drop_drop]
      ring
    _ = (38541818235155407177/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b86_r056_c2,
        List.drop_drop]
      ring
    _ = (38541818235155407177/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b86_c3 :
    bflatChargeRowsFor (bflatBlockJ5B86.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (38189000525100395967/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B86.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 57 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1336434636730462043/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b86_r000_c3]
    _ = (5350640778276960387/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r008_c3,
        List.drop_drop]
      ring
    _ = (16063491943434737159/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r016_c3,
        List.drop_drop]
      ring
    _ = (2678665500613692417/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r024_c3,
        List.drop_drop]
      ring
    _ = (13397913939472036873/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r032_c3,
        List.drop_drop]
      ring
    _ = (32160153545307071711/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r040_c3,
        List.drop_drop]
      ring
    _ = (1500782174833689341/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r048_c3,
        List.drop_drop]
      ring
    _ = (38189000525100395967/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b86_r056_c3,
        List.drop_drop]
      ring
    _ = (38189000525100395967/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b86_c4 :
    bflatChargeRowsFor (bflatBlockJ5B86.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (352466340187058577/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B86.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 57 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (196820721517644689/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b86_r000_c4]
    _ = (24635893546395743/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r008_c4,
        List.drop_drop]
      ring
    _ = (1183894476110185539/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r016_c4,
        List.drop_drop]
      ring
    _ = (790029104392748413/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r024_c4,
        List.drop_drop]
      ring
    _ = (1976625344800973949/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r032_c4,
        List.drop_drop]
      ring
    _ = (2373388183735209967/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r040_c4,
        List.drop_drop]
      ring
    _ = (86567064086884227/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r048_c4,
        List.drop_drop]
      ring
    _ = (352466340187058577/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b86_r056_c4,
        List.drop_drop]
      ring
    _ = (352466340187058577/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R24C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24)
      bflatExactSingletonBlocksJ5Seg0 =
      (2701745069227989025457791/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R24_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b86_c0]
  norm_num

theorem bflatExactChargeJ5R24C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24)
      bflatExactSingletonBlocksJ5Seg1 =
      (19346906768630161033129/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R24_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b86_c1]
  norm_num

theorem bflatExactChargeJ5R24C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24)
      bflatExactSingletonBlocksJ5Seg2 =
      (38541818235155407177/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R24_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b86_c2]
  norm_num

theorem bflatExactChargeJ5R24C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24)
      bflatExactSingletonBlocksJ5Seg3 =
      (38189000525100395967/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R24_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b86_c3]
  norm_num

theorem bflatExactChargeJ5R24C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R24)
      bflatExactSingletonBlocksJ5Seg4 =
      (352466340187058577/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R24_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b86_c4]
  norm_num

end ASDExplicitGamma.Model
