module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b93_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (19955266081641019877473/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2059721749340936983131/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2450828315697409097/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3516935246597855689/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1732684983001489/62500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1227849691719444043491/125000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (813330502783639985199/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (24301900019964867081/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3494726596451924597/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (275766808007547329/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (96720262719514206488083/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (8030074733384369783111/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6024787046940299673/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3472900815081743459/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (274330558692733207/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (47625819950889985396769/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (123892414166195790373/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (23899897072152155027/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (345144225538203069/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (272919686188139671/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (46910305833082698504379/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7830344960751044021801/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11852008874468973939/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (107197980200726133/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (135766515310090251/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (46212869850431249158883/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (193342225667085981149/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (23511383437848678201/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (681912953024706681/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (16885590067433579/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (91065641925800967456399/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7639072032435070824561/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (583046748350190459/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3389115301809552601/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (268827780860619321/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (11217373960377879348171/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1509284353053868660723/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11567677996034796451/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2105607574823749/6250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (133753466131690613/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (88444516803801617262989/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1863917129473132722027/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (22951723664341466743/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1674560354259667739/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (133102900469660639/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (21795249640999133733033/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (736674511960035740969/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (22770858594350797371/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3329546951971774263/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (52984663961535863/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (4297363526944096338343/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7279586953391207137509/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11296325133735521491/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1655118584919431831/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (52731690507262731/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (42371108684193164403801/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (224816623751311299479/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (350265503442762781/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3291178154226968731/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (262410196600451647/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (10445596680421264263389/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7110320630133491790471/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11121891105445724039/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (818089300129960469/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (261177585929480823/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r104_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (72174233732250482059619/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r104_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (6154027766785202758401/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r104_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (19323072948637115057/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r104_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1424025676101840311/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b93_r104_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B93.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (227530853983757177/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b93_c0 :
    bflatChargeRowsFor (bflatBlockJ5B93.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1259081203793593701652871/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B93.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 111 := by decide +kernel
  have hnil : rows.drop 112 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (19955266081641019877473/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b93_r000_c0]
    _ = (39600861149152124573329/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r008_c0,
        List.drop_drop]
      ring
    _ = (36840571058159353669341/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r016_c0,
        List.drop_drop]
      ring
    _ = (194988104183527400074133/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r024_c0,
        List.drop_drop]
      ring
    _ = (15118650626038131161157/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r032_c0,
        List.drop_drop]
      ring
    _ = (57622255973408269547479/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r040_c0,
        List.drop_drop]
      ring
    _ = (667288201659883662931189/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r048_c0,
        List.drop_drop]
      ring
    _ = (757027193342906697716557/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r056_c0,
        List.drop_drop]
      ring
    _ = (422735855073354157489773/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r064_c0,
        List.drop_drop]
      ring
    _ = (466326354355352424955839/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r072_c0,
        List.drop_drop]
      ring
    _ = (509299989624793388339269/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r080_c0,
        List.drop_drop]
      ring
    _ = (55167109830898655274307/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r088_c0,
        List.drop_drop]
      ring
    _ = (296726742515335804898313/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r096_c0,
        List.drop_drop]
      ring
    _ = (1259081203793593701652871/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b93_r104_c0,
        List.drop_drop]
      ring
    _ = (1259081203793593701652871/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b93_c1 :
    bflatChargeRowsFor (bflatBlockJ5B93.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (105641389998204697114941/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B93.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 111 := by decide +kernel
  have hnil : rows.drop 112 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (2059721749340936983131/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b93_r000_c1]
    _ = (8186096012600073892257/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r008_c1,
        List.drop_drop]
      ring
    _ = (195218134068676140541/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r016_c1,
        List.drop_drop]
      ring
    _ = (32331381265221048151497/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r024_c1,
        List.drop_drop]
      ring
    _ = (20080863112986046086649/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r032_c1,
        List.drop_drop]
      ring
    _ = (23947707626327765709629/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r040_c1,
        List.drop_drop]
      ring
    _ = (55534487285090602243819/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r048_c1,
        List.drop_drop]
      ring
    _ = (31540454525179972773717/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r056_c1,
        List.drop_drop]
      ring
    _ = (35268288784126238217771/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r064_c1,
        List.drop_drop]
      ring
    _ = (4868957667990802115327/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r072_c1,
        List.drop_drop]
      ring
    _ = (85182909641244040982741/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r080_c1,
        List.drop_drop]
      ring
    _ = (92377041601286002566069/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r088_c1,
        List.drop_drop]
      ring
    _ = (4974368111570974717827/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r096_c1,
        List.drop_drop]
      ring
    _ = (105641389998204697114941/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b93_r104_c1,
        List.drop_drop]
      ring
    _ = (105641389998204697114941/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b93_c2 :
    bflatChargeRowsFor (bflatBlockJ5B93.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (161390467727872418663/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B93.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 111 := by decide +kernel
  have hnil : rows.drop 112 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (2450828315697409097/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b93_r000_c2]
    _ = (48810183176938958051/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r008_c2,
        List.drop_drop]
      ring
    _ = (72909331364700156743/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r016_c2,
        List.drop_drop]
      ring
    _ = (9680922843685231177/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r024_c2,
        List.drop_drop]
      ring
    _ = (1883019471652972807/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r032_c2,
        List.drop_drop]
      ring
    _ = (144024629623638937849/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r040_c2,
        List.drop_drop]
      ring
    _ = (167346499557646556209/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r048_c2,
        List.drop_drop]
      ring
    _ = (190481855549716149111/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r056_c2,
        List.drop_drop]
      ring
    _ = (106716789607028807927/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r064_c2,
        List.drop_drop]
      ring
    _ = (9448177512336336529/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r072_c2,
        List.drop_drop]
      ring
    _ = (258797088075879456207/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r080_c2,
        List.drop_drop]
      ring
    _ = (281214080296216274191/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r088_c2,
        List.drop_drop]
      ring
    _ = (303457862507107722269/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r096_c2,
        List.drop_drop]
      ring
    _ = (161390467727872418663/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b93_r104_c2,
        List.drop_drop]
      ring
    _ = (161390467727872418663/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b93_c3 :
    bflatChargeRowsFor (bflatBlockJ5B93.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (46934484003868339729/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B93.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 111 := by decide +kernel
  have hnil : rows.drop 112 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (3516935246597855689/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b93_r000_c3]
    _ = (3505830921524890143/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r008_c3,
        List.drop_drop]
      ring
    _ = (2096912531626304749/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r016_c3,
        List.drop_drop]
      ring
    _ = (2787200982702710887/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r024_c3,
        List.drop_drop]
      ring
    _ = (17366340279936790691/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r032_c3,
        List.drop_drop]
      ring
    _ = (81155879082266891/39062500000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r040_c3,
        List.drop_drop]
      ring
    _ = (24165020346869876697/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r048_c3,
        List.drop_drop]
      ring
    _ = (27533992466587875097/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r056_c3,
        List.drop_drop]
      ring
    _ = (1235324527004288423/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r064_c3,
        List.drop_drop]
      ring
    _ = (17106330063539492419/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r072_c3,
        List.drop_drop]
      ring
    _ = (75045794593835697/20000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r080_c3,
        List.drop_drop]
      ring
    _ = (40814075451144817231/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r088_c3,
        List.drop_drop]
      ring
    _ = (44086432651664659107/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r096_c3,
        List.drop_drop]
      ring
    _ = (46934484003868339729/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b93_r104_c3,
        List.drop_drop]
      ring
    _ = (46934484003868339729/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b93_c4 :
    bflatChargeRowsFor (bflatBlockJ5B93.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (744838008957756131/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B93.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 111 := by decide +kernel
  have hnil : rows.drop 112 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (1732684983001489/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b93_r000_c4]
    _ = (552996405287785569/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r008_c4,
        List.drop_drop]
      ring
    _ = (103415870497564847/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r016_c4,
        List.drop_drop]
      ring
    _ = (1100246650168658447/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r024_c4,
        List.drop_drop]
      ring
    _ = (1371779680788838949/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r032_c4,
        List.drop_drop]
      ring
    _ = (1641949121867776213/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r040_c4,
        List.drop_drop]
      ring
    _ = (955388451364197767/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r048_c4,
        List.drop_drop]
      ring
    _ = (54457095874794419/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r056_c4,
        List.drop_drop]
      ring
    _ = (1222244817965549019/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r064_c4,
        List.drop_drop]
      ring
    _ = (2709412955738777353/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r072_c4,
        List.drop_drop]
      ring
    _ = (46454240754298297/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r080_c4,
        List.drop_drop]
      ring
    _ = (647096320975108531/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r088_c4,
        List.drop_drop]
      ring
    _ = (1748329595402511739/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r096_c4,
        List.drop_drop]
      ring
    _ = (744838008957756131/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b93_r104_c4,
        List.drop_drop]
      ring
    _ = (744838008957756131/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R31C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31)
      bflatExactSingletonBlocksJ5Seg0 =
      (1259081203793593701652871/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R31_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b93_c0]
  norm_num

theorem bflatExactChargeJ5R31C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31)
      bflatExactSingletonBlocksJ5Seg1 =
      (105641389998204697114941/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R31_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b93_c1]
  norm_num

theorem bflatExactChargeJ5R31C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31)
      bflatExactSingletonBlocksJ5Seg2 =
      (161390467727872418663/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R31_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b93_c2]
  norm_num

theorem bflatExactChargeJ5R31C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31)
      bflatExactSingletonBlocksJ5Seg3 =
      (46934484003868339729/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R31_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b93_c3]
  norm_num

theorem bflatExactChargeJ5R31C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R31)
      bflatExactSingletonBlocksJ5Seg4 =
      (744838008957756131/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R31_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b93_c4]
  norm_num

end ASDExplicitGamma.Model
