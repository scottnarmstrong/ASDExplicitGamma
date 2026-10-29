module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b88_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (292619036509370367756771/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3749090632930695942533/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10234150533438258273/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2604859576708901313/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (388940103208173993/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (28607702183276460681751/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (18472028572258193817117/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8127247475463170793/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1036695660321937537/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (387354074942170093/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (27965775895468764715933/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (71085069542404567269/39062500000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (40325145018283921731/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1288934366679685517/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (77130863268975181/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (273363063725639732582047/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (17923178416715077824791/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10001076070372855447/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5126609527347631033/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (95962216120176473/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (66798608163691049176629/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3529736546725145201881/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (19837336400796427367/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (159256430134428531/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (381945667255982729/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (130576528099050670853199/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4343679462586766294881/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (19668592242166469823/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4945933171943847/9765625000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (379952561504050911/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (255239832078904373549463/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (17101685747905884860689/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (38992747554565675771/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5032006165177465019/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (47234656540418969/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (249455378611994808515637/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3365992696565193198131/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (38642242791119969879/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2499211181907097167/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (375727293707863823/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (76514780419703698727223/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10381467863578721330371/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (23971058781309872399/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (776644212673050171/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b88_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B88.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (116853796254956811/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b88_c0 :
    bflatChargeRowsFor (bflatBlockJ5B88.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1158894570702817236124059/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B88.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 69 := by decide +kernel
  have hnil : rows.drop 72 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (292619036509370367756771/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b88_r000_c0]
    _ = (578696058342134974574281/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r008_c0,
        List.drop_drop]
      ring
    _ = (858353817296822621733611/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r016_c0,
        List.drop_drop]
      ring
    _ = (565858440511231177157829/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r024_c0,
        List.drop_drop]
      ring
    _ = (699455656838613275511087/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r032_c0,
        List.drop_drop]
      ring
    _ = (415016092468831973182143/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r040_c0,
        List.drop_drop]
      ring
    _ = (383060840390846453255607/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r048_c0,
        List.drop_drop]
      ring
    _ = (270594947570778384349209/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r056_c0,
        List.drop_drop]
      ring
    _ = (1158894570702817236124059/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b88_r064_c0,
        List.drop_drop]
      ring
    _ = (1158894570702817236124059/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b88_c1 :
    bflatChargeRowsFor (bflatBlockJ5B88.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (152674955634765683946081/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B88.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 69 := by decide +kernel
  have hnil : rows.drop 72 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (3749090632930695942533/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b88_r000_c1]
    _ = (18608740868455836764891/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r008_c1,
        List.drop_drop]
      ring
    _ = (27707629769883621375323/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r016_c1,
        List.drop_drop]
      ring
    _ = (73338437956482320575437/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r024_c1,
        List.drop_drop]
      ring
    _ = (45493560345054023292421/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r032_c1,
        List.drop_drop]
      ring
    _ = (54180919270227555882183/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r040_c1,
        List.drop_drop]
      ring
    _ = (25092704857672199325011/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r048_c1,
        List.drop_drop]
      ring
    _ = (14229348777118696261571/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r056_c1,
        List.drop_drop]
      ring
    _ = (152674955634765683946081/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b88_r064_c1,
        List.drop_drop]
      ring
    _ = (152674955634765683946081/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b88_c2 :
    bflatChargeRowsFor (bflatBlockJ5B88.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (68504039044753108601/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B88.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 69 := by decide +kernel
  have hnil : rows.drop 72 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (10234150533438258273/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b88_r000_c2]
    _ = (81572839511068887057/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r008_c2,
        List.drop_drop]
      ring
    _ = (30474496132338202197/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r016_c2,
        List.drop_drop]
      ring
    _ = (10118893050677764411/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r024_c2,
        List.drop_drop]
      ring
    _ = (20157696161243708531/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r032_c2,
        List.drop_drop]
      ring
    _ = (60228536524192506239/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r040_c2,
        List.drop_drop]
      ring
    _ = (279906893651335700727/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r048_c2,
        List.drop_drop]
      ring
    _ = (159274568221227835303/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r056_c2,
        List.drop_drop]
      ring
    _ = (68504039044753108601/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b88_r064_c2,
        List.drop_drop]
      ring
    _ = (68504039044753108601/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b88_c3 :
    bflatChargeRowsFor (bflatBlockJ5B88.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (43973391161149935769/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B88.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 69 := by decide +kernel
  have hnil : rows.drop 72 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (2604859576708901313/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b88_r000_c3]
    _ = (10393197455027490311/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r008_c3,
        List.drop_drop]
      ring
    _ = (15548934921746232379/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r016_c3,
        List.drop_drop]
      ring
    _ = (5168886112273465853/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r024_c3,
        List.drop_drop]
      ring
    _ = (6442937553348894101/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r032_c3,
        List.drop_drop]
      ring
    _ = (7709096445366518933/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r040_c3,
        List.drop_drop]
      ring
    _ = (35868391946643540751/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r048_c3,
        List.drop_drop]
      ring
    _ = (8173362862091547017/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r056_c3,
        List.drop_drop]
      ring
    _ = (43973391161149935769/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b88_r064_c3,
        List.drop_drop]
      ring
    _ = (43973391161149935769/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b88_c4 :
    bflatChargeRowsFor (bflatBlockJ5B88.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (41187596578463609/125000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B88.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 69 := by decide +kernel
  have hnil : rows.drop 72 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (388940103208173993/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b88_r000_c4]
    _ = (388147089075172043/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r008_c4,
        List.drop_drop]
      ring
    _ = (1161948494495219991/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r016_c4,
        List.drop_drop]
      ring
    _ = (1545797358975925883/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r024_c4,
        List.drop_drop]
      ring
    _ = (481935756557977153/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r032_c4,
        List.drop_drop]
      ring
    _ = (2307695587735959523/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r040_c4,
        List.drop_drop]
      ring
    _ = (107422913602372451/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r048_c4,
        List.drop_drop]
      ring
    _ = (1530650066883587549/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r056_c4,
        List.drop_drop]
      ring
    _ = (41187596578463609/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b88_r064_c4,
        List.drop_drop]
      ring
    _ = (41187596578463609/125000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R26C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26)
      bflatExactSingletonBlocksJ5Seg0 =
      (1158894570702817236124059/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R26_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b88_c0]
  norm_num

theorem bflatExactChargeJ5R26C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26)
      bflatExactSingletonBlocksJ5Seg1 =
      (152674955634765683946081/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R26_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b88_c1]
  norm_num

theorem bflatExactChargeJ5R26C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26)
      bflatExactSingletonBlocksJ5Seg2 =
      (68504039044753108601/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R26_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b88_c2]
  norm_num

theorem bflatExactChargeJ5R26C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26)
      bflatExactSingletonBlocksJ5Seg3 =
      (43973391161149935769/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R26_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b88_c3]
  norm_num

theorem bflatExactChargeJ5R26C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R26)
      bflatExactSingletonBlocksJ5Seg4 =
      (41187596578463609/125000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R26_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b88_c4]
  norm_num

end ASDExplicitGamma.Model
