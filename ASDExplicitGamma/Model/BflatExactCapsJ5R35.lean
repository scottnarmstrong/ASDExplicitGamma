module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b97_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (45112725321710481372647/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4163141330434711256107/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15281183549713092537/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1232772684641043131/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (206879043962162991/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (44662116185184181603151/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (515726636714782464401/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15178990797486311291/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2452730864881077963/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (51495460490298499/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (44218391936823152603733/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1022246231147596870609/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3769438156988141569/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2440004249180143903/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (12818098673151781/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (43781413939969102174483/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (810529644627349514159/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3744364642936845893/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (606841215067561687/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (204202223781013261/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (21675523057481409443289/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4016794484749911225589/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14878097978596006391/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1207405996309243713/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (203319742581014261/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (42927154928745772045527/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3981415303952048994591/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14779660042281925913/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2402344900903360337/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (50610524314613691/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (42509609388392856486663/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3946502378437945245519/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14682133826509531909/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2389962804039020853/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (201569246722248731/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (263114256484588287827/62500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3912047513248334683691/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2917101658266239081/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1188832444667765387/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (200701147036626073/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (41693043954711137038323/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (121188832030960423437/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14489772319830058283/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (11827251583724131/50000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (99918875882424867/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (5161721844100093028057/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (480559968254023346833/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3598728686192928799/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (470663644629028583/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (99489506159123587/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1278136018085151808419/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3811351028595565569111/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (893807773435027839/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2341267726619778501/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (6191402447088057/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (40512659112749011464087/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (118082773396820064457/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2841558004211741211/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2329297930689366677/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (49318824471982931/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (2508161160422143288559/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3746365309879009312923/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (882218782540732943/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (463481585692041389/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (49107554527474263/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r104_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (9938499420236715337241/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r104_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1857246623333027869843/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r104_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (14024044762362403263/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r104_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2305596806654656347/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r104_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (195589585247446873/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r112_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (39382805718545834853233/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r112_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (460378153468191838917/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r112_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6966705854422409649/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r112_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1146931824746536963/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r112_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (12172084070404601/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r120_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (3901689445806376525557/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r120_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3651954058796786545643/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r120_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1730448802313452037/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r120_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1141103771200152163/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r120_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (193921443435619341/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r128_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (19328079091431989634577/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r128_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (905318171241634274423/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r128_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1719321258230104793/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r128_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2270627575513162197/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r128_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (48273456505653221/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r136_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1915024683387279014929/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r136_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1795487096480199003021/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r136_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13666339960241792431/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r136_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2259122846968819689/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r136_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (48067609793381141/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r144_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (2371862510148094166081/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r144_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3561051812735682249613/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r144_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6789444781628298517/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r144_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2247692465957359831/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r144_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (95725614936693379/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r152_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (37603979371397664407651/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r152_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (882874729696228991137/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r152_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13492208504174410881/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r152_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2236335555525033201/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r152_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (190636146046899483/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r160_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (14013313309553361999331/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r160_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (164595910339591028741/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r160_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2518692996407628681/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r160_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (835712726724715017/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b97_r160_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B97.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (8909906148473239/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b97_c0 :
    bflatChargeRowsFor (bflatBlockJ5B97.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (837868590370549088528099/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B97.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 163 := by decide +kernel
  have hnil : rows.drop 168 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (45112725321710481372647/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b97_r000_c0]
    _ = (44887420753447331487899/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r008_c0,
        List.drop_drop]
      ring
    _ = (133993233443717815579531/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r016_c0,
        List.drop_drop]
      ring
    _ = (88887323691843458877007/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r024_c0,
        List.drop_drop]
      ring
    _ = (13820355843665608540037/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r032_c0,
        List.drop_drop]
      ring
    _ = (264052848427395508686119/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r040_c0,
        List.drop_drop]
      ring
    _ = (153281228907894182586391/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r048_c0,
        List.drop_drop]
      ring
    _ = (174330369426661245612551/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r056_c0,
        List.drop_drop]
      ring
    _ = (15614151312321345130537/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r064_c0,
        List.drop_drop]
      ring
    _ = (431647557560834372487881/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r072_c0,
        List.drop_drop]
      ring
    _ = (472547910139559230357289/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r080_c0,
        List.drop_drop]
      ring
    _ = (8016571394567316278459/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r088_c0,
        List.drop_drop]
      ring
    _ = (6914889347738281680479/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r096_c0,
        List.drop_drop]
      ring
    _ = (148236286375002348946821/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r104_c0,
        List.drop_drop]
      ring
    _ = (632327951218555230640517/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r112_c0,
        List.drop_drop]
      ring
    _ = (671344845676618995896087/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r120_c0,
        List.drop_drop]
      ring
    _ = (710001003859482975165241/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r128_c0,
        List.drop_drop]
      ring
    _ = (748301497527228555463821/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r136_c0,
        List.drop_drop]
      ring
    _ = (786251297689598062121117/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r144_c0,
        List.drop_drop]
      ring
    _ = (3218184676019514556753/39062500000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r152_c0,
        List.drop_drop]
      ring
    _ = (837868590370549088528099/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b97_r160_c0,
        List.drop_drop]
      ring
    _ = (837868590370549088528099/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b97_c1 :
    bflatChargeRowsFor (bflatBlockJ5B97.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (7801727213583672198773/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B97.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 163 := by decide +kernel
  have hnil : rows.drop 168 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (4163141330434711256107/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b97_r000_c1]
    _ = (1657790884830594194263/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r008_c1,
        List.drop_drop]
      ring
    _ = (12377939348743358453751/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r016_c1,
        List.drop_drop]
      ring
    _ = (8215293785940053012273/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r024_c1,
        List.drop_drop]
      ring
    _ = (4089476411326003450027/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r032_c1,
        List.drop_drop]
      ring
    _ = (12214398680291033122363/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r040_c1,
        List.drop_drop]
      ring
    _ = (5675059947804002298049/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r048_c1,
        List.drop_drop]
      ring
    _ = (2017959203266771635871/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r056_c1,
        List.drop_drop]
      ring
    _ = (452067373465738496549/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r064_c1,
        List.drop_drop]
      ring
    _ = (5001233702911408312323/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r072_c1,
        List.drop_drop]
      ring
    _ = (8764244130377366413539/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r080_c1,
        List.drop_drop]
      ring
    _ = (47599869400585074130319/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r088_c1,
        List.drop_drop]
      ring
    _ = (25673117355232041721621/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r096_c1,
        List.drop_drop]
      ring
    _ = (3441295497320633698933/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r104_c1,
        List.drop_drop]
      ring
    _ = (7342969148109459236783/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r112_c1,
        List.drop_drop]
      ring
    _ = (62395707243672460439907/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r120_c1,
        List.drop_drop]
      ring
    _ = (66016979928638997537599/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r128_c1,
        List.drop_drop]
      ring
    _ = (69607954121599395543641/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r136_c1,
        List.drop_drop]
      ring
    _ = (36584502967167538896627/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r144_c1,
        List.drop_drop]
      ring
    _ = (38350252426559996878901/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r152_c1,
        List.drop_drop]
      ring
    _ = (7801727213583672198773/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b97_r160_c1,
        List.drop_drop]
      ring
    _ = (7801727213583672198773/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b97_c2 :
    bflatChargeRowsFor (bflatBlockJ5B97.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (292280128642934400249/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B97.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 163 := by decide +kernel
  have hnil : rows.drop 168 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (15281183549713092537/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b97_r000_c2]
    _ = (7615043586799850957/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r008_c2,
        List.drop_drop]
      ring
    _ = (5692240871893996263/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r016_c2,
        List.drop_drop]
      ring
    _ = (15128846386724838419/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r024_c2,
        List.drop_drop]
      ring
    _ = (75393483525495360067/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r032_c2,
        List.drop_drop]
      ring
    _ = (4508657178388864299/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r040_c2,
        List.drop_drop]
      ring
    _ = (104855277394286817889/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r048_c2,
        List.drop_drop]
      ring
    _ = (59720392842809006647/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r056_c2,
        List.drop_drop]
      ring
    _ = (133930558005448071577/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r064_c2,
        List.drop_drop]
      ring
    _ = (148325472750219786773/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r072_c2,
        List.drop_drop]
      ring
    _ = (162626397125180232197/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r080_c2,
        List.drop_drop]
      ring
    _ = (44208546786559734563/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r088_c2,
        List.drop_drop]
      ring
    _ = (9547484383344533267/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r096_c2,
        List.drop_drop]
      ring
    _ = (204973732429253068603/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r104_c2,
        List.drop_drop]
      ring
    _ = (218907144138097887901/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r112_c2,
        List.drop_drop]
      ring
    _ = (232750734556605504197/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r120_c2,
        List.drop_drop]
      ring
    _ = (246505304622446342541/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r128_c2,
        List.drop_drop]
      ring
    _ = (65042911145672033743/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r136_c2,
        List.drop_drop]
      ring
    _ = (136875267072972366003/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r144_c2,
        List.drop_drop]
      ring
    _ = (287242742650119142887/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r152_c2,
        List.drop_drop]
      ring
    _ = (292280128642934400249/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b97_r160_c2,
        List.drop_drop]
      ring
    _ = (292280128642934400249/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b97_c3 :
    bflatChargeRowsFor (bflatBlockJ5B97.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (23904165612703200019/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B97.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 163 := by decide +kernel
  have hnil : rows.drop 168 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1232772684641043131/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b97_r000_c3]
    _ = (196731049366526569/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r008_c3,
        List.drop_drop]
      ring
    _ = (229946265104478379/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r016_c3,
        List.drop_drop]
      ring
    _ = (2446411335903388719/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r024_c3,
        List.drop_drop]
      ring
    _ = (6100228668116021151/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r032_c3,
        List.drop_drop]
      ring
    _ = (14602802237135402639/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r040_c3,
        List.drop_drop]
      ring
    _ = (4248191260293605873/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r048_c3,
        List.drop_drop]
      ring
    _ = (9685214965254977133/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r056_c3,
        List.drop_drop]
      ring
    _ = (10867940123627390233/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r064_c3,
        List.drop_drop]
      ring
    _ = (24089198470399923381/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r072_c3,
        List.drop_drop]
      ring
    _ = (13215233098509850941/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r080_c3,
        List.drop_drop]
      ring
    _ = (28759764127709068559/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r088_c3,
        List.drop_drop]
      ring
    _ = (1942323253510579719/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r096_c3,
        List.drop_drop]
      ring
    _ = (33382768862823931851/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r104_c3,
        List.drop_drop]
      ring
    _ = (35676632512317005777/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r112_c3,
        List.drop_drop]
      ring
    _ = (37958840054717310103/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r120_c3,
        List.drop_drop]
      ring
    _ = (402294676302304723/100000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r128_c3,
        List.drop_drop]
      ring
    _ = (42488590477199291989/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r136_c3,
        List.drop_drop]
      ring
    _ = (2236814147157832591/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r144_c3,
        List.drop_drop]
      ring
    _ = (46972618498681685021/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r152_c3,
        List.drop_drop]
      ring
    _ = (23904165612703200019/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b97_r160_c3,
        List.drop_drop]
      ring
    _ = (23904165612703200019/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b97_c4 :
    bflatChargeRowsFor (bflatBlockJ5B97.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (505478418071829439/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B97.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 163 := by decide +kernel
  have hnil : rows.drop 168 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (206879043962162991/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b97_r000_c4]
    _ = (412860885923356987/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r008_c4,
        List.drop_drop]
      ring
    _ = (617950464693785483/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r016_c4,
        List.drop_drop]
      ring
    _ = (102769086059349843/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r024_c4,
        List.drop_drop]
      ring
    _ = (205094486211162601/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r032_c4,
        List.drop_drop]
      ring
    _ = (1227914528314267769/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r040_c4,
        List.drop_drop]
      ring
    _ = (2858967550073033/20000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r048_c4,
        List.drop_drop]
      ring
    _ = (1630184922073142573/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r056_c4,
        List.drop_drop]
      ring
    _ = (1830022673837992307/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r064_c4,
        List.drop_drop]
      ring
    _ = (2029001686156239481/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r072_c4,
        List.drop_drop]
      ring
    _ = (445425312892611461/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r080_c4,
        List.drop_drop]
      ring
    _ = (2424401862350989029/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r088_c4,
        List.drop_drop]
      ring
    _ = (2620832080460886081/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r096_c4,
        List.drop_drop]
      ring
    _ = (1408210832854166477/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r104_c4,
        List.drop_drop]
      ring
    _ = (301117501083480657/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r112_c4,
        List.drop_drop]
      ring
    _ = (3205096454270425911/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r120_c4,
        List.drop_drop]
      ring
    _ = (679638056058607759/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r128_c4,
        List.drop_drop]
      ring
    _ = (3590460719466563359/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r136_c4,
        List.drop_drop]
      ring
    _ = (3781911949339950117/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r144_c4,
        List.drop_drop]
      ring
    _ = (2482842559616781/6250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r152_c4,
        List.drop_drop]
      ring
    _ = (505478418071829439/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b97_r160_c4,
        List.drop_drop]
      ring
    _ = (505478418071829439/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R35C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35)
      bflatExactSingletonBlocksJ5Seg0 =
      (837868590370549088528099/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R35_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b97_c0]
  norm_num

theorem bflatExactChargeJ5R35C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35)
      bflatExactSingletonBlocksJ5Seg1 =
      (7801727213583672198773/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R35_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b97_c1]
  norm_num

theorem bflatExactChargeJ5R35C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35)
      bflatExactSingletonBlocksJ5Seg2 =
      (292280128642934400249/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R35_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b97_c2]
  norm_num

theorem bflatExactChargeJ5R35C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35)
      bflatExactSingletonBlocksJ5Seg3 =
      (23904165612703200019/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R35_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b97_c3]
  norm_num

theorem bflatExactChargeJ5R35C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R35)
      bflatExactSingletonBlocksJ5Seg4 =
      (505478418071829439/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R35_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b97_c4]
  norm_num

end ASDExplicitGamma.Model
