module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b94_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (8142797592738372750967/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1391481622176872298027/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2192527426606875893/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (323766759316391233/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (129452706037901293/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (20081101118965879360907/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3439006802236539618207/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (339977697547116707/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3219465171604806797/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (257712758164638779/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (3169790265726896365133/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (425003485246565793867/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21593964733659003667/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (320145674580645703/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (128266193415516127/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (78188188597449958679533/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3361743531270902313399/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10715685073219956027/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (397954042970339193/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (127681767485965007/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (38576948732873369190167/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (415516392718984947793/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21270713021804364427/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1582991290368609153/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1271027419562473/50000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (76141119735437819357869/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (6574338454536763431277/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10555960993515957439/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3148498659110192723/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (126528779811958321/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (75149129646965187606131/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (6501674777290923828943/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (4190986017641580989/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (156558618235443901/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (125959566329231097/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (14835447516988017493111/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (6430232552619448587323/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (20799674701486737349/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3113996059894300717/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (250789617821598921/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (73224788474185651735043/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1589993775587444090517/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (20646097425763225397/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3096962673678393989/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (249668473601346431/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (72291160186847715576739/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3145433844131307932749/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (20494143958829927247/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3080065689145187251/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (62138800343790837/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (7137576196624987462259/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1244575485787382171307/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1017188197952486297/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (76582478211197307/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (123724672207361937/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (70478032872719592614113/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (769496651885052773251/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (504872772362894431/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (609331507130071871/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (246350486708856093/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (17399360064041673405593/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (6090125623926760858187/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10023770940802979433/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (3030135957676628767/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (61314562906179561/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r104_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (34366739129878263481989/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r104_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (6025306833240613323071/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r104_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (9950808757383608071/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r104_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (301372992362629949/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r104_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (6104307510674687/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r112_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (67885666358587986806971/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r112_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5961490535433686438097/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r112_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (19757101689287220097/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r112_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1498717711353120291/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r112_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (243092330674431383/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r120_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1684079476538193366743/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r120_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1480516428623586783583/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r120_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (983371340914902411/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r120_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (746825563910799383/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b94_r120_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B94.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (30302506182820661/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b94_c0 :
    bflatChargeRowsFor (bflatBlockJ5B94.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1132233833216855421180281/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B94.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 122 := by decide +kernel
  have hnil : rows.drop 128 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (8142797592738372750967/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b94_r000_c0]
    _ = (80876190201623622476649/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r008_c0,
        List.drop_drop]
      ring
    _ = (240997137046419654081623/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r016_c0,
        List.drop_drop]
      ring
    _ = (79796331410967403190289/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r024_c0,
        List.drop_drop]
      ring
    _ = (39633922310961635114149/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r032_c0,
        List.drop_drop]
      ring
    _ = (472480342845054170499359/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r040_c0,
        List.drop_drop]
      ring
    _ = (54762947249201935810549/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r048_c0,
        List.drop_drop]
      ring
    _ = (124361342015391889114209/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r056_c0,
        List.drop_drop]
      ring
    _ = (86878937318893137163261/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r064_c0,
        List.drop_drop]
      ring
    _ = (767322658737992812882827/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r072_c0,
        List.drop_drop]
      ring
    _ = (838698420704242687505417/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r080_c0,
        List.drop_drop]
      ring
    _ = (90917645357696228011953/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r088_c0,
        List.drop_drop]
      ring
    _ = (489386946916564486870951/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r096_c0,
        List.drop_drop]
      ring
    _ = (26187684302322137517647/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r104_c0,
        List.drop_drop]
      ring
    _ = (1115393038451473487512851/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r112_c0,
        List.drop_drop]
      ring
    _ = (1132233833216855421180281/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b94_r120_c0,
        List.drop_drop]
      ring
    _ = (1132233833216855421180281/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b94_c1 :
    bflatChargeRowsFor (bflatBlockJ5B94.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (98100605465649565740497/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B94.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 122 := by decide +kernel
  have hnil : rows.drop 128 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (1391481622176872298027/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b94_r000_c1]
    _ = (13835421715357440726549/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r008_c1,
        List.drop_drop]
      ring
    _ = (20635477479302493428421/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r016_c1,
        List.drop_drop]
      ring
    _ = (27358964541844298055219/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r024_c1,
        List.drop_drop]
      ring
    _ = (34007226825348057219907/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r032_c1,
        List.drop_drop]
      ring
    _ = (2536347829992801290699/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r040_c1,
        List.drop_drop]
      ring
    _ = (47083240057175744480127/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r048_c1,
        List.drop_drop]
      ring
    _ = (1070269452195903861349/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r056_c1,
        List.drop_drop]
      ring
    _ = (29936723856072484714759/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r064_c1,
        List.drop_drop]
      ring
    _ = (8270539425050948161877/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r072_c1,
        List.drop_drop]
      ring
    _ = (72387192829344496151551/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r080_c1,
        List.drop_drop]
      ring
    _ = (78543166044424918337559/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r088_c1,
        List.drop_drop]
      ring
    _ = (42316645834175839597873/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r096_c1,
        List.drop_drop]
      ring
    _ = (90658598501592292518817/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r104_c1,
        List.drop_drop]
      ring
    _ = (48310044518512989478457/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r112_c1,
        List.drop_drop]
      ring
    _ = (98100605465649565740497/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b94_r120_c1,
        List.drop_drop]
      ring
    _ = (98100605465649565740497/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b94_c2 :
    bflatChargeRowsFor (bflatBlockJ5B94.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (158574227808053814241/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B94.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 122 := by decide +kernel
  have hnil : rows.drop 128 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (2192527426606875893/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b94_r000_c2]
    _ = (21841923454542114089/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r008_c2,
        List.drop_drop]
      ring
    _ = (13055562328548646369/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r016_c2,
        List.drop_drop]
      ring
    _ = (86709181789183143899/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r024_c2,
        List.drop_drop]
      ring
    _ = (53989947405493754163/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r032_c2,
        List.drop_drop]
      ring
    _ = (32272954199504855801/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r040_c2,
        List.drop_drop]
      ring
    _ = (150046746886227328149/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r048_c2,
        List.drop_drop]
      ring
    _ = (85423210793857032749/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r056_c2,
        List.drop_drop]
      ring
    _ = (38298503802695458179/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r064_c2,
        List.drop_drop]
      ring
    _ = (105993331486153609071/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r072_c2,
        List.drop_drop]
      ring
    _ = (116165213465678472041/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r080_c2,
        List.drop_drop]
      ring
    _ = (126262668912936360661/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r088_c2,
        List.drop_drop]
      ring
    _ = (68143219926869670047/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r096_c2,
        List.drop_drop]
      ring
    _ = (29247449722224589633/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r104_c2,
        List.drop_drop]
      ring
    _ = (312231598911533116427/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r112_c2,
        List.drop_drop]
      ring
    _ = (158574227808053814241/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b94_r120_c2,
        List.drop_drop]
      ring
    _ = (158574227808053814241/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b94_c3 :
    bflatChargeRowsFor (bflatBlockJ5B94.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (11869245853407570141/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B94.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 122 := by decide +kernel
  have hnil : rows.drop 128 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (323766759316391233/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b94_r000_c3]
    _ = (6457132764768719127/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r008_c3,
        List.drop_drop]
      ring
    _ = (9658589510575176157/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r016_c3,
        List.drop_drop]
      ring
    _ = (12842221854337889701/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r024_c3,
        List.drop_drop]
      ring
    _ = (16008204435075108007/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r032_c3,
        List.drop_drop]
      ring
    _ = (1915670309418530073/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r040_c3,
        List.drop_drop]
      ring
    _ = (17830300367115343/8000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r048_c3,
        List.drop_drop]
      ring
    _ = (25401871518788479467/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r056_c3,
        List.drop_drop]
      ring
    _ = (1781177137029179591/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r064_c3,
        List.drop_drop]
      ring
    _ = (31578899881612060707/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r072_c3,
        List.drop_drop]
      ring
    _ = (34642199010059952987/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r080_c3,
        List.drop_drop]
      ring
    _ = (18844428272855156171/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r088_c3,
        List.drop_drop]
      ring
    _ = (40718992503386941109/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r096_c3,
        List.drop_drop]
      ring
    _ = (43732722427013240599/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r104_c3,
        List.drop_drop]
      ring
    _ = (46730157849719481181/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r112_c3,
        List.drop_drop]
      ring
    _ = (11869245853407570141/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b94_r120_c3,
        List.drop_drop]
      ring
    _ = (11869245853407570141/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b94_c4 :
    bflatChargeRowsFor (bflatBlockJ5B94.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (764727457450348833/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B94.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 122 := by decide +kernel
  have hnil : rows.drop 128 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (129452706037901293/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b94_r000_c4]
    _ = (103323634048088273/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r008_c4,
        List.drop_drop]
      ring
    _ = (773150557071473619/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r016_c4,
        List.drop_drop]
      ring
    _ = (1028514092043403633/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r024_c4,
        List.drop_drop]
      ring
    _ = (1282719575955898233/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r032_c4,
        List.drop_drop]
      ring
    _ = (12286217084638519/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r040_c4,
        List.drop_drop]
      ring
    _ = (1787696268238277069/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r048_c4,
        List.drop_drop]
      ring
    _ = (203848588605987599/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r056_c4,
        List.drop_drop]
      ring
    _ = (2288154359661222421/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r064_c4,
        List.drop_drop]
      ring
    _ = (2536709561036385769/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r072_c4,
        List.drop_drop]
      ring
    _ = (2784158905451109643/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r080_c4,
        List.drop_drop]
      ring
    _ = (378813674019995717/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r088_c4,
        List.drop_drop]
      ring
    _ = (163788382189234199/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r096_c4,
        List.drop_drop]
      ring
    _ = (175996997210583573/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r104_c4,
        List.drop_drop]
      ring
    _ = (3763032274886102843/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r112_c4,
        List.drop_drop]
      ring
    _ = (764727457450348833/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b94_r120_c4,
        List.drop_drop]
      ring
    _ = (764727457450348833/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R32C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32)
      bflatExactSingletonBlocksJ5Seg0 =
      (1132233833216855421180281/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R32_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b94_c0]
  norm_num

theorem bflatExactChargeJ5R32C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32)
      bflatExactSingletonBlocksJ5Seg1 =
      (98100605465649565740497/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R32_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b94_c1]
  norm_num

theorem bflatExactChargeJ5R32C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32)
      bflatExactSingletonBlocksJ5Seg2 =
      (158574227808053814241/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R32_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b94_c2]
  norm_num

theorem bflatExactChargeJ5R32C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32)
      bflatExactSingletonBlocksJ5Seg3 =
      (11869245853407570141/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R32_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b94_c3]
  norm_num

theorem bflatExactChargeJ5R32C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R32)
      bflatExactSingletonBlocksJ5Seg4 =
      (764727457450348833/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R32_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b94_c4]
  norm_num

end ASDExplicitGamma.Model
