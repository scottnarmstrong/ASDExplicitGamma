module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b96_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (54879980855567992612989/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2477550929213059412351/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8677577117126177417/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2718925349310485569/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (224375667282944141/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (10854700116268374544133/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4906859286983355705533/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (269277031128812509/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (338054015200657901/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (6980849259684081/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (53677010930547045121953/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2429646623079927815857/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (4278352037771116859/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (168126841402897929/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (556008482581331/25000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (424722478967391859059/80000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (300774563153321978343/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3398836475539872861/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1337858789625569517/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (221424357937043629/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (13128300161878907422519/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (476614806866844751427/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16876046349418682333/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (133074833634576351/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (220450111211080949/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (12986372854146734304783/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (590068512593504231259/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16758993689862073337/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (330920865800080763/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (43896138375690923/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (10277398983070898710997/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4675582957301303221647/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16643017912971127739/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2633328497877517531/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (218516137028720969/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (508375281655268682829/100000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4631242641701621972533/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16528112374915408451/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2619381510562597321/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (108778240570051279/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (25148456104317694868093/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4587517294610511087137/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8207135116781523881/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (162845377940637747/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (216601755493577687/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (3110310741945356084929/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (908879436157000491653/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8150742207587529707/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2591762143398051421/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (215651987675464331/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (12310383889296030103871/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1125468169505205608193/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16189747587955830767/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (10070663220659863/39062500000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (42941440233072303/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (24363217533643440910119/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4459934268081954920741/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8039526071034872117/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2564508900394979581/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (106883707502949461/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (48219505440485039064997/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (441857252946622093767/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1996173771964486429/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2551019363691275673/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (106416321775193547/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r104_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (2982536551154506387581/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r104_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2188889065928306538411/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r104_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (7930376743419443807/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r104_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2537620987661913659/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r104_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (52975724071037563/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r112_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (2361475716476222766971/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r112_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1084385458027311612149/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r112_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3938283392510991911/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r112_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2524313525339526479/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r112_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (42195635543013687/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r120_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (23373068995227597147199/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r120_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1074463617907690366569/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r120_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1564652161827831301/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r120_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (313887083664607209/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r120_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (105029243664321361/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r128_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (23135151312390210823727/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r128_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4258706975000895845557/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r128_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (7770454264419097439/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r128_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2497970052267742429/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r128_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (52285954900684991/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r136_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (286261611221005820137/62500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r136_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4220090349699503586863/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r136_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15436284913262242473/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r136_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (496986649622782773/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r136_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (208234164077054523/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r144_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (22727531155717202917641/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r144_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2095727399303776598453/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r144_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1535843035370462539/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r144_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (309401439612672733/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b96_r144_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B96.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (51888761739806731/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b96_c0 :
    bflatChargeRowsFor (bflatBlockJ5B96.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (925349306242392257602973/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B96.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 148 := by decide +kernel
  have hnil : rows.drop 152 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (54879980855567992612989/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b96_r000_c0]
    _ = (54576740718454932666827/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r008_c0,
        List.drop_drop]
      ring
    _ = (162830492367456910455607/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r016_c0,
        List.drop_drop]
      ring
    _ = (107960401119190446418991/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r024_c0,
        List.drop_drop]
      ring
    _ = (134217001442948261264029/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r032_c0,
        List.drop_drop]
      ring
    _ = (32037949430248345974719/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r040_c0,
        List.drop_drop]
      ring
    _ = (14870659568713518132087/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r048_c0,
        List.drop_drop]
      ring
    _ = (16904160695334592863403/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r056_c0,
        List.drop_drop]
      ring
    _ = (472900929592000211321261/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r064_c0,
        List.drop_drop]
      ring
    _ = (4181327211705007269441/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r072_c0,
        List.drop_drop]
      ring
    _ = (571907437020310029095609/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r080_c0,
        List.drop_drop]
      ring
    _ = (620633872087596910915847/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r088_c0,
        List.drop_drop]
      ring
    _ = (167213344382020487495211/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r096_c0,
        List.drop_drop]
      ring
    _ = (35828698117327702609107/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r104_c0,
        List.drop_drop]
      ring
    _ = (19095086916901962688039/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r112_c0,
        List.drop_drop]
      ring
    _ = (405274807333266850907979/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r120_c0,
        List.drop_drop]
      ring
    _ = (214204979322828530865853/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r128_c0,
        List.drop_drop]
      ring
    _ = (225655443771668763671333/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r136_c0,
        List.drop_drop]
      ring
    _ = (925349306242392257602973/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b96_r144_c0,
        List.drop_drop]
      ring
    _ = (925349306242392257602973/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b96_c1 :
    bflatChargeRowsFor (bflatBlockJ5B96.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (84427162281007197233111/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B96.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 148 := by decide +kernel
  have hnil : rows.drop 152 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (2477550929213059412351/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b96_r000_c1]
    _ = (1972392229081894906047/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r008_c1,
        List.drop_drop]
      ring
    _ = (14721254391569330161949/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r016_c1,
        List.drop_drop]
      ring
    _ = (19533647402022481815437/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r024_c1,
        List.drop_drop]
      ring
    _ = (24299795470690929329707/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r032_c1,
        List.drop_drop]
      ring
    _ = (29020343571438963179779/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r040_c1,
        List.drop_drop]
      ring
    _ = (16847963264370133200713/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r048_c1,
        List.drop_drop]
      ring
    _ = (38327169170441888373959/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r056_c1,
        List.drop_drop]
      ring
    _ = (5364335808131549932637/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r064_c1,
        List.drop_drop]
      ring
    _ = (47459083645837401919361/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r072_c1,
        List.drop_drop]
      ring
    _ = (51960956323858224352133/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r080_c1,
        List.drop_drop]
      ring
    _ = (28210445295970089636437/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r088_c1,
        List.drop_drop]
      ring
    _ = (3802466445087900013159/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r096_c1,
        List.drop_drop]
      ring
    _ = (32608620626631506643683/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r104_c1,
        List.drop_drop]
      ring
    _ = (34777391542686129867981/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r112_c1,
        List.drop_drop]
      ring
    _ = (36926318778501510601119/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r120_c1,
        List.drop_drop]
      ring
    _ = (15622268906400783409559/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r128_c1,
        List.drop_drop]
      ring
    _ = (41165717440851710317329/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r136_c1,
        List.drop_drop]
      ring
    _ = (84427162281007197233111/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b96_r144_c1,
        List.drop_drop]
      ring
    _ = (84427162281007197233111/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b96_c2 :
    bflatChargeRowsFor (bflatBlockJ5B96.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (151186703465520485467/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B96.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 148 := by decide +kernel
  have hnil : rows.drop 152 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (8677577117126177417/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b96_r000_c2]
    _ = (3458888422649635541/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r008_c2,
        List.drop_drop]
      ring
    _ = (25851146188790411423/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r016_c2,
        List.drop_drop]
      ring
    _ = (68696474755280187151/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r024_c2,
        List.drop_drop]
      ring
    _ = (21393130276174717371/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r032_c2,
        List.drop_drop]
      ring
    _ = (102331514794560942821/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r040_c2,
        List.drop_drop]
      ring
    _ = (743590829422075441/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r048_c2,
        List.drop_drop]
      ring
    _ = (135502645082447479011/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r056_c2,
        List.drop_drop]
      ring
    _ = (151916915316010526773/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r064_c2,
        List.drop_drop]
      ring
    _ = (168218399731185586187/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r072_c2,
        List.drop_drop]
      ring
    _ = (92204073659570708477/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r080_c2,
        List.drop_drop]
      ring
    _ = (50121799865302790297/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r088_c2,
        List.drop_drop]
      ring
    _ = (10822829481846352631/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r096_c2,
        List.drop_drop]
      ring
    _ = (116158671561882970117/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r104_c2,
        List.drop_drop]
      ring
    _ = (124035238346904953939/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r112_c2,
        List.drop_drop]
      ring
    _ = (32964624789011027611/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r120_c2,
        List.drop_drop]
      ring
    _ = (139628953420463207883/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r128_c2,
        List.drop_drop]
      ring
    _ = (294694191754188658239/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r136_c2,
        List.drop_drop]
      ring
    _ = (151186703465520485467/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b96_r144_c2,
        List.drop_drop]
      ring
    _ = (151186703465520485467/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b96_c3 :
    bflatChargeRowsFor (bflatBlockJ5B96.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (24017562300159811621/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B96.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 148 := by decide +kernel
  have hnil : rows.drop 152 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (2718925349310485569/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b96_r000_c3]
    _ = (5423357470915748777/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r008_c3,
        List.drop_drop]
      ring
    _ = (8113386933362115641/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r016_c3,
        List.drop_drop]
      ring
    _ = (431564180504530187/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r024_c3,
        List.drop_drop]
      ring
    _ = (2690120237060956339/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r032_c3,
        List.drop_drop]
      ring
    _ = (16097968111705427799/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r040_c3,
        List.drop_drop]
      ring
    _ = (1873129660958294533/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r048_c3,
        List.drop_drop]
      ring
    _ = (21350678120145542651/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r056_c3,
        List.drop_drop]
      ring
    _ = (23956204167195746603/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r064_c3,
        List.drop_drop]
      ring
    _ = (3318495788824224753/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r072_c3,
        List.drop_drop]
      ring
    _ = (3640757011885340369/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r080_c3,
        List.drop_drop]
      ring
    _ = (31690564995477702533/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r088_c3,
        List.drop_drop]
      ring
    _ = (17120792179584489103/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r096_c3,
        List.drop_drop]
      ring
    _ = (7355841069366178373/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r104_c3,
        List.drop_drop]
      ring
    _ = (4912939859021302293/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r112_c3,
        List.drop_drop]
      ring
    _ = (2613413471342954751/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r120_c3,
        List.drop_drop]
      ring
    _ = (8862517118751003689/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r128_c3,
        List.drop_drop]
      ring
    _ = (4679751884186893231/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r136_c3,
        List.drop_drop]
      ring
    _ = (24017562300159811621/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b96_r144_c3,
        List.drop_drop]
      ring
    _ = (24017562300159811621/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b96_c4 :
    bflatChargeRowsFor (bflatBlockJ5B96.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (99881252179968219/250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B96.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 148 := by decide +kernel
  have hnil : rows.drop 152 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (224375667282944141/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b96_r000_c4]
    _ = (447762843592834733/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r008_c4,
        List.drop_drop]
      ring
    _ = (670166236625367133/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r016_c4,
        List.drop_drop]
      ring
    _ = (445795297281205381/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r024_c4,
        List.drop_drop]
      ring
    _ = (1112040705773491711/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r032_c4,
        List.drop_drop]
      ring
    _ = (665760698825973163/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r040_c4,
        List.drop_drop]
      ring
    _ = (310007506936133459/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r048_c4,
        List.drop_drop]
      ring
    _ = (1767594015820769853/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r056_c4,
        List.drop_drop]
      ring
    _ = (99209788565717377/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r064_c4,
        List.drop_drop]
      ring
    _ = (2199847758989811871/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r072_c4,
        List.drop_drop]
      ring
    _ = (1207277480077586693/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r080_c4,
        List.drop_drop]
      ring
    _ = (657080593790268077/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r088_c4,
        List.drop_drop]
      ring
    _ = (1420577509355729701/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r096_c4,
        List.drop_drop]
      ring
    _ = (1526528957497804827/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r104_c4,
        List.drop_drop]
      ring
    _ = (3264036092710678089/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r112_c4,
        List.drop_drop]
      ring
    _ = (3474094580039320811/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r120_c4,
        List.drop_drop]
      ring
    _ = (147329535985682431/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r128_c4,
        List.drop_drop]
      ring
    _ = (1945736281859557649/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r136_c4,
        List.drop_drop]
      ring
    _ = (99881252179968219/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b96_r144_c4,
        List.drop_drop]
      ring
    _ = (99881252179968219/250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R34C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34)
      bflatExactSingletonBlocksJ5Seg0 =
      (925349306242392257602973/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R34_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b96_c0]
  norm_num

theorem bflatExactChargeJ5R34C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34)
      bflatExactSingletonBlocksJ5Seg1 =
      (84427162281007197233111/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R34_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b96_c1]
  norm_num

theorem bflatExactChargeJ5R34C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34)
      bflatExactSingletonBlocksJ5Seg2 =
      (151186703465520485467/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R34_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b96_c2]
  norm_num

theorem bflatExactChargeJ5R34C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34)
      bflatExactSingletonBlocksJ5Seg3 =
      (24017562300159811621/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R34_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b96_c3]
  norm_num

theorem bflatExactChargeJ5R34C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R34)
      bflatExactSingletonBlocksJ5Seg4 =
      (99881252179968219/250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R34_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b96_c4]
  norm_num

end ASDExplicitGamma.Model
