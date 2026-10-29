module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b98_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (37136256334503997952167/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (872863778282661667301/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2674851909838067091/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1776670551814839/8000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (189522048612234421/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (36801628450087740430727/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3462754045982171265911/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (830585324353913197/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (552413089420404261/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (188716561248889967/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (36471559324449570895513/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (171720058966434766989/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (264104131514374061/200000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (17588297362352619/80000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (37583006655618923/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (7229192217075051566259/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (851597631188327847419/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6560887105635043731/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2187491837622849433/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (37423483805841991/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (17912374075845402633709/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3378716238230337642911/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (13039058822544881687/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2176515594039213819/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (37264734938503241/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (17753918596327657458813/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3351372618848993801127/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3239262840719790319/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (270700962420227057/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (92766879209667401/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (35195147084535548589219/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1662177053590710222733/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (12875743015923865887/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2154767439689295917/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (92373815200133049/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (6977319772912574397309/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (103051727603606955093/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (12795125197331804019/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (85759765119232037/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (91982626461061209/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (34582115682493255059117/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (130850834582971675211/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (12715189554998600767/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1066643552197195317/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (183186590404291721/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (8570405687501992591723/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3245195702947757421003/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3158981991984935401/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2122645736394881637/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (182411609415409231/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (3398504728820508644837/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3219424782259385987693/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (12557332543892576489/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1056034709322010297/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (5676258708479231/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (16846159236720824538001/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1596976607548388150437/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1247939561573789917/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (525389393171755353/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (180872569015546261/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (33403367381792681401667/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (792194059882893804161/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (12402109736840150929/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2091109646450453039/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (36021690676626819/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r104_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (8279531733099116981371/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r104_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1571944607828375737413/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r104_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6162733837704312603/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r104_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2080725113567226407/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r104_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (35869581349937931/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r112_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (32836531829955795639351/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r112_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3119287621968668988599/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r112_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1531182800998020309/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r112_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (258800434068123693/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r112_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (89295453033198273/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r120_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (4069814813332870771213/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r120_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (773741762905351621667/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r120_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1217408711215709147/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r120_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (103007212289732809/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r120_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (177837430182712787/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r128_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (16142012531905748642349/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r128_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3070923208580380216539/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r128_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2419867031724443577/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r128_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1024973489267999959/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r128_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (44271864939510861/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r136_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (32012991213350826448681/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r136_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (380893987962720755519/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r136_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (6012600051337977773/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r136_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (101990561879866091/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r136_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 136).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (88170488581911469/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r144_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (992042444363479424911/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r144_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3023649050763421976477/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r144_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (5975837837629488723/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r144_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2029736610126096527/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r144_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 144).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (175597966377427653/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r152_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (31481068841576701435057/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r152_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (600082132494415359681/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r152_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11878755773645394301/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r152_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (252465337778410321/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r152_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 152).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (21857301608666117/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r160_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (31220067275508108751611/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r160_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2977432846470421323731/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r160_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11806434451876233759/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r160_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1004884568772802817/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r160_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 160).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (174122303484873581/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r168_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 168).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (15481149549415982930809/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r168_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 168).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2954711801366510499407/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r168_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 168).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11734705911031253027/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r168_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 168).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (999937777903826071/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r168_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 168).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (86694813161022971/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r176_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 176).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (144313213404027976157/125000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r176_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 176).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1102210921948890761923/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r176_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 176).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (273883888244403081/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r176_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 176).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (186853706794732757/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b98_r176_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B98.entries.map bflatSingletonModeBlock).drop 176).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (64832915183775543/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b98_c0 :
    bflatChargeRowsFor (bflatBlockJ5B98.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (378839126058924829714237/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B98.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 179 := by decide +kernel
  have hnil : rows.drop 184 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (37136256334503997952167/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b98_r000_c0]
    _ = (36968942392295869191447/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r008_c0,
        List.drop_drop]
      ring
    _ = (110409444109041309278407/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r016_c0,
        List.drop_drop]
      ring
    _ = (73277702597208283554851/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r024_c0,
        List.drop_drop]
      ring
    _ = (1139875958413171077357/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r032_c0,
        List.drop_drop]
      ring
    _ = (108943995269381343647373/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r040_c0,
        List.drop_drop]
      ring
    _ = (50616627524659647176793/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r048_c0,
        List.drop_drop]
      ring
    _ = (28796973648786110787051/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r056_c0,
        List.drop_drop]
      ring
    _ = (322551852170354362929627/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r064_c0,
        List.drop_drop]
      ring
    _ = (356833474920362333296519/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r072_c0,
        List.drop_drop]
      ring
    _ = (390818522208567419744889/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r080_c0,
        List.drop_drop]
      ring
    _ = (424510840682009068820891/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r088_c0,
        List.drop_drop]
      ring
    _ = (228957104031900875111279/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r096_c0,
        List.drop_drop]
      ring
    _ = (245516167498099109074021/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r104_c0,
        List.drop_drop]
      ring
    _ = (523868866826154013787393/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r112_c0,
        List.drop_drop]
      ring
    _ = (556427385332816979957097/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r120_c0,
        List.drop_drop]
      ring
    _ = (117742282079325695448359/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r128_c0,
        List.drop_drop]
      ring
    _ = (155181100402494825922619/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r136_c0,
        List.drop_drop]
      ring
    _ = (163117439957402661321907/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r144_c0,
        List.drop_drop]
      ring
    _ = (136790165734237469344537/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r152_c0,
        List.drop_drop]
      ring
    _ = (89396361993336931934287/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r160_c0,
        List.drop_drop]
      ring
    _ = (373066597522763710667957/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 176) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 168)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r168_c0,
        List.drop_drop]
      ring
    _ = (378839126058924829714237/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 184) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 176)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b98_r176_c0,
        List.drop_drop]
      ring
    _ = (378839126058924829714237/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b98_c1 :
    bflatChargeRowsFor (bflatBlockJ5B98.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (71780354199731080494267/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B98.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 179 := by decide +kernel
  have hnil : rows.drop 184 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (872863778282661667301/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b98_r000_c1]
    _ = (1390841831822563587023/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r008_c1,
        List.drop_drop]
      ring
    _ = (2077722067688302654979/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r016_c1,
        List.drop_drop]
      ring
    _ = (13795000863194824664571/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r024_c1,
        List.drop_drop]
      ring
    _ = (8586858550712581153741/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r032_c1,
        List.drop_drop]
      ring
    _ = (20525089720274156108609/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r040_c1,
        List.drop_drop]
      ring
    _ = (953977753098223062163/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r048_c1,
        List.drop_drop]
      ring
    _ = (27147099110770999117051/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r056_c1,
        List.drop_drop]
      ring
    _ = (15209184987672645498663/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r064_c1,
        List.drop_drop]
      ring
    _ = (33663565678293048418329/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r072_c1,
        List.drop_drop]
      ring
    _ = (18441495230276217203011/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r080_c1,
        List.drop_drop]
      ring
    _ = (2504808979728075669181/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r088_c1,
        List.drop_drop]
      ring
    _ = (2162285995759039296177/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r096_c1,
        List.drop_drop]
      ring
    _ = (23194804565418768699183/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r104_c1,
        List.drop_drop]
      ring
    _ = (9901779350561241277393/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r112_c1,
        List.drop_drop]
      ring
    _ = (52603863804427612873633/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r120_c1,
        List.drop_drop]
      ring
    _ = (13918696753251998272543/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r128_c1,
        List.drop_drop]
      ring
    _ = (14680484729177439783581/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r136_c1,
        List.drop_drop]
      ring
    _ = (61745587967473181110801/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r144_c1,
        List.drop_drop]
      ring
    _ = (32372999314972628954603/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r152_c1,
        List.drop_drop]
      ring
    _ = (67723431476415679232937/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r160_c1,
        List.drop_drop]
      ring
    _ = (8834767909722773716543/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 176) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 168)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r168_c1,
        List.drop_drop]
      ring
    _ = (71780354199731080494267/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 184) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 176)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b98_r176_c1,
        List.drop_drop]
      ring
    _ = (71780354199731080494267/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b98_c2 :
    bflatChargeRowsFor (bflatBlockJ5B98.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (56014961164900155871/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B98.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 179 := by decide +kernel
  have hnil : rows.drop 184 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (2674851909838067091/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b98_r000_c2]
    _ = (26663624738852946607/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r008_c2,
        List.drop_drop]
      ring
    _ = (39868831314571649657/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r016_c2,
        List.drop_drop]
      ring
    _ = (52990605525841737119/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r024_c2,
        List.drop_drop]
      ring
    _ = (33014832174193309403/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r032_c2,
        List.drop_drop]
      ring
    _ = (39493357855632890041/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r040_c2,
        List.drop_drop]
      ring
    _ = (91862458727189645969/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r048_c2,
        List.drop_drop]
      ring
    _ = (26164395981130362497/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r056_c2,
        List.drop_drop]
      ring
    _ = (23474554695904010151/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r064_c2,
        List.drop_drop]
      ring
    _ = (130008701447459792359/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r072_c2,
        List.drop_drop]
      ring
    _ = (8910377124459523053/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r080_c2,
        List.drop_drop]
      ring
    _ = (77522714803545134009/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r088_c2,
        List.drop_drop]
      ring
    _ = (167447539343930418947/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r096_c2,
        List.drop_drop]
      ring
    _ = (179773007019339044153/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r104_c2,
        List.drop_drop]
      ring
    _ = (1536179755418585653/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r112_c2,
        List.drop_drop]
      ring
    _ = (40839311307896059619/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r120_c2,
        List.drop_drop]
      ring
    _ = (10814794584905125799/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r128_c2,
        List.drop_drop]
      ring
    _ = (114160545900389235763/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r136_c2,
        List.drop_drop]
      ring
    _ = (60068191869009362243/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r144_c2,
        List.drop_drop]
      ring
    _ = (252151523249682843273/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r152_c2,
        List.drop_drop]
      ring
    _ = (32994744712694884629/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r160_c2,
        List.drop_drop]
      ring
    _ = (275692663612590330059/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 176) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 168)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r168_c2,
        List.drop_drop]
      ring
    _ = (56014961164900155871/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 184) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 176)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b98_r176_c2,
        List.drop_drop]
      ring
    _ = (56014961164900155871/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b98_c3 :
    bflatChargeRowsFor (bflatBlockJ5B98.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (47125623775934748803/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B98.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 179 := by decide +kernel
  have hnil : rows.drop 184 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1776670551814839/8000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b98_r000_c3]
    _ = (2215245273725082897/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r008_c3,
        List.drop_drop]
      ring
    _ = (6629027717744243169/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r016_c3,
        List.drop_drop]
      ring
    _ = (4408259777683546301/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r024_c3,
        List.drop_drop]
      ring
    _ = (10993035149406306421/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r032_c3,
        List.drop_drop]
      ring
    _ = (13158642848768122877/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r040_c3,
        List.drop_drop]
      ring
    _ = (7656705144228709397/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r048_c3,
        List.drop_drop]
      ring
    _ = (17457404416438219719/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r056_c3,
        List.drop_drop]
      ring
    _ = (19590691520832610353/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r064_c3,
        List.drop_drop]
      ring
    _ = (2171333725722749199/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r072_c3,
        List.drop_drop]
      ring
    _ = (2978175834483939073/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r080_c3,
        List.drop_drop]
      ring
    _ = (6481741062139633499/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r088_c3,
        List.drop_drop]
      ring
    _ = (5603614779001797407/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r096_c3,
        List.drop_drop]
      ring
    _ = (15049399504288106721/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r104_c3,
        List.drop_drop]
      ring
    _ = (16084601240560601493/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r112_c3,
        List.drop_drop]
      ring
    _ = (17114673363457929583/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r120_c3,
        List.drop_drop]
      ring
    _ = (9069823426362964771/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r128_c3,
        List.drop_drop]
      ring
    _ = (4789888117881147613/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r136_c3,
        List.drop_drop]
      ring
    _ = (40348841553175277431/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r144_c3,
        List.drop_drop]
      ring
    _ = (42368564255402559999/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r152_c3,
        List.drop_drop]
      ring
    _ = (44378333392948165633/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r160_c3,
        List.drop_drop]
      ring
    _ = (1855128357950232711/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 176) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 168)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r168_c3,
        List.drop_drop]
      ring
    _ = (47125623775934748803/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 184) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 176)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b98_r176_c3,
        List.drop_drop]
      ring
    _ = (47125623775934748803/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b98_c4 :
    bflatChargeRowsFor (bflatBlockJ5B98.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (2027033391825251103/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B98.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 179 := by decide +kernel
  have hnil : rows.drop 184 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (189522048612234421/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b98_r000_c4]
    _ = (94559652465281097/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r008_c4,
        List.drop_drop]
      ring
    _ = (566153643139219003/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r016_c4,
        List.drop_drop]
      ring
    _ = (376635531084214479/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r024_c4,
        List.drop_drop]
      ring
    _ = (939594736860945163/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r032_c4,
        List.drop_drop]
      ring
    _ = (225025699056055993/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r040_c4,
        List.drop_drop]
      ring
    _ = (1309876125680546063/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r048_c4,
        List.drop_drop]
      ring
    _ = (1493841378602668481/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r056_c4,
        List.drop_drop]
      ring
    _ = (838513984503480101/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r064_c4,
        List.drop_drop]
      ring
    _ = (1859439578422369433/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r072_c4,
        List.drop_drop]
      ring
    _ = (81643194283748193/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r080_c4,
        List.drop_drop]
      ring
    _ = (1110976213054625543/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r088_c4,
        List.drop_drop]
      ring
    _ = (2402060879492385181/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r096_c4,
        List.drop_drop]
      ring
    _ = (645352196560518709/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r104_c4,
        List.drop_drop]
      ring
    _ = (1379999846154235691/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r112_c4,
        List.drop_drop]
      ring
    _ = (2937837122491184169/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r120_c4,
        List.drop_drop]
      ring
    _ = (3114924582249227613/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r128_c4,
        List.drop_drop]
      ring
    _ = (3291265559413050551/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 144) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 136)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r136_c4,
        List.drop_drop]
      ring
    _ = (866715881447619551/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 152) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 144)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r144_c4,
        List.drop_drop]
      ring
    _ = (182086096932990357/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 160) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 152)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r152_c4,
        List.drop_drop]
      ring
    _ = (3815844242144680721/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 168) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 160)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r160_c4,
        List.drop_drop]
      ring
    _ = (3989233868466726663/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 176) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 168)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r168_c4,
        List.drop_drop]
      ring
    _ = (2027033391825251103/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 184) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 176)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b98_r176_c4,
        List.drop_drop]
      ring
    _ = (2027033391825251103/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R36C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36)
      bflatExactSingletonBlocksJ5Seg0 =
      (378839126058924829714237/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R36_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b98_c0]
  norm_num

theorem bflatExactChargeJ5R36C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36)
      bflatExactSingletonBlocksJ5Seg1 =
      (71780354199731080494267/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R36_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b98_c1]
  norm_num

theorem bflatExactChargeJ5R36C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36)
      bflatExactSingletonBlocksJ5Seg2 =
      (56014961164900155871/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R36_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b98_c2]
  norm_num

theorem bflatExactChargeJ5R36C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36)
      bflatExactSingletonBlocksJ5Seg3 =
      (47125623775934748803/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R36_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b98_c3]
  norm_num

theorem bflatExactChargeJ5R36C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R36)
      bflatExactSingletonBlocksJ5Seg4 =
      (2027033391825251103/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R36_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b98_c4]
  norm_num

end ASDExplicitGamma.Model
