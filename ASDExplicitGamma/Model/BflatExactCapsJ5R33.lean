module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b95_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (6684791909220328208189/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2941546073791615315879/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (9789193848899492753/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1488609367534414147/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (241750374980545711/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (66034809595618202459657/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5821442538793037385649/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2429615616553065627/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2961162743126287627/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (120341466960514153/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (16309111631971789140949/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1440179840036602072441/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (19296773935063408231/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2945208140544837277/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (239620720845011859/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1007069401113779434979/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5700901804202538573749/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3831582111495370057/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2929352603574250029/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (238563567601479237/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (63682425163588492164333/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (225678805834026672649/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (475507824234047033/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1456797069604079367/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (59377833156425869/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (31463022159370801396279/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (697988208263280003409/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (9441980735807599313/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2897931059558914551/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (236463898971059617/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (3109148124945364504449/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2763345289262662987537/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1874883831262109011/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1441180978183696623/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (58855293084799323/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (12290571607763127397549/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5470307958436497793359/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (18614927508547081433/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (57337713516163471/200000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (46876615824362687/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (60735423222837668609673/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (676842709394669648257/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1848221466853263003/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2851501293737524981/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (233349564466308299/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (12006072663002428794319/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2679988163666058204193/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (18350686825558763019/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2836208091518507923/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (7260018449269679/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (29668697820978422240779/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (331624823843588424437/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1822033227369095199/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (705251383136089037/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (115648066929810237/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r088_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (58656248728345839727969/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r088_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1313197528488943632607/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r088_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3618228082458780957/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r088_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2805893239568213079/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r088_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 88).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (230276185126187523/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r096_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (28993330742199870576883/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r096_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2600170778004964321509/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r096_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (17963101597726038511/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r096_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (27908709729343523/100000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r096_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 96).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (114630372927808739/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r104_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (57328382444619183847169/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r104_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5148638442586626872241/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r104_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (445905175073331347/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r104_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (555187721958650071/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r104_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 104).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (114124913765185979/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r112_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (56681169056794288588937/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r112_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (40781345314044927307/80000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r112_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (141683587882216919/80000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r112_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1380548062185221037/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r112_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 112).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (227243449847724901/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r120_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (56044787020142595096263/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r120_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5047418522628143649221/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r120_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8792909231425686349/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r120_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (137317178467347347/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r120_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 120).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (226241639213644081/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r128_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (9705099725611138445729/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r128_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (4375828299600698590393/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r128_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15286237295350119489/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r128_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (597754925196937817/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b95_r128_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B95.entries.map bflatSingletonModeBlock).drop 128).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (24642906361378329/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b95_c0 :
    bflatChargeRowsFor (bflatBlockJ5B95.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (102814183644920754468319/1000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B95.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 135 := by decide +kernel
  have hnil : rows.drop 136 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (6684791909220328208189/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b95_r000_c0]
    _ = (132882728687821484541547/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r008_c0,
        List.drop_drop]
      ring
    _ = (198119175215708641105343/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r016_c0,
        List.drop_drop]
      ring
    _ = (262571616886990524943999/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r024_c0,
        List.drop_drop]
      ring
    _ = (81563510512644754277083/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r032_c0,
        List.drop_drop]
      ring
    _ = (38918008636932061990089/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r040_c0,
        List.drop_drop]
      ring
    _ = (45136304886822790998987/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r048_c0,
        List.drop_drop]
      ring
    _ = (102563181381408709395523/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r056_c0,
        List.drop_drop]
      ring
    _ = (71693916266235151948411/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r064_c0,
        List.drop_drop]
      ring
    _ = (633581693444893359558883/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r072_c0,
        List.drop_drop]
      ring
    _ = (692919089086850204040441/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r080_c0,
        List.drop_drop]
      ring
    _ = (75157533781519604376841/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r088_c0,
        List.drop_drop]
      ring
    _ = (12649406239056184139409/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r096_c0,
        List.drop_drop]
      ring
    _ = (173378076348842993753869/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r104_c0,
        List.drop_drop]
      ring
    _ = (461785775400504628679141/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r112_c0,
        List.drop_drop]
      ring
    _ = (195923267564230370490909/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r120_c0,
        List.drop_drop]
      ring
    _ = (102814183644920754468319/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b95_r128_c0,
        List.drop_drop]
      ring
    _ = (102814183644920754468319/1000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b95_c1 :
    bflatChargeRowsFor (bflatBlockJ5B95.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (572452690516672637981/62500000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B95.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 135 := by decide +kernel
  have hnil : rows.drop 136 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (2941546073791615315879/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b95_r000_c1]
    _ = (11704534686376268017407/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r008_c1,
        List.drop_drop]
      ring
    _ = (17465254046522676307171/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r016_c1,
        List.drop_drop]
      ring
    _ = (579153896268130372023/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r024_c1,
        List.drop_drop]
      ring
    _ = (5761625199315176339429/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r032_c1,
        List.drop_drop]
      ring
    _ = (34392031662682121724417/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r040_c1,
        List.drop_drop]
      ring
    _ = (39918722241207447699491/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r048_c1,
        List.drop_drop]
      ring
    _ = (907780603992878909857/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r056_c1,
        List.drop_drop]
      ring
    _ = (25401885937400651339453/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r064_c1,
        List.drop_drop]
      ring
    _ = (14040937050533354771823/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r072_c1,
        List.drop_drop]
      ring
    _ = (15367436345907708469571/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r080_c1,
        List.drop_drop]
      ring
    _ = (8340316937198326051089/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r088_c1,
        List.drop_drop]
      ring
    _ = (7192287705359653705173/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r096_c1,
        List.drop_drop]
      ring
    _ = (77071515496183163923971/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r104_c1,
        List.drop_drop]
      ring
    _ = (41084591830219389918673/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r112_c1,
        List.drop_drop]
      ring
    _ = (87216602183066923486567/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r120_c1,
        List.drop_drop]
      ring
    _ = (572452690516672637981/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b95_r128_c1,
        List.drop_drop]
      ring
    _ = (572452690516672637981/62500000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b95_c2 :
    bflatChargeRowsFor (bflatBlockJ5B95.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (78066056102280792451/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B95.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 135 := by decide +kernel
  have hnil : rows.drop 136 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (9789193848899492753/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b95_r000_c2]
    _ = (19507656315111755261/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r008_c2,
        List.drop_drop]
      ring
    _ = (58312086565286918753/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r016_c2,
        List.drop_drop]
      ring
    _ = (38734998561381884519/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r024_c2,
        List.drop_drop]
      ring
    _ = (48245155046062825179/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r032_c2,
        List.drop_drop]
      ring
    _ = (14421783945467606123/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r040_c2,
        List.drop_drop]
      ring
    _ = (67061554938180969547/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r048_c2,
        List.drop_drop]
      ring
    _ = (152738037384909020527/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r056_c2,
        List.drop_drop]
      ring
    _ = (171220252053441650557/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r064_c2,
        List.drop_drop]
      ring
    _ = (23696367359875051697/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r072_c2,
        List.drop_drop]
      ring
    _ = (103895635576345682783/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r080_c2,
        List.drop_drop]
      ring
    _ = (225882411564985270351/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r088_c2,
        List.drop_drop]
      ring
    _ = (121922756581355654431/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r096_c2,
        List.drop_drop]
      ring
    _ = (130840860082822281371/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r104_c2,
        List.drop_drop]
      ring
    _ = (279392168650921677617/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r112_c2,
        List.drop_drop]
      ring
    _ = (59395597422754610063/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r120_c2,
        List.drop_drop]
      ring
    _ = (78066056102280792451/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b95_r128_c2,
        List.drop_drop]
      ring
    _ = (78066056102280792451/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b95_c3 :
    bflatChargeRowsFor (bflatBlockJ5B95.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (6019199023482273547/1250000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B95.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 135 := by decide +kernel
  have hnil : rows.drop 136 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (1488609367534414147/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b95_r000_c3]
    _ = (5938381478195115921/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r008_c3,
        List.drop_drop]
      ring
    _ = (4441794809369976599/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r016_c3,
        List.drop_drop]
      ring
    _ = (11812942222314203227/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r024_c3,
        List.drop_drop]
      ring
    _ = (14726536361522361961/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r032_c3,
        List.drop_drop]
      ring
    _ = (550764606908789891/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r040_c3,
        List.drop_drop]
      ring
    _ = (10253414688724334879/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r048_c3,
        List.drop_drop]
      ring
    _ = (5843428763314210827/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r056_c3,
        List.drop_drop]
      ring
    _ = (26225216346994368289/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r064_c3,
        List.drop_drop]
      ring
    _ = (7265356109628219053/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r072_c3,
        List.drop_drop]
      ring
    _ = (797060749276430809/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r080_c3,
        List.drop_drop]
      ring
    _ = (34688323210625445439/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r088_c3,
        List.drop_drop]
      ring
    _ = (37479194183559797739/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r096_c3,
        List.drop_drop]
      ring
    _ = (20127566396676524047/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r104_c3,
        List.drop_drop]
      ring
    _ = (5377028614715436271/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r112_c3,
        List.drop_drop]
      ring
    _ = (11440643121767609277/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r120_c3,
        List.drop_drop]
      ring
    _ = (6019199023482273547/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b95_r128_c3,
        List.drop_drop]
      ring
    _ = (6019199023482273547/1250000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b95_c4 :
    bflatChargeRowsFor (bflatBlockJ5B95.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (3939778467572970007/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B95.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 135 := by decide +kernel
  have hnil : rows.drop 136 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (241750374980545711/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b95_r000_c4]
    _ = (482433308901574017/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r008_c4,
        List.drop_drop]
      ring
    _ = (180513507436646469/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r016_c4,
        List.drop_drop]
      ring
    _ = (960617597348065113/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r024_c4,
        List.drop_drop]
      ring
    _ = (1198128929973768589/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r032_c4,
        List.drop_drop]
      ring
    _ = (717296414472414103/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r040_c4,
        List.drop_drop]
      ring
    _ = (835007000642012749/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r048_c4,
        List.drop_drop]
      ring
    _ = (1904397080405838933/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r056_c4,
        List.drop_drop]
      ring
    _ = (66804582652254601/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r064_c4,
        List.drop_drop]
      ring
    _ = (1851615027538107/7812500000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r072_c4,
        List.drop_drop]
      ring
    _ = (1300681684554198717/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r080_c4,
        List.drop_drop]
      ring
    _ = (2831639554234584957/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 96) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 88)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r088_c4,
        List.drop_drop]
      ring
    _ = (612180060018040487/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 104) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 96)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r096_c4,
        List.drop_drop]
      ring
    _ = (3289150127620574393/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 112) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 104)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r104_c4,
        List.drop_drop]
      ring
    _ = (1758196788734149647/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 120) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 112)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r112_c4,
        List.drop_drop]
      ring
    _ = (29941081733455547/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 128) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 120)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r120_c4,
        List.drop_drop]
      ring
    _ = (3939778467572970007/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 136) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 128)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b95_r128_c4,
        List.drop_drop]
      ring
    _ = (3939778467572970007/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R33C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33)
      bflatExactSingletonBlocksJ5Seg0 =
      (102814183644920754468319/1000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R33_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b95_c0]
  norm_num

theorem bflatExactChargeJ5R33C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33)
      bflatExactSingletonBlocksJ5Seg1 =
      (572452690516672637981/62500000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R33_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b95_c1]
  norm_num

theorem bflatExactChargeJ5R33C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33)
      bflatExactSingletonBlocksJ5Seg2 =
      (78066056102280792451/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R33_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b95_c2]
  norm_num

theorem bflatExactChargeJ5R33C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33)
      bflatExactSingletonBlocksJ5Seg3 =
      (6019199023482273547/1250000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R33_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b95_c3]
  norm_num

theorem bflatExactChargeJ5R33C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R33)
      bflatExactSingletonBlocksJ5Seg4 =
      (3939778467572970007/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R33_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b95_c4]
  norm_num

end ASDExplicitGamma.Model
