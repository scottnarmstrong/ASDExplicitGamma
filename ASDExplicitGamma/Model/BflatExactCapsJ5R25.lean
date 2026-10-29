module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b87_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (348108531687559970333491/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10403561624472076626299/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (42809585036477165357/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (334419373707246887/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (79304293888215597/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (340704121166825319824287/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10279862983110226654029/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (42629598477014826349/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5340305359776260913/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (79222896360583961/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (41674438267733306107143/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (20306890159230555347973/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (42430721304927578971/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5327495077263588817/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (395530228525675337/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (163093734437973246950239/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (10024640294399020846163/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (42214007273049325929/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5312392407533939543/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (394776556369353197/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (319084372114846937042439/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (791501618130957370427/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (20990255803385282451/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1323777977807905727/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (393861432582921561/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (312090171100628724639163/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2440286311815710910989/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (41731287507451584827/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (659471127404634003/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (392792915300043977/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (305208425849460364063657/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (19254128238951028123403/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10366845702022833201/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (262723981499602137/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (78315824927211981/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (52300604589692038702267/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (16625533265326073247563/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (9014181605687529463/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (915752769385086517/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b87_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B87.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (68305610362165563/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b87_c0 :
    bflatChargeRowsFor (bflatBlockJ5B87.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1273140809942797226085997/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B87.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 63 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (348108531687559970333491/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b87_r000_c0]
    _ = (344406326427192645078889/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r008_c0,
        List.drop_drop]
      ring
    _ = (511104079498125869507461/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r016_c0,
        List.drop_drop]
      ring
    _ = (6741978139360991164577/50000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r024_c0,
        List.drop_drop]
      ring
    _ = (1667479999987045169957839/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r032_c0,
        List.drop_drop]
      ring
    _ = (989785085543836947298501/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r040_c0,
        List.drop_drop]
      ring
    _ = (2284778596937134258660659/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r048_c0,
        List.drop_drop]
      ring
    _ = (1273140809942797226085997/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b87_r056_c0,
        List.drop_drop]
      ring
    _ = (1273140809942797226085997/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b87_c1 :
    bflatChargeRowsFor (bflatBlockJ5B87.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (39228128103817481630127/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B87.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 63 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (10403561624472076626299/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b87_r000_c1]
    _ = (2585428075947787910041/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r008_c1,
        List.drop_drop]
      ring
    _ = (61673739374395161908629/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r016_c1,
        List.drop_drop]
      ring
    _ = (16344603992638640720191/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r024_c1,
        List.drop_drop]
      ring
    _ = (10151056041646713786163/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r032_c1,
        List.drop_drop]
      ring
    _ = (60516425455496412574771/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r040_c1,
        List.drop_drop]
      ring
    _ = (28057395829988770654589/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r048_c1,
        List.drop_drop]
      ring
    _ = (39228128103817481630127/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b87_r056_c1,
        List.drop_drop]
      ring
    _ = (39228128103817481630127/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b87_c2 :
    bflatChargeRowsFor (bflatBlockJ5B87.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (331319820436532496991/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B87.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 63 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (42809585036477165357/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b87_r000_c2]
    _ = (42719591756745995853/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r008_c2,
        List.drop_drop]
      ring
    _ = (127869904818419570677/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r016_c2,
        List.drop_drop]
      ring
    _ = (85041956045734448303/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r024_c2,
        List.drop_drop]
      ring
    _ = (53016105924559865377/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r032_c2,
        List.drop_drop]
      ring
    _ = (50759142241138209267/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r040_c2,
        List.drop_drop]
      ring
    _ = (295263094013782379139/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r048_c2,
        List.drop_drop]
      ring
    _ = (331319820436532496991/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b87_r056_c2,
        List.drop_drop]
      ring
    _ = (331319820436532496991/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b87_c3 :
    bflatChargeRowsFor (bflatBlockJ5B87.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (20867513615637954861/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B87.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 63 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (334419373707246887/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b87_r000_c3]
    _ = (2138203067818442221/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r008_c3,
        List.drop_drop]
      ring
    _ = (8009255208177899961/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r016_c3,
        List.drop_drop]
      ring
    _ = (4266180564777947893/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r024_c3,
        List.drop_drop]
      ring
    _ = (26626014735121362373/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r032_c3,
        List.drop_drop]
      ring
    _ = (31901783754358434397/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r040_c3,
        List.drop_drop]
      ring
    _ = (37156263384350477137/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r048_c3,
        List.drop_drop]
      ring
    _ = (20867513615637954861/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b87_r056_c3,
        List.drop_drop]
      ring
    _ = (20867513615637954861/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b87_c4 :
    bflatChargeRowsFor (bflatBlockJ5B87.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (1551352130234439791/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B87.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 63 := by decide +kernel
  have hnil : rows.drop 64 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (79304293888215597/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b87_r000_c4]
    _ = (79263595124399779/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r008_c4,
        List.drop_drop]
      ring
    _ = (1188166179769673127/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r016_c4,
        List.drop_drop]
      ring
    _ = (395735684034756581/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r024_c4,
        List.drop_drop]
      ring
    _ = (395360833744389577/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r032_c4,
        List.drop_drop]
      ring
    _ = (1184798542010995931/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r040_c4,
        List.drop_drop]
      ring
    _ = (2761176208658051767/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r048_c4,
        List.drop_drop]
      ring
    _ = (1551352130234439791/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b87_r056_c4,
        List.drop_drop]
      ring
    _ = (1551352130234439791/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R25C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25)
      bflatExactSingletonBlocksJ5Seg0 =
      (1273140809942797226085997/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R25_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b87_c0]
  norm_num

theorem bflatExactChargeJ5R25C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25)
      bflatExactSingletonBlocksJ5Seg1 =
      (39228128103817481630127/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R25_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b87_c1]
  norm_num

theorem bflatExactChargeJ5R25C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25)
      bflatExactSingletonBlocksJ5Seg2 =
      (331319820436532496991/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R25_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b87_c2]
  norm_num

theorem bflatExactChargeJ5R25C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25)
      bflatExactSingletonBlocksJ5Seg3 =
      (20867513615637954861/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R25_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b87_c3]
  norm_num

theorem bflatExactChargeJ5R25C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R25)
      bflatExactSingletonBlocksJ5Seg4 =
      (1551352130234439791/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R25_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b87_c4]
  norm_num

end ASDExplicitGamma.Model
