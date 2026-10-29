module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b99_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (15306525030247756891743/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2923882814536663869599/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11637036689607083941/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (198636918913313513/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (2693559059081091/156250000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1897671919306261237471/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1450878433005257517467/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (5783346772470423101/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1976616705305423861/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (10728950798795551/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (30115510545986514761731/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2879875478849083164327/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (229938491320752369/200000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (245865385945133297/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (6837681816761813/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (1493564027971975076311/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2858235204427801984803/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11427724482818474729/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1957288028517880599/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (1702242697954079/100000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (29630012837691740214571/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2836832664943569199103/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (141988601508982081/125000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1947711228957809487/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (33901975717679447/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (29391660523058088810497/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (281566455001586171169/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (11291010391809844303/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1938192396438105581/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (168798864936317467/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (728904444169939594601/250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (698681903357066332381/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (112234862862925507/100000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1928731243955299021/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (168091222321732797/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (28923519686175437147073/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (693504667504876708567/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (446260434576068043/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1919327488670540147/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (167386944460907261/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (14346821161790569151543/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2753534592731424894609/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (5545039624384154517/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1909980850703856619/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (166686025198837239/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (7116625651935493621513/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (546654461963932604219/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2756046654317137613/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (237586381500472297/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (165988458410474923/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (14148917857557520087087/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1359106282648520136517/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (5487550697904114527/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (473439768971165373/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b99_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B99.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (82733687619305289/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b99_c0 :
    bflatChargeRowsFor (bflatBlockJ5B99.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (309373025477425192703379/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B99.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (15306525030247756891743/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b99_r000_c0]
    _ = (30487900384697846791511/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r008_c0,
        List.drop_drop]
      ring
    _ = (91091311315382208344753/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r016_c0,
        List.drop_drop]
      ring
    _ = (120962591874821709870973/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r024_c0,
        List.drop_drop]
      ring
    _ = (18824075589064181260693/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r032_c0,
        List.drop_drop]
      ring
    _ = (179984265235571538896041/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r040_c0,
        List.drop_drop]
      ring
    _ = (209140443002369122680081/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r048_c0,
        List.drop_drop]
      ring
    _ = (119031981344272279913577/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r056_c0,
        List.drop_drop]
      ring
    _ = (833617515662892806657/31250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r064_c0,
        List.drop_drop]
      ring
    _ = (73806026904966918154073/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r072_c0,
        List.drop_drop]
      ring
    _ = (309373025477425192703379/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b99_r080_c0,
        List.drop_drop]
      ring
    _ = (309373025477425192703379/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b99_c1 :
    bflatChargeRowsFor (bflatBlockJ5B99.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (29630907047430875180469/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B99.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (2923882814536663869599/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b99_r000_c1]
    _ = (5825639680547178904533/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r008_c1,
        List.drop_drop]
      ring
    _ = (435275757969813103443/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r016_c1,
        List.drop_drop]
      ring
    _ = (11563750363824064053663/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r024_c1,
        List.drop_drop]
      ring
    _ = (7200291514383816626383/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r032_c1,
        List.drop_drop]
      ring
    _ = (2152030947347936870557/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r040_c1,
        List.drop_drop]
      ring
    _ = (1000548759610588014699/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r048_c1,
        List.drop_drop]
      ring
    _ = (2848124232778908391031/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r056_c1,
        List.drop_drop]
      ring
    _ = (25538528454962692022857/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r064_c1,
        List.drop_drop]
      ring
    _ = (1766987547798897190247/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r072_c1,
        List.drop_drop]
      ring
    _ = (29630907047430875180469/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b99_r080_c1,
        List.drop_drop]
      ring
    _ = (29630907047430875180469/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b99_c2 :
    bflatChargeRowsFor (bflatBlockJ5B99.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (118760291510567659893/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B99.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (11637036689607083941/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b99_r000_c2]
    _ = (23203730234547930143/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r008_c2,
        List.drop_drop]
      ring
    _ = (34700654800585548593/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r016_c2,
        List.drop_drop]
      ring
    _ = (23064189641702011661/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r024_c2,
        List.drop_drop]
      ring
    _ = (28743733702061294901/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r032_c2,
        List.drop_drop]
      ring
    _ = (13755695559186486821/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r040_c2,
        List.drop_drop]
      ring
    _ = (16000392816444996961/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r048_c2,
        List.drop_drop]
      ring
    _ = (2278961873665667147/250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r056_c2,
        List.drop_drop]
      ring
    _ = (51124277097697497457/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r064_c2,
        List.drop_drop]
      ring
    _ = (56636370406331772683/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r072_c2,
        List.drop_drop]
      ring
    _ = (118760291510567659893/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b99_r080_c2,
        List.drop_drop]
      ring
    _ = (118760291510567659893/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b99_c3 :
    bflatChargeRowsFor (bflatBlockJ5B99.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (20378710809189225943/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B99.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (198636918913313513/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b99_r000_c3]
    _ = (3962985894438558991/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r008_c3,
        List.drop_drop]
      ring
    _ = (5929908981999625367/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r016_c3,
        List.drop_drop]
      ring
    _ = (3943598505258752983/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r024_c3,
        List.drop_drop]
      ring
    _ = (9834908239475315453/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r032_c3,
        List.drop_drop]
      ring
    _ = (5886550317956710517/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r040_c3,
        List.drop_drop]
      ring
    _ = (2740366375973744011/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r048_c3,
        List.drop_drop]
      ring
    _ = (7810579684269630101/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r056_c3,
        List.drop_drop]
      ring
    _ = (17531140219243116821/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r064_c3,
        List.drop_drop]
      ring
    _ = (19431831271246895197/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r072_c3,
        List.drop_drop]
      ring
    _ = (20378710809189225943/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b99_r080_c3,
        List.drop_drop]
      ring
    _ = (20378710809189225943/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b99_c4 :
    bflatChargeRowsFor (bflatBlockJ5B99.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (443603097328086019/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B99.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (2693559059081091/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b99_r000_c4]
    _ = (4300637407023983/125000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r008_c4,
        List.drop_drop]
      ring
    _ = (102998607596192793/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r016_c4,
        List.drop_drop]
      ring
    _ = (137043461555274373/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r024_c4,
        List.drop_drop]
      ring
    _ = (8547271863647691/100000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r032_c4,
        List.drop_drop]
      ring
    _ = (1023526051301086567/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r040_c4,
        List.drop_drop]
      ring
    _ = (297904318405704841/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r048_c4,
        List.drop_drop]
      ring
    _ = (10872033744669813/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r056_c4,
        List.drop_drop]
      ring
    _ = (190711280410320483/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r064_c4,
        List.drop_drop]
      ring
    _ = (1691678701693038787/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r072_c4,
        List.drop_drop]
      ring
    _ = (443603097328086019/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b99_r080_c4,
        List.drop_drop]
      ring
    _ = (443603097328086019/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R37C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37)
      bflatExactSingletonBlocksJ5Seg0 =
      (309373025477425192703379/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R37_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b99_c0]
  norm_num

theorem bflatExactChargeJ5R37C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37)
      bflatExactSingletonBlocksJ5Seg1 =
      (29630907047430875180469/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R37_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b99_c1]
  norm_num

theorem bflatExactChargeJ5R37C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37)
      bflatExactSingletonBlocksJ5Seg2 =
      (118760291510567659893/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R37_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b99_c2]
  norm_num

theorem bflatExactChargeJ5R37C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37)
      bflatExactSingletonBlocksJ5Seg3 =
      (20378710809189225943/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R37_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b99_c3]
  norm_num

theorem bflatExactChargeJ5R37C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R37)
      bflatExactSingletonBlocksJ5Seg4 =
      (443603097328086019/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R37_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b99_c4]
  norm_num

end ASDExplicitGamma.Model
