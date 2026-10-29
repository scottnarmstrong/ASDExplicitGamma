module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b90_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (24215138052813215878039/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1747734799278893382027/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (17280454666424922161/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4588204695525163413/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (174398085564314639/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (94730533858715435220791/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (13747282163019366786241/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (1068592522152627303/312500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4550212294715821049/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (3462642982408909/100000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (11582380294429164717191/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (540673801144543584017/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (16915736362659857133/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1128083795510014531/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (13749456771198073/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (22661273793742558317817/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2658129358139755015787/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8367712655280585417/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (447462807755988271/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (170608331770772619/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (22171915639829240231431/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (13068751619180779894457/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8278366505200266403/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (554642722740437359/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (338708880333297387/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (86785672621875562569991/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (12851208867775792266219/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (32759657619378057603/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4399923215298906613/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (168108320251985777/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (169876032564528378365227/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1579756736122394551973/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (32409731960733202037/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4363015469736324177/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (333743238995179169/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r056_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (41571776014101015282671/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r056_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (3107327211802499424573/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r056_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3206396430114987691/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r056_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4326457874115800381/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r056_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 56).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (41411462295002767/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r064_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (40700555250177903042521/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r064_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (2444996705426072989257/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r064_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (31722599549889340487/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r064_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4290286070813861509/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r064_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 64).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (82216193297725799/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r072_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (159418997793293906217899/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r072_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (601253806716968167269/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r072_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (31385853278663129403/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r072_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (4254532103205720357/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r072_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 72).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (163232477698440863/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r080_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (19617974238725895244757/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r080_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5938950235474770802871/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r080_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (15568142028807577907/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r080_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1056998392703005131/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b90_r080_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B90.entries.map bflatSingletonModeBlock).drop 80).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (162341635173519239/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b90_c0 :
    bflatChargeRowsFor (bflatBlockJ5B90.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (918796684966485142668919/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B90.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (24215138052813215878039/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b90_r000_c0]
    _ = (191591086069968298732947/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r008_c0,
        List.drop_drop]
      ring
    _ = (11370005137016064658819/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r016_c0,
        List.drop_drop]
      ring
    _ = (374895223600371849741743/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r024_c0,
        List.drop_drop]
      ring
    _ = (463582886159688810667467/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r032_c0,
        List.drop_drop]
      ring
    _ = (275184279390782186618729/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r040_c0,
        List.drop_drop]
      ring
    _ = (1270613150127657124840143/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r048_c0,
        List.drop_drop]
      ring
    _ = (1436900254184061185970827/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r056_c0,
        List.drop_drop]
      ring
    _ = (1599702475184772798140911/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r064_c0,
        List.drop_drop]
      ring
    _ = (175912147297806670435881/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r072_c0,
        List.drop_drop]
      ring
    _ = (918796684966485142668919/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b90_r080_c0,
        List.drop_drop]
      ring
    _ = (918796684966485142668919/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b90_c1 :
    bflatChargeRowsFor (bflatBlockJ5B90.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (27142597099330620778221/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B90.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (1747734799278893382027/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b90_r000_c1]
    _ = (27729160557250513842457/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r008_c1,
        List.drop_drop]
      ring
    _ = (20623002792932051721441/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r016_c1,
        List.drop_drop]
      ring
    _ = (54536652376562878521817/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r024_c1,
        List.drop_drop]
      ring
    _ = (33802701997871829208137/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r032_c1,
        List.drop_drop]
      ring
    _ = (80456612863519450682493/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r040_c1,
        List.drop_drop]
      ring
    _ = (93094666752498607098277/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r048_c1,
        List.drop_drop]
      ring
    _ = (105523975599708604796569/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r056_c1,
        List.drop_drop]
      ring
    _ = (58874479563419484871427/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r064_c1,
        List.drop_drop]
      ring
    _ = (64887017630589166544117/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r072_c1,
        List.drop_drop]
      ring
    _ = (27142597099330620778221/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b90_r080_c1,
        List.drop_drop]
      ring
    _ = (27142597099330620778221/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b90_c2 :
    bflatChargeRowsFor (bflatBlockJ5B90.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (345081608147598223911/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B90.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (17280454666424922161/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b90_r000_c2]
    _ = (34377935020866959009/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r008_c2,
        List.drop_drop]
      ring
    _ = (25646835691763408071/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r016_c2,
        List.drop_drop]
      ring
    _ = (2125909271690249593/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r024_c2,
        List.drop_drop]
      ring
    _ = (42292914852244259891/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r032_c2,
        List.drop_drop]
      ring
    _ = (201931317028355097167/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r040_c2,
        List.drop_drop]
      ring
    _ = (58585262247272074801/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r048_c2,
        List.drop_drop]
      ring
    _ = (133202506645119088057/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r056_c2,
        List.drop_drop]
      ring
    _ = (298127612840127516601/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r064_c2,
        List.drop_drop]
      ring
    _ = (82378366529697661501/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r072_c2,
        List.drop_drop]
      ring
    _ = (345081608147598223911/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b90_r080_c2,
        List.drop_drop]
      ring
    _ = (345081608147598223911/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b90_c3 :
    bflatChargeRowsFor (bflatBlockJ5B90.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (46310733550341047467/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B90.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (4588204695525163413/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b90_r000_c3]
    _ = (4569208495120492231/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r008_c3,
        List.drop_drop]
      ring
    _ = (6825376086140521293/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r016_c3,
        List.drop_drop]
      ring
    _ = (1132836265615057831/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r024_c3,
        List.drop_drop]
      ring
    _ = (2820315253970553021/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r032_c3,
        List.drop_drop]
      ring
    _ = (26962445247063330781/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r040_c3,
        List.drop_drop]
      ring
    _ = (15662730358399827479/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r048_c3,
        List.drop_drop]
      ring
    _ = (35651918590915455339/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r056_c3,
        List.drop_drop]
      ring
    _ = (2496387791358082303/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r064_c3,
        List.drop_drop]
      ring
    _ = (8839347352987007441/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r072_c3,
        List.drop_drop]
      ring
    _ = (46310733550341047467/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b90_r080_c3,
        List.drop_drop]
      ring
    _ = (46310733550341047467/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b90_c4 :
    bflatChargeRowsFor (bflatBlockJ5B90.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (110551417942024739/312500000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B90.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 84 := by decide +kernel
  have hnil : rows.drop 88 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (174398085564314639/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b90_r000_c4]
    _ = (347530234684760089/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r008_c4,
        List.drop_drop]
      ring
    _ = (1038796888649472003/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r016_c4,
        List.drop_drop]
      ring
    _ = (1380013552191017241/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r024_c4,
        List.drop_drop]
      ring
    _ = (429680608131078657/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r032_c4,
        List.drop_drop]
      ring
    _ = (1027469536514143091/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r040_c4,
        List.drop_drop]
      ring
    _ = (2388682312023465351/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r048_c4,
        List.drop_drop]
      ring
    _ = (2719974010383487487/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 64) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 56)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r056_c4,
        List.drop_drop]
      ring
    _ = (3048838783574390683/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 72) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 64)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r064_c4,
        List.drop_drop]
      ring
    _ = (3375303738971272409/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 80) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 72)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r072_c4,
        List.drop_drop]
      ring
    _ = (110551417942024739/312500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 88) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 80)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b90_r080_c4,
        List.drop_drop]
      ring
    _ = (110551417942024739/312500000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R28C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28)
      bflatExactSingletonBlocksJ5Seg0 =
      (918796684966485142668919/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R28_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b90_c0]
  norm_num

theorem bflatExactChargeJ5R28C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28)
      bflatExactSingletonBlocksJ5Seg1 =
      (27142597099330620778221/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R28_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b90_c1]
  norm_num

theorem bflatExactChargeJ5R28C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28)
      bflatExactSingletonBlocksJ5Seg2 =
      (345081608147598223911/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R28_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b90_c2]
  norm_num

theorem bflatExactChargeJ5R28C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28)
      bflatExactSingletonBlocksJ5Seg3 =
      (46310733550341047467/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R28_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b90_c3]
  norm_num

theorem bflatExactChargeJ5R28C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R28)
      bflatExactSingletonBlocksJ5Seg4 =
      (110551417942024739/312500000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R28_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b90_c4]
  norm_num

end ASDExplicitGamma.Model
