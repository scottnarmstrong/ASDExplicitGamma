module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b85_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (455068406964486215369309/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (181678753762107640163/78125000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (267910094106399207/62500000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5200118661642892029/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (95206940310397831/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (111769041850378300726093/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (11577971453802850722641/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (8607758688340284009/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (5232159880107811179/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (383488657089159157/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (109766830594479304955821/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1440071856163673418301/625000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10795232241449996521/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2630304839920170741/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (38589342293908577/1000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r024_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (431053368123126119926139/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r024_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (22911291160953445955269/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r024_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (43292652771594222459/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r024_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1057103920502804757/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r024_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 24).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (388045190288175329/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r032_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (211522629344802355106179/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r032_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5691790928359266609541/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r032_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (43374653993981925303/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r032_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2653474249997064103/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r032_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 32).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (194973812653553329/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r040_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (51881676450488191323051/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r040_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (22609566814041433664389/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r040_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (2171383774744705803/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r040_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2662481060235730347/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r040_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 40).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (391604901404207981/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r048_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (40907512608177936586157/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r048_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (5620847028508351207847/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r048_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (21724880022205113893/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r048_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (133409423654287101/500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b85_r048_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B85.entries.map bflatSingletonModeBlock).drop 48).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (7853943066851147/400000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b85_c0 :
    bflatChargeRowsFor (bflatBlockJ5B85.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (562980299640288536350131/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B85.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 52 := by decide +kernel
  have hnil : rows.drop 56 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (455068406964486215369309/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b85_r000_c0]
    _ = (902144574365999418273681/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b85_r008_c0,
        List.drop_drop]
      ring
    _ = (268242379348783327619393/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b85_r016_c0,
        List.drop_drop]
      ring
    _ = (27691644763547543094111/156250000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b85_r024_c0,
        List.drop_drop]
      ring
    _ = (1097655261778323734117731/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b85_r032_c0,
        List.drop_drop]
      ring
    _ = (261036393516055299881987/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b85_r040_c0,
        List.drop_drop]
      ring
    _ = (562980299640288536350131/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b85_r048_c0,
        List.drop_drop]
      ring
    _ = (562980299640288536350131/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b85_c1 :
    bflatChargeRowsFor (bflatBlockJ5B85.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (74490844416611451276239/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B85.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 52 := by decide +kernel
  have hnil : rows.drop 56 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (181678753762107640163/78125000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b85_r000_c1]
    _ = (23205411694577739693073/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b85_r008_c1,
        List.drop_drop]
      ring
    _ = (34725986543887127039481/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b85_r016_c1,
        List.drop_drop]
      ring
    _ = (92363264248727700034231/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b85_r024_c1,
        List.drop_drop]
      ring
    _ = (23026085592432953294479/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b85_r032_c1,
        List.drop_drop]
      ring
    _ = (8608749673512887508549/625000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b85_r040_c1,
        List.drop_drop]
      ring
    _ = (74490844416611451276239/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b85_r048_c1,
        List.drop_drop]
      ring
    _ = (74490844416611451276239/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b85_c2 :
    bflatChargeRowsFor (bflatBlockJ5B85.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (70226299936800164241/2500000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B85.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 52 := by decide +kernel
  have hnil : rows.drop 56 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (267910094106399207/62500000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b85_r000_c2]
    _ = (17180881699745058633/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b85_r008_c2,
        List.drop_drop]
      ring
    _ = (129085337464525279249/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b85_r016_c2,
        List.drop_drop]
      ring
    _ = (43094497559029875427/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b85_r024_c2,
        List.drop_drop]
      ring
    _ = (215752644230101427011/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b85_r032_c2,
        List.drop_drop]
      ring
    _ = (259180319724995543071/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b85_r040_c2,
        List.drop_drop]
      ring
    _ = (70226299936800164241/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b85_r048_c2,
        List.drop_drop]
      ring
    _ = (70226299936800164241/2500000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b85_c3 :
    bflatChargeRowsFor (bflatBlockJ5B85.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (6855701383531279879/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B85.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 52 := by decide +kernel
  have hnil : rows.drop 56 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (5200118661642892029/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b85_r000_c3]
    _ = (1304034817718837901/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b85_r008_c3,
        List.drop_drop]
      ring
    _ = (1569288822159104469/1000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b85_r016_c3,
        List.drop_drop]
      ring
    _ = (839136312964202739/400000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b85_r024_c3,
        List.drop_drop]
      ring
    _ = (26285356324099196681/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b85_r032_c3,
        List.drop_drop]
      ring
    _ = (252882547556565259/80000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b85_r040_c3,
        List.drop_drop]
      ring
    _ = (6855701383531279879/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b85_r048_c3,
        List.drop_drop]
      ring
    _ = (6855701383531279879/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b85_c4 :
    bflatChargeRowsFor (bflatBlockJ5B85.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (1258078067470302447/5000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B85.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 52 := by decide +kernel
  have hnil : rows.drop 56 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (95206940310397831/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b85_r000_c4]
    _ = (764316418330750481/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b85_r008_c4,
        List.drop_drop]
      ring
    _ = (1150209841269836251/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b85_r016_c4,
        List.drop_drop]
      ring
    _ = (76912751577900579/500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 32) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 24)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b85_r024_c4,
        List.drop_drop]
      ring
    _ = (964101328432559119/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 40) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 32)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b85_r032_c4,
        List.drop_drop]
      ring
    _ = (2319807558269326219/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 48) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 40)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b85_r040_c4,
        List.drop_drop]
      ring
    _ = (1258078067470302447/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 56) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 48)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b85_r048_c4,
        List.drop_drop]
      ring
    _ = (1258078067470302447/5000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R23C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23)
      bflatExactSingletonBlocksJ5Seg0 =
      (562980299640288536350131/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R23_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b85_c0]
  norm_num

theorem bflatExactChargeJ5R23C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23)
      bflatExactSingletonBlocksJ5Seg1 =
      (74490844416611451276239/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R23_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b85_c1]
  norm_num

theorem bflatExactChargeJ5R23C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23)
      bflatExactSingletonBlocksJ5Seg2 =
      (70226299936800164241/2500000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R23_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b85_c2]
  norm_num

theorem bflatExactChargeJ5R23C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23)
      bflatExactSingletonBlocksJ5Seg3 =
      (6855701383531279879/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R23_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b85_c3]
  norm_num

theorem bflatExactChargeJ5R23C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R23)
      bflatExactSingletonBlocksJ5Seg4 =
      (1258078067470302447/5000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R23_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b85_c4]
  norm_num

end ASDExplicitGamma.Model
