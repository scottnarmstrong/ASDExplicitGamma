module
public import ASDExplicitGamma.Model.BflatExactCapsJ5Meta
@[expose] public section
namespace ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Model

private theorem bflat_j5_tile_b77_r000_c0 :
    bflatChargeRowsFor ((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (596607004411043052988329/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r000_c1 :
    bflatChargeRowsFor ((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (1694214623196238874571/1250000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r000_c2 :
    bflatChargeRowsFor ((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (18924074860900973197/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r000_c3 :
    bflatChargeRowsFor ((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (2163438044780776459/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r000_c4 :
    bflatChargeRowsFor ((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (77491132369125311/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r008_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (300135748112503459813919/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r008_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (7085704677763629128117/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r008_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (3984725874511864043/2000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r008_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (1140266315911306223/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r008_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 8).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (163442628160952743/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r016_c0 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg0 =
      (301600067212762728202681/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r016_c1 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg1 =
      (14778203575029863385269/10000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r016_c2 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg2 =
      (10461733581396169869/5000000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r016_c3 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg3 =
      (599507523346485517/2500000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_tile_b77_r016_c4 :
    bflatChargeRowsFor (((bflatBlockJ5B77.entries.map bflatSingletonModeBlock).drop 16).take 8) bflatExactSingletonBlocksJ5Seg4 =
      (687766340444021/40000000000000000000000000 : ℚ) := by decide +kernel

private theorem bflat_j5_block_b77_c0 :
    bflatChargeRowsFor (bflatBlockJ5B77.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg0 =
      (1800078635061575429021529/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B77.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 24 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg0 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg0 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg0 8
    _ = (596607004411043052988329/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflat_j5_tile_b77_r000_c0]
    _ = (1196878500636049972616167/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b77_r008_c0,
        List.drop_drop]
      ring
    _ = (1800078635061575429021529/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg0 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg0 8, bflat_j5_tile_b77_r016_c0,
        List.drop_drop]
      ring
    _ = (1800078635061575429021529/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b77_c1 :
    bflatChargeRowsFor (bflatBlockJ5B77.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg1 =
      (42503329916127032638071/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B77.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 24 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg1 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg1 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg1 8
    _ = (1694214623196238874571/1250000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflat_j5_tile_b77_r000_c1]
    _ = (13862563170548584626401/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b77_r008_c1,
        List.drop_drop]
      ring
    _ = (42503329916127032638071/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg1 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg1 8, bflat_j5_tile_b77_r016_c1,
        List.drop_drop]
      ring
    _ = (42503329916127032638071/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b77_c2 :
    bflatChargeRowsFor (bflatBlockJ5B77.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg2 =
      (1195423427925052663/200000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B77.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 24 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg2 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg2 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg2 8
    _ = (18924074860900973197/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflat_j5_tile_b77_r000_c2]
    _ = (9711926058365073353/2500000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b77_r008_c2,
        List.drop_drop]
      ring
    _ = (1195423427925052663/200000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg2 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg2 8, bflat_j5_tile_b77_r016_c2,
        List.drop_drop]
      ring
    _ = (1195423427925052663/200000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b77_c3 :
    bflatChargeRowsFor (bflatBlockJ5B77.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg3 =
      (6842000769989330973/10000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B77.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 24 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg3 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg3 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg3 8
    _ = (2163438044780776459/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflat_j5_tile_b77_r000_c3]
    _ = (888794135320677781/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b77_r008_c3,
        List.drop_drop]
      ring
    _ = (6842000769989330973/10000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg3 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg3 8, bflat_j5_tile_b77_r016_c3,
        List.drop_drop]
      ring
    _ = (6842000769989330973/10000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

private theorem bflat_j5_block_b77_c4 :
    bflatChargeRowsFor (bflatBlockJ5B77.entries.map bflatSingletonModeBlock) bflatExactSingletonBlocksJ5Seg4 =
      (98073295602041723/2000000000000000000000000000 : ℚ) := by
  let rows : List ModeBlockData := (bflatBlockJ5B77.entries.map bflatSingletonModeBlock)
  have hlen : rows.length = 24 := by decide +kernel
  have hnil : rows.drop 24 = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  calc
    bflatChargeRowsFor rows bflatExactSingletonBlocksJ5Seg4 =
        bflatChargeRowsFor (rows.take 8) bflatExactSingletonBlocksJ5Seg4 +
          bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 :=
      bflatChargeRowsFor_split_rows rows bflatExactSingletonBlocksJ5Seg4 8
    _ = (77491132369125311/5000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 8) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflat_j5_tile_b77_r000_c4]
    _ = (63684978579840673/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 16) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 8)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b77_r008_c4,
        List.drop_drop]
      ring
    _ = (98073295602041723/2000000000000000000000000000 : ℚ) +
        bflatChargeRowsFor (rows.drop 24) bflatExactSingletonBlocksJ5Seg4 := by
      rw [bflatChargeRowsFor_split_rows (rows.drop 16)
        bflatExactSingletonBlocksJ5Seg4 8, bflat_j5_tile_b77_r016_c4,
        List.drop_drop]
      ring
    _ = (98073295602041723/2000000000000000000000000000 : ℚ) := by
      rw [hnil]
      simp [bflatChargeRowsFor]

theorem bflatExactChargeJ5R15C0 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15)
      bflatExactSingletonBlocksJ5Seg0 =
      (1800078635061575429021529/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R15_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b77_c0]
  norm_num

theorem bflatExactChargeJ5R15C1 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15)
      bflatExactSingletonBlocksJ5Seg1 =
      (42503329916127032638071/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R15_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b77_c1]
  norm_num

theorem bflatExactChargeJ5R15C2 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15)
      bflatExactSingletonBlocksJ5Seg2 =
      (1195423427925052663/200000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R15_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b77_c2]
  norm_num

theorem bflatExactChargeJ5R15C3 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15)
      bflatExactSingletonBlocksJ5Seg3 =
      (6842000769989330973/10000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R15_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b77_c3]
  norm_num

theorem bflatExactChargeJ5R15C4 :
    bflatChargeRowsFor (bflatSingletonModeBlocks bflatBlocksJ5R15)
      bflatExactSingletonBlocksJ5Seg4 =
      (98073295602041723/2000000000000000000000000000 : ℚ) := by
  rw [bflatChargeRowsFor_singletonBlocks_blocks]
  simp only [
    bflatBlocksJ5R15_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    bflat_j5_block_b77_c4]
  norm_num

end ASDExplicitGamma.Model
