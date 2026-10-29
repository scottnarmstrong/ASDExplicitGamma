module

public import ASDExplicitGamma.Model.BflatExactCapsData
public import ASDExplicitGamma.Model.BflatExactCapsJ4Rows
public import ASDExplicitGamma.Model.BflatExactCapsJ3Rows
public import ASDExplicitGamma.Model.BflatExactCapsJ5Rows
public import ASDExplicitGamma.Numerics.Model.BlockListJ3

/-! # Exact finite source caps for the actual q3 projected energy -/

@[expose] public section

namespace ASDExplicitGamma.Model

open ASDExplicitGamma.Numerics.Model

private theorem bflat_projection_exact_cap_j0 :
    2 - 2 * q3Projection 0 32 <
      ((559403904376645107821 / 500000000000000000000 : ℚ) : ℝ) := by
  have hcert := block_certificate_sound 0 32 bflatBlocksJ0
    block_cover_j0
    (fun b hb => List.all_eq_true.mp all_blocks_entries_j0 b hb)
    (fun b hb => List.all_eq_true.mp all_blocks_mass_j0 b hb)
  rw [bflat_lower_j0, bflat_charge_j0] at hcert
  have hc :
      (2 - 2 * (493759100642544901389 / 500000000000000000000 : ℚ) ^ 2 +
        427676881796787397744738143 / 400000000000000000000000000 : ℚ) <
        559403904376645107821 / 500000000000000000000 := by
    norm_num
  exact hcert.trans_lt (by exact_mod_cast hc)

private theorem bflat_projection_exact_cap_j1 :
    2 - 2 * q3Projection 1 32 <
      ((2348204711708936647311 / 5000000000000000000000 : ℚ) : ℝ) := by
  have hcert := block_certificate_sound 1 32 bflatBlocksJ1
    block_cover_j1
    (fun b hb => List.all_eq_true.mp all_blocks_entries_j1 b hb)
    (fun b hb => List.all_eq_true.mp all_blocks_mass_j1 b hb)
  rw [bflat_lower_j1, bflat_charge_j1] at hcert
  have hc :
      (2 - 2 * (9874139282297751711771 / 10000000000000000000000 : ℚ) ^ 2 +
        4196134736660985147874921551 / 10000000000000000000000000000 : ℚ) <
        2348204711708936647311 / 5000000000000000000000 := by
    norm_num
  exact hcert.trans_lt (by exact_mod_cast hc)

private theorem bflat_projection_exact_cap_j2 :
    2 - 2 * q3Projection 2 64 <
      ((423198987121844722901 / 2500000000000000000000 : ℚ) : ℝ) := by
  have hcert := block_certificate_sound 2 64 bflatBlocksJ2
    block_cover_j2
    (fun b hb => List.all_eq_true.mp all_blocks_entries_j2 b hb)
    (fun b hb => List.all_eq_true.mp all_blocks_mass_j2 b hb)
  rw [bflat_lower_j2, bflat_charge_j2] at hcert
  have hc :
      (2 - 2 * (9935585126662989094951 / 10000000000000000000000 : ℚ) ^ 2 +
        717983155160369949570785527 / 5000000000000000000000000000 : ℚ) <
        423198987121844722901 / 2500000000000000000000 := by
    norm_num
  exact hcert.trans_lt (by exact_mod_cast hc)

private theorem bflat_projection_exact_cap_j3 :
    2 - 2 * q3Projection 3 256 <
      ((144329642328994216417 / 2500000000000000000000 : ℚ) : ℝ) := by
  have hcert := block_certificate_sound 3 256 bflatExactSingletonBlocksJ3
    (bflatSingleton_blocks_cover block_cover_j3
      (fun b hb => List.all_eq_true.mp all_blocks_mass_j3 b hb))
    (bflatSingleton_blocks_entries_checked (fun b hb =>
      List.all_eq_true.mp all_blocks_entries_j3 b hb))
    (bflatSingleton_blocks_mass_checked (fun b hb =>
      List.all_eq_true.mp all_blocks_entries_j3 b hb))
  rw [bflatExactLowerSumJ3,
    show blockCharge bflatExactSingletonBlocksJ3 = bflatExactChargeRowsJ3.sum by rfl,
    bflat_exact_charge_j3_total] at hcert
  have hc :
      (2 - 2 * (1996796649127349043391 / 2000000000000000000000 : ℚ) ^ 2 +
        256651429573512118405969381 / 5000000000000000000000000000 : ℚ) <
        144329642328994216417 / 2500000000000000000000 := by
    norm_num
  exact hcert.trans_lt (by exact_mod_cast hc)

private theorem bflat_projection_exact_cap_j4 :
    2 - 2 * q3Projection 4 512 <
      ((3055492116062002119 / 156250000000000000000 : ℚ) : ℝ) := by
  have hcert := block_certificate_sound 4 512 bflatExactSingletonBlocksJ4
    (bflatSingleton_blocks_cover block_cover_j4
      (fun b hb => List.all_eq_true.mp all_blocks_mass_j4 b hb))
    (bflatSingleton_blocks_entries_checked (fun b hb =>
      List.all_eq_true.mp all_blocks_entries_j4 b hb))
    (bflatSingleton_blocks_mass_checked (fun b hb =>
      List.all_eq_true.mp all_blocks_entries_j4 b hb))
  rw [bflatExactLowerSumJ4,
    show blockCharge bflatExactSingletonBlocksJ4 = bflatExactChargeRowsJ4.sum by rfl,
    bflat_exact_charge_j4_total] at hcert
  have hc :
      (2 - 2 * (9991631911802854962809 / 10000000000000000000000 : ℚ) ^ 2 +
        81046573809701382518989531 / 5000000000000000000000000000 : ℚ) <
        3055492116062002119 / 156250000000000000000 := by
    norm_num
  exact hcert.trans_lt (by exact_mod_cast hc)

private theorem bflat_projection_exact_cap_j5 :
    2 - 2 * q3Projection 5 2048 <
      ((32510441860151370407 / 5000000000000000000000 : ℚ) : ℝ) := by
  have hmass : ∀ b ∈ bflatBlocksJ5, blockMassCheck b = true := by
    intro b hb
    exact List.all_eq_true.mp all_blocks_mass_j5 b hb
  have hentries : ∀ b ∈ bflatBlocksJ5, entryChecks 5 b.entries = true := by
    intro b hb
    exact List.all_eq_true.mp all_blocks_entries_j5 b hb
  have hcert := block_certificate_sound 5 2048 bflatExactSingletonBlocksJ5
    (bflatSingleton_blocks_cover block_cover_j5 hmass)
    (bflatSingleton_blocks_entries_checked hentries)
    (bflatSingleton_blocks_mass_checked hentries)
  have hlower := bflat_lowerSum_le_singletonBlocks hmass
  rw [bflat_lower_j5] at hlower
  have hsource0 :
      (0 : ℚ) ≤ 9997956762112368149281 / 10000000000000000000000 := by norm_num
  have hsingle0 : (0 : ℚ) ≤ blockLowerSum bflatExactSingletonBlocksJ5 :=
    le_trans hsource0 hlower
  rw [bflat_exact_charge_j5_total] at hcert
  have hlowerExact :
      (9997956762112368149281 / 10000000000000000000000 : ℚ) ≤
        blockLowerSum bflatExactSingletonBlocksJ5 := by
    simpa [bflatExactSingletonBlocksJ5] using hlower
  have hsquare :
      (9997956762112368149281 / 10000000000000000000000 : ℚ)^2 ≤
        (blockLowerSum bflatExactSingletonBlocksJ5)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlowerExact)
      (add_nonneg hsource0 hsingle0)]
  have hcompare :
      (2 - 2 * (blockLowerSum bflatExactSingletonBlocksJ5)^2 +
        (14212191783496059642525039 / 2500000000000000000000000000 : ℚ)) ≤
      (2 - 2 * (9997956762112368149281 / 10000000000000000000000 : ℚ)^2 +
        (14212191783496059642525039 / 2500000000000000000000000000 : ℚ)) := by
    linarith [hsquare]
  have hcompareR :
      ((2 - 2 * (blockLowerSum bflatExactSingletonBlocksJ5)^2 +
        (14212191783496059642525039 / 2500000000000000000000000000 : ℚ) : ℚ) : ℝ) ≤
      ((2 - 2 * (9997956762112368149281 / 10000000000000000000000 : ℚ)^2 +
        (14212191783496059642525039 / 2500000000000000000000000000 : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hcompare
  have hcap :
      (2 - 2 * (9997956762112368149281 / 10000000000000000000000 : ℚ)^2 +
        (14212191783496059642525039 / 2500000000000000000000000000 : ℚ) : ℚ) <
        32510441860151370407 / 5000000000000000000000 := by
    norm_num
  exact lt_of_le_of_lt (le_trans hcert hcompareR) (by exact_mod_cast hcap)

/-- Public exact-grid projection certificates used by the native affine
boundary comparison. -/
theorem bflat_projection_exact_cap_j0' :
    2 - 2 * q3Projection 0 32 <
      ((559403904376645107821 / 500000000000000000000 : ℚ) : ℝ) :=
  bflat_projection_exact_cap_j0

theorem bflat_projection_exact_cap_j1' :
    2 - 2 * q3Projection 1 32 <
      ((2348204711708936647311 / 5000000000000000000000 : ℚ) : ℝ) :=
  bflat_projection_exact_cap_j1

theorem bflat_projection_exact_cap_j2' :
    2 - 2 * q3Projection 2 64 <
      ((423198987121844722901 / 2500000000000000000000 : ℚ) : ℝ) :=
  bflat_projection_exact_cap_j2

theorem bflat_projection_exact_cap_j3' :
    2 - 2 * q3Projection 3 256 <
      ((144329642328994216417 / 2500000000000000000000 : ℚ) : ℝ) :=
  bflat_projection_exact_cap_j3

theorem bflat_projection_exact_cap_j4' :
    2 - 2 * q3Projection 4 512 <
      ((3055492116062002119 / 156250000000000000000 : ℚ) : ℝ) :=
  bflat_projection_exact_cap_j4

theorem bflat_projection_exact_cap_j5' :
    2 - 2 * q3Projection 5 2048 <
      ((32510441860151370407 / 5000000000000000000000 : ℚ) : ℝ) :=
  bflat_projection_exact_cap_j5

end ASDExplicitGamma.Model
