module
public import ASDExplicitGamma.Numerics.Model.ChargesJ0Part000
public import ASDExplicitGamma.Numerics.Model.ChargesJ0Part001
public import ASDExplicitGamma.Numerics.Model.ChargesJ0Part002
public import ASDExplicitGamma.Numerics.Model.ChargesJ0Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
theorem bflat_charge_j0 : blockCharge bflatBlocksJ0 = (427676881796787397744738143/400000000000000000000000000 : ℚ) := by
  have hrows : bflatBlocksJ0.map (fun a => blockChargeRow a bflatBlocksJ0) = [(155318790599416893341082037/625000000000000000000000000 : ℚ), (2761033125707689797595716199/10000000000000000000000000000 : ℚ), (1664530033275083264828860599/10000000000000000000000000000 : ℚ), (18307288945193576808156159/200000000000000000000000000 : ℚ), (580227784331945026319338591/10000000000000000000000000000 : ℚ), (408224372687983730010556861/10000000000000000000000000000 : ℚ), (37874410564700688159132351/1250000000000000000000000000 : ℚ), (234219672022351135913598943/10000000000000000000000000000 : ℚ), (186505205182046247499923877/10000000000000000000000000000 : ℚ), (38015979973855469528156159/2500000000000000000000000000 : ℚ), (6317990143965247249107333/500000000000000000000000000 : ℚ), (3333423455836258676946749/312500000000000000000000000 : ℚ), (11406023077451979371034529/1250000000000000000000000000 : ℚ), (78945238998411848817159551/10000000000000000000000000000 : ℚ), (68972150470184668389903471/10000000000000000000000000000 : ℚ), (60775723806914317235819477/10000000000000000000000000000 : ℚ), (26978721270885282474447813/5000000000000000000000000000 : ℚ), (24112416318884909020506287/5000000000000000000000000000 : ℚ), (43359002005937784814400887/10000000000000000000000000000 : ℚ), (19596823766457739965283477/5000000000000000000000000000 : ℚ), (1424019594249234521246441/400000000000000000000000000 : ℚ), (32479351774643592371013383/10000000000000000000000000000 : ℚ), (14875522660861197468783291/5000000000000000000000000000 : ℚ), (6838081986877082453213401/2500000000000000000000000000 : ℚ), (630804619388242167869861/250000000000000000000000000 : ℚ), (291863826649862503907177/125000000000000000000000000 : ℚ), (21669032719356980198744993/10000000000000000000000000000 : ℚ), (4032762115567997439816391/2000000000000000000000000000 : ℚ), (4702500224002384325663751/2500000000000000000000000000 : ℚ), (8793982525535014334874759/5000000000000000000000000000 : ℚ), (3296229435602441862486091/2000000000000000000000000000 : ℚ), (1934439017463884318319/1250000000000000000000000 : ℚ)] := by
    change [blockChargeRow bflatBlockJ0B0 bflatBlocksJ0, blockChargeRow bflatBlockJ0B1 bflatBlocksJ0, blockChargeRow bflatBlockJ0B2 bflatBlocksJ0, blockChargeRow bflatBlockJ0B3 bflatBlocksJ0, blockChargeRow bflatBlockJ0B4 bflatBlocksJ0, blockChargeRow bflatBlockJ0B5 bflatBlocksJ0, blockChargeRow bflatBlockJ0B6 bflatBlocksJ0, blockChargeRow bflatBlockJ0B7 bflatBlocksJ0, blockChargeRow bflatBlockJ0B8 bflatBlocksJ0, blockChargeRow bflatBlockJ0B9 bflatBlocksJ0, blockChargeRow bflatBlockJ0B10 bflatBlocksJ0, blockChargeRow bflatBlockJ0B11 bflatBlocksJ0, blockChargeRow bflatBlockJ0B12 bflatBlocksJ0, blockChargeRow bflatBlockJ0B13 bflatBlocksJ0, blockChargeRow bflatBlockJ0B14 bflatBlocksJ0, blockChargeRow bflatBlockJ0B15 bflatBlocksJ0, blockChargeRow bflatBlockJ0B16 bflatBlocksJ0, blockChargeRow bflatBlockJ0B17 bflatBlocksJ0, blockChargeRow bflatBlockJ0B18 bflatBlocksJ0, blockChargeRow bflatBlockJ0B19 bflatBlocksJ0, blockChargeRow bflatBlockJ0B20 bflatBlocksJ0, blockChargeRow bflatBlockJ0B21 bflatBlocksJ0, blockChargeRow bflatBlockJ0B22 bflatBlocksJ0, blockChargeRow bflatBlockJ0B23 bflatBlocksJ0, blockChargeRow bflatBlockJ0B24 bflatBlocksJ0, blockChargeRow bflatBlockJ0B25 bflatBlocksJ0, blockChargeRow bflatBlockJ0B26 bflatBlocksJ0, blockChargeRow bflatBlockJ0B27 bflatBlocksJ0, blockChargeRow bflatBlockJ0B28 bflatBlocksJ0, blockChargeRow bflatBlockJ0B29 bflatBlocksJ0, blockChargeRow bflatBlockJ0B30 bflatBlocksJ0, blockChargeRow bflatBlockJ0B31 bflatBlocksJ0] = _
    rw [block_charge_row_j0_b0,
      block_charge_row_j0_b1,
      block_charge_row_j0_b2,
      block_charge_row_j0_b3,
      block_charge_row_j0_b4,
      block_charge_row_j0_b5,
      block_charge_row_j0_b6,
      block_charge_row_j0_b7,
      block_charge_row_j0_b8,
      block_charge_row_j0_b9,
      block_charge_row_j0_b10,
      block_charge_row_j0_b11,
      block_charge_row_j0_b12,
      block_charge_row_j0_b13,
      block_charge_row_j0_b14,
      block_charge_row_j0_b15,
      block_charge_row_j0_b16,
      block_charge_row_j0_b17,
      block_charge_row_j0_b18,
      block_charge_row_j0_b19,
      block_charge_row_j0_b20,
      block_charge_row_j0_b21,
      block_charge_row_j0_b22,
      block_charge_row_j0_b23,
      block_charge_row_j0_b24,
      block_charge_row_j0_b25,
      block_charge_row_j0_b26,
      block_charge_row_j0_b27,
      block_charge_row_j0_b28,
      block_charge_row_j0_b29,
      block_charge_row_j0_b30,
      block_charge_row_j0_b31]
  change (bflatBlocksJ0.map (fun a => blockChargeRow a bflatBlocksJ0)).sum = _
  rw [hrows]
  decide +kernel
theorem bflat_lower_j0 : blockLowerSum bflatBlocksJ0 = (493759100642544901389/500000000000000000000 : ℚ) := by
  decide +kernel
/-- Exact q3 covariance-integral cap, with a positive block majorant. -/
theorem bflat_cap_j0 : 2-2*q3Projection 0 32 < ((1119/1000 : ℚ) : ℝ) := by
  have h := block_certificate_sound 0 32 bflatBlocksJ0 block_cover_j0
    (List.all_eq_true.mp all_blocks_entries_j0) (List.all_eq_true.mp all_blocks_mass_j0)
  rw [bflat_lower_j0,bflat_charge_j0] at h
  have hc : (2-2*(493759100642544901389/500000000000000000000 : ℚ)^2+(427676881796787397744738143/400000000000000000000000000 : ℚ) : ℚ) < (1119/1000 : ℚ) := by decide +kernel
  exact h.trans_lt (by exact_mod_cast hc)
end ASDExplicitGamma.Numerics.Model
