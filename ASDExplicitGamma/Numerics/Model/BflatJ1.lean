module
public import ASDExplicitGamma.Numerics.Model.ChargesJ1Part000
public import ASDExplicitGamma.Numerics.Model.ChargesJ1Part001
public import ASDExplicitGamma.Numerics.Model.ChargesJ1Part002
public import ASDExplicitGamma.Numerics.Model.ChargesJ1Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
theorem bflat_charge_j1 : blockCharge bflatBlocksJ1 = (4196134736660985147874921551/10000000000000000000000000000 : ℚ) := by
  have hrows : bflatBlocksJ1.map (fun a => blockChargeRow a bflatBlocksJ1) = [(169978114812036851803538371/10000000000000000000000000000 : ℚ), (10606735693211671670029733/312500000000000000000000000 : ℚ), (212882086857113248336855559/5000000000000000000000000000 : ℚ), (448340730124970202487929069/10000000000000000000000000000 : ℚ), (21363106351991057255917631/500000000000000000000000000 : ℚ), (190307229064297707927132371/5000000000000000000000000000 : ℚ), (32311064005511888798032903/1000000000000000000000000000 : ℚ), (265349063199536035566659579/10000000000000000000000000000 : ℚ), (26723135640223350337212851/1250000000000000000000000000 : ℚ), (17131994979669599538204723/1000000000000000000000000000 : ℚ), (1382679771048813463478217/100000000000000000000000000 : ℚ), (56708819767973633619447733/5000000000000000000000000000 : ℚ), (94948186053339189874223527/10000000000000000000000000000 : ℚ), (40532587892522625058391803/5000000000000000000000000000 : ℚ), (70329947491602046072422061/10000000000000000000000000000 : ℚ), (61742266022394571102271367/10000000000000000000000000000 : ℚ), (54674235867689272027998379/10000000000000000000000000000 : ℚ), (6093723170954119283923421/1250000000000000000000000000 : ℚ), (4373401644665744406228443/1000000000000000000000000000 : ℚ), (1233135590447562635151661/312500000000000000000000000 : ℚ), (17897682798734806273784029/5000000000000000000000000000 : ℚ), (16313991411867019878913943/5000000000000000000000000000 : ℚ), (29867940427494771277559323/10000000000000000000000000000 : ℚ), (13722425625225701558979803/5000000000000000000000000000 : ℚ), (12652417475554305635167033/5000000000000000000000000000 : ℚ), (23405875146173066843969029/10000000000000000000000000000 : ℚ), (21713792749060676835489751/10000000000000000000000000000 : ℚ), (20199807143692407071798579/10000000000000000000000000000 : ℚ), (4709869752047722089892819/2500000000000000000000000000 : ℚ), (17612277659402978297125773/10000000000000000000000000000 : ℚ), (4125288317836635084103989/2500000000000000000000000000 : ℚ), (15491923887787479714875169/10000000000000000000000000000 : ℚ)] := by
    change [blockChargeRow bflatBlockJ1B0 bflatBlocksJ1, blockChargeRow bflatBlockJ1B1 bflatBlocksJ1, blockChargeRow bflatBlockJ1B2 bflatBlocksJ1, blockChargeRow bflatBlockJ1B3 bflatBlocksJ1, blockChargeRow bflatBlockJ1B4 bflatBlocksJ1, blockChargeRow bflatBlockJ1B5 bflatBlocksJ1, blockChargeRow bflatBlockJ1B6 bflatBlocksJ1, blockChargeRow bflatBlockJ1B7 bflatBlocksJ1, blockChargeRow bflatBlockJ1B8 bflatBlocksJ1, blockChargeRow bflatBlockJ1B9 bflatBlocksJ1, blockChargeRow bflatBlockJ1B10 bflatBlocksJ1, blockChargeRow bflatBlockJ1B11 bflatBlocksJ1, blockChargeRow bflatBlockJ1B12 bflatBlocksJ1, blockChargeRow bflatBlockJ1B13 bflatBlocksJ1, blockChargeRow bflatBlockJ1B14 bflatBlocksJ1, blockChargeRow bflatBlockJ1B15 bflatBlocksJ1, blockChargeRow bflatBlockJ1B16 bflatBlocksJ1, blockChargeRow bflatBlockJ1B17 bflatBlocksJ1, blockChargeRow bflatBlockJ1B18 bflatBlocksJ1, blockChargeRow bflatBlockJ1B19 bflatBlocksJ1, blockChargeRow bflatBlockJ1B20 bflatBlocksJ1, blockChargeRow bflatBlockJ1B21 bflatBlocksJ1, blockChargeRow bflatBlockJ1B22 bflatBlocksJ1, blockChargeRow bflatBlockJ1B23 bflatBlocksJ1, blockChargeRow bflatBlockJ1B24 bflatBlocksJ1, blockChargeRow bflatBlockJ1B25 bflatBlocksJ1, blockChargeRow bflatBlockJ1B26 bflatBlocksJ1, blockChargeRow bflatBlockJ1B27 bflatBlocksJ1, blockChargeRow bflatBlockJ1B28 bflatBlocksJ1, blockChargeRow bflatBlockJ1B29 bflatBlocksJ1, blockChargeRow bflatBlockJ1B30 bflatBlocksJ1, blockChargeRow bflatBlockJ1B31 bflatBlocksJ1] = _
    rw [block_charge_row_j1_b0,
      block_charge_row_j1_b1,
      block_charge_row_j1_b2,
      block_charge_row_j1_b3,
      block_charge_row_j1_b4,
      block_charge_row_j1_b5,
      block_charge_row_j1_b6,
      block_charge_row_j1_b7,
      block_charge_row_j1_b8,
      block_charge_row_j1_b9,
      block_charge_row_j1_b10,
      block_charge_row_j1_b11,
      block_charge_row_j1_b12,
      block_charge_row_j1_b13,
      block_charge_row_j1_b14,
      block_charge_row_j1_b15,
      block_charge_row_j1_b16,
      block_charge_row_j1_b17,
      block_charge_row_j1_b18,
      block_charge_row_j1_b19,
      block_charge_row_j1_b20,
      block_charge_row_j1_b21,
      block_charge_row_j1_b22,
      block_charge_row_j1_b23,
      block_charge_row_j1_b24,
      block_charge_row_j1_b25,
      block_charge_row_j1_b26,
      block_charge_row_j1_b27,
      block_charge_row_j1_b28,
      block_charge_row_j1_b29,
      block_charge_row_j1_b30,
      block_charge_row_j1_b31]
  change (bflatBlocksJ1.map (fun a => blockChargeRow a bflatBlocksJ1)).sum = _
  rw [hrows]
  decide +kernel
theorem bflat_lower_j1 : blockLowerSum bflatBlocksJ1 = (9874139282297751711771/10000000000000000000000 : ℚ) := by
  decide +kernel
/-- Exact q3 covariance-integral cap, with a positive block majorant. -/
theorem bflat_cap_j1 : 2-2*q3Projection 1 32 < ((47/100 : ℚ) : ℝ) := by
  have h := block_certificate_sound 1 32 bflatBlocksJ1 block_cover_j1
    (List.all_eq_true.mp all_blocks_entries_j1) (List.all_eq_true.mp all_blocks_mass_j1)
  rw [bflat_lower_j1,bflat_charge_j1] at h
  have hc : (2-2*(9874139282297751711771/10000000000000000000000 : ℚ)^2+(4196134736660985147874921551/10000000000000000000000000000 : ℚ) : ℚ) < (47/100 : ℚ) := by decide +kernel
  exact h.trans_lt (by exact_mod_cast hc)
end ASDExplicitGamma.Numerics.Model
