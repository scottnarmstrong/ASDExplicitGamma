module
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part000
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part001
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part002
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part003
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part004
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part005
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part006
public import ASDExplicitGamma.Numerics.Model.ChargesJ2Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
theorem bflat_charge_j2 : blockCharge bflatBlocksJ2 = (717983155160369949570785527/5000000000000000000000000000 : ℚ) := by
  have hrows : bflatBlocksJ2.map (fun a => blockChargeRow a bflatBlocksJ2) = [(3832402918291771311771493/5000000000000000000000000000 : ℚ), (17650953148176637556768031/10000000000000000000000000000 : ℚ), (26259269545800733848779177/10000000000000000000000000000 : ℚ), (33531448027913716610316983/10000000000000000000000000000 : ℚ), (19778040551995665393194001/5000000000000000000000000000 : ℚ), (1388226115140578187794117/312500000000000000000000000 : ℚ), (1205599994514248802899999/250000000000000000000000000 : ℚ), (10210010703861752355898581/2000000000000000000000000000 : ℚ), (10598624431271432492345139/2000000000000000000000000000 : ℚ), (1692010592750303497826499/312500000000000000000000000 : ℚ), (54593547076951608036940339/10000000000000000000000000000 : ℚ), (6803571152073010359785787/1250000000000000000000000000 : ℚ), (13433618400084860409580233/2500000000000000000000000000 : ℚ), (52592862441388187556447763/10000000000000000000000000000 : ℚ), (10216241462818754217254007/2000000000000000000000000000 : ℚ), (4927225254815361396455911/1000000000000000000000000000 : ℚ), (9446700863269197525734243/2000000000000000000000000000 : ℚ), (45026819156206311667299003/10000000000000000000000000000 : ℚ), (8541620301578131019204737/2000000000000000000000000000 : ℚ), (40327115613940850311969577/10000000000000000000000000000 : ℚ), (4740926621078570588121281/1250000000000000000000000000 : ℚ), (35546372572721762737229979/10000000000000000000000000000 : ℚ), (33215347675911131199707157/10000000000000000000000000000 : ℚ), (619198191697020089970417/200000000000000000000000000 : ℚ), (900005517688022794464501/312500000000000000000000000 : ℚ), (13375606969065351589707399/5000000000000000000000000000 : ℚ), (12411745079499023248585373/5000000000000000000000000000 : ℚ), (11511686534114895705055781/5000000000000000000000000000 : ℚ), (1334603151620287490823441/625000000000000000000000000 : ℚ), (309594678742403419201367/156250000000000000000000000 : ℚ), (575056594629219700240917/312500000000000000000000000 : ℚ), (2139012006487883244897611/1250000000000000000000000000 : ℚ), (1593856253731303520570003/1000000000000000000000000000 : ℚ), (14873754958998646493420291/10000000000000000000000000000 : ℚ), (13909508790636897787811637/10000000000000000000000000000 : ℚ), (1629661964526148511027973/1250000000000000000000000000 : ℚ), (12248517007272300632257271/10000000000000000000000000000 : ℚ), (11534744543818743897662533/10000000000000000000000000000 : ℚ), (10887910721023694920411367/10000000000000000000000000000 : ℚ), (321889062266501282939749/312500000000000000000000000 : ℚ), (9765396020055680297624527/10000000000000000000000000000 : ℚ), (927643931251175245578767/1000000000000000000000000000 : ℚ), (176559016880764524324231/200000000000000000000000000 : ℚ), (1682995490487368017347737/2000000000000000000000000000 : ℚ), (2008303715324971366698177/2500000000000000000000000000 : ℚ), (1535792794966378544265131/2000000000000000000000000000 : ℚ), (7349075704073821489733051/10000000000000000000000000000 : ℚ), (7040889041370234205114931/10000000000000000000000000000 : ℚ), (844020806509908105897633/1250000000000000000000000000 : ℚ), (3240514971629517395817799/5000000000000000000000000000 : ℚ), (38911877748477469295633/62500000000000000000000000 : ℚ), (5985442385328232692000563/10000000000000000000000000000 : ℚ), (5758514820646146344318423/10000000000000000000000000000 : ℚ), (5544129594973767715604267/10000000000000000000000000000 : ℚ), (1068283372112821814762653/2000000000000000000000000000 : ℚ), (321849849251575113326467/625000000000000000000000000 : ℚ), (993592506034914979858617/2000000000000000000000000000 : ℚ), (1198964212164212984332683/2500000000000000000000000000 : ℚ), (4632669494513397898576427/10000000000000000000000000000 : ℚ), (1119456597508637289265707/2500000000000000000000000000 : ℚ), (4330786481211433492270489/10000000000000000000000000000 : ℚ), (4191039803245024441762371/10000000000000000000000000000 : ℚ), (2029053405457799449204061/5000000000000000000000000000 : ℚ), (7678785853259032707613/19531250000000000000000000 : ℚ)] := by
    change [blockChargeRow bflatBlockJ2B0 bflatBlocksJ2, blockChargeRow bflatBlockJ2B1 bflatBlocksJ2, blockChargeRow bflatBlockJ2B2 bflatBlocksJ2, blockChargeRow bflatBlockJ2B3 bflatBlocksJ2, blockChargeRow bflatBlockJ2B4 bflatBlocksJ2, blockChargeRow bflatBlockJ2B5 bflatBlocksJ2, blockChargeRow bflatBlockJ2B6 bflatBlocksJ2, blockChargeRow bflatBlockJ2B7 bflatBlocksJ2, blockChargeRow bflatBlockJ2B8 bflatBlocksJ2, blockChargeRow bflatBlockJ2B9 bflatBlocksJ2, blockChargeRow bflatBlockJ2B10 bflatBlocksJ2, blockChargeRow bflatBlockJ2B11 bflatBlocksJ2, blockChargeRow bflatBlockJ2B12 bflatBlocksJ2, blockChargeRow bflatBlockJ2B13 bflatBlocksJ2, blockChargeRow bflatBlockJ2B14 bflatBlocksJ2, blockChargeRow bflatBlockJ2B15 bflatBlocksJ2, blockChargeRow bflatBlockJ2B16 bflatBlocksJ2, blockChargeRow bflatBlockJ2B17 bflatBlocksJ2, blockChargeRow bflatBlockJ2B18 bflatBlocksJ2, blockChargeRow bflatBlockJ2B19 bflatBlocksJ2, blockChargeRow bflatBlockJ2B20 bflatBlocksJ2, blockChargeRow bflatBlockJ2B21 bflatBlocksJ2, blockChargeRow bflatBlockJ2B22 bflatBlocksJ2, blockChargeRow bflatBlockJ2B23 bflatBlocksJ2, blockChargeRow bflatBlockJ2B24 bflatBlocksJ2, blockChargeRow bflatBlockJ2B25 bflatBlocksJ2, blockChargeRow bflatBlockJ2B26 bflatBlocksJ2, blockChargeRow bflatBlockJ2B27 bflatBlocksJ2, blockChargeRow bflatBlockJ2B28 bflatBlocksJ2, blockChargeRow bflatBlockJ2B29 bflatBlocksJ2, blockChargeRow bflatBlockJ2B30 bflatBlocksJ2, blockChargeRow bflatBlockJ2B31 bflatBlocksJ2, blockChargeRow bflatBlockJ2B32 bflatBlocksJ2, blockChargeRow bflatBlockJ2B33 bflatBlocksJ2, blockChargeRow bflatBlockJ2B34 bflatBlocksJ2, blockChargeRow bflatBlockJ2B35 bflatBlocksJ2, blockChargeRow bflatBlockJ2B36 bflatBlocksJ2, blockChargeRow bflatBlockJ2B37 bflatBlocksJ2, blockChargeRow bflatBlockJ2B38 bflatBlocksJ2, blockChargeRow bflatBlockJ2B39 bflatBlocksJ2, blockChargeRow bflatBlockJ2B40 bflatBlocksJ2, blockChargeRow bflatBlockJ2B41 bflatBlocksJ2, blockChargeRow bflatBlockJ2B42 bflatBlocksJ2, blockChargeRow bflatBlockJ2B43 bflatBlocksJ2, blockChargeRow bflatBlockJ2B44 bflatBlocksJ2, blockChargeRow bflatBlockJ2B45 bflatBlocksJ2, blockChargeRow bflatBlockJ2B46 bflatBlocksJ2, blockChargeRow bflatBlockJ2B47 bflatBlocksJ2, blockChargeRow bflatBlockJ2B48 bflatBlocksJ2, blockChargeRow bflatBlockJ2B49 bflatBlocksJ2, blockChargeRow bflatBlockJ2B50 bflatBlocksJ2, blockChargeRow bflatBlockJ2B51 bflatBlocksJ2, blockChargeRow bflatBlockJ2B52 bflatBlocksJ2, blockChargeRow bflatBlockJ2B53 bflatBlocksJ2, blockChargeRow bflatBlockJ2B54 bflatBlocksJ2, blockChargeRow bflatBlockJ2B55 bflatBlocksJ2, blockChargeRow bflatBlockJ2B56 bflatBlocksJ2, blockChargeRow bflatBlockJ2B57 bflatBlocksJ2, blockChargeRow bflatBlockJ2B58 bflatBlocksJ2, blockChargeRow bflatBlockJ2B59 bflatBlocksJ2, blockChargeRow bflatBlockJ2B60 bflatBlocksJ2, blockChargeRow bflatBlockJ2B61 bflatBlocksJ2, blockChargeRow bflatBlockJ2B62 bflatBlocksJ2, blockChargeRow bflatBlockJ2B63 bflatBlocksJ2] = _
    rw [block_charge_row_j2_b0,
      block_charge_row_j2_b1,
      block_charge_row_j2_b2,
      block_charge_row_j2_b3,
      block_charge_row_j2_b4,
      block_charge_row_j2_b5,
      block_charge_row_j2_b6,
      block_charge_row_j2_b7,
      block_charge_row_j2_b8,
      block_charge_row_j2_b9,
      block_charge_row_j2_b10,
      block_charge_row_j2_b11,
      block_charge_row_j2_b12,
      block_charge_row_j2_b13,
      block_charge_row_j2_b14,
      block_charge_row_j2_b15,
      block_charge_row_j2_b16,
      block_charge_row_j2_b17,
      block_charge_row_j2_b18,
      block_charge_row_j2_b19,
      block_charge_row_j2_b20,
      block_charge_row_j2_b21,
      block_charge_row_j2_b22,
      block_charge_row_j2_b23,
      block_charge_row_j2_b24,
      block_charge_row_j2_b25,
      block_charge_row_j2_b26,
      block_charge_row_j2_b27,
      block_charge_row_j2_b28,
      block_charge_row_j2_b29,
      block_charge_row_j2_b30,
      block_charge_row_j2_b31,
      block_charge_row_j2_b32,
      block_charge_row_j2_b33,
      block_charge_row_j2_b34,
      block_charge_row_j2_b35,
      block_charge_row_j2_b36,
      block_charge_row_j2_b37,
      block_charge_row_j2_b38,
      block_charge_row_j2_b39,
      block_charge_row_j2_b40,
      block_charge_row_j2_b41,
      block_charge_row_j2_b42,
      block_charge_row_j2_b43,
      block_charge_row_j2_b44,
      block_charge_row_j2_b45,
      block_charge_row_j2_b46,
      block_charge_row_j2_b47,
      block_charge_row_j2_b48,
      block_charge_row_j2_b49,
      block_charge_row_j2_b50,
      block_charge_row_j2_b51,
      block_charge_row_j2_b52,
      block_charge_row_j2_b53,
      block_charge_row_j2_b54,
      block_charge_row_j2_b55,
      block_charge_row_j2_b56,
      block_charge_row_j2_b57,
      block_charge_row_j2_b58,
      block_charge_row_j2_b59,
      block_charge_row_j2_b60,
      block_charge_row_j2_b61,
      block_charge_row_j2_b62,
      block_charge_row_j2_b63]
  change (bflatBlocksJ2.map (fun a => blockChargeRow a bflatBlocksJ2)).sum = _
  rw [hrows]
  decide +kernel
theorem bflat_lower_j2 : blockLowerSum bflatBlocksJ2 = (9935585126662989094951/10000000000000000000000 : ℚ) := by
  decide +kernel
/-- Exact q3 covariance-integral cap, with a positive block majorant. -/
theorem bflat_cap_j2 : 2-2*q3Projection 2 64 < ((17/100 : ℚ) : ℝ) := by
  have h := block_certificate_sound 2 64 bflatBlocksJ2 block_cover_j2
    (List.all_eq_true.mp all_blocks_entries_j2) (List.all_eq_true.mp all_blocks_mass_j2)
  rw [bflat_lower_j2,bflat_charge_j2] at h
  have hc : (2-2*(9935585126662989094951/10000000000000000000000 : ℚ)^2+(717983155160369949570785527/5000000000000000000000000000 : ℚ) : ℚ) < (17/100 : ℚ) := by decide +kernel
  exact h.trans_lt (by exact_mod_cast hc)
end ASDExplicitGamma.Numerics.Model
