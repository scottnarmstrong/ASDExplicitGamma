module
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part000
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part001
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part002
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part003
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part004
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part005
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part006
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part007
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part008
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part009
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part010
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part011
public import ASDExplicitGamma.Numerics.Model.ChargesJ4Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
theorem bflat_charge_j4 : blockCharge bflatBlocksJ4 = (8203060553804829142322999/500000000000000000000000000 : ℚ) := by
  have hrows : bflatBlocksJ4.map (fun a => blockChargeRow a bflatBlocksJ4) = [(11467355388854854122081/10000000000000000000000000000 : ℚ), (27948840793489064045669/10000000000000000000000000000 : ℚ), (44253448102160837565089/10000000000000000000000000000 : ℚ), (30160049780214951478731/5000000000000000000000000000 : ℚ), (38075010825124073912983/5000000000000000000000000000 : ℚ), (22936163611906587179901/2500000000000000000000000000 : ℚ), (53552709922213776318473/5000000000000000000000000000 : ℚ), (122233721810327098139407/10000000000000000000000000000 : ℚ), (68565473710633423141569/5000000000000000000000000000 : ℚ), (30359693598699442326189/2000000000000000000000000000 : ℚ), (166237640308837047181481/10000000000000000000000000000 : ℚ), (4511245197938083620647/250000000000000000000000000 : ℚ), (19443630250441105963873/1000000000000000000000000000 : ℚ), (6506201415747731046657/312500000000000000000000000 : ℚ), (22173754854908376009751/1000000000000000000000000000 : ℚ), (58763729234997913337683/2500000000000000000000000000 : ℚ), (124075924558849849600481/5000000000000000000000000000 : ℚ), (261029639129747500153283/10000000000000000000000000000 : ℚ), (136844788937296571183919/5000000000000000000000000000 : ℚ), (17883309657061773149691/625000000000000000000000000 : ℚ), (149180528917709813991953/5000000000000000000000000000 : ℚ), (310375177575874956784449/10000000000000000000000000000 : ℚ), (322176605663406759699513/10000000000000000000000000000 : ℚ), (13350665496168409392841/400000000000000000000000000 : ℚ), (345146572588200241331323/10000000000000000000000000000 : ℚ), (178158858257660393392687/5000000000000000000000000000 : ℚ), (367281380938039449312861/10000000000000000000000000000 : ℚ), (37803888491764489625843/1000000000000000000000000000 : ℚ), (194295777796531704383593/5000000000000000000000000000 : ℚ), (398940728861927276860191/10000000000000000000000000000 : ℚ), (204543874987277358214251/5000000000000000000000000000 : ℚ), (419033974042330798514519/10000000000000000000000000000 : ℚ), (428780766462708282270439/10000000000000000000000000000 : ℚ), (219164751631837372671599/5000000000000000000000000000 : ℚ), (1399004910534559862969/31250000000000000000000000 : ℚ), (456838368802479813221167/10000000000000000000000000000 : ℚ), (465801304792070882905447/10000000000000000000000000000 : ℚ), (474571799850372390898303/10000000000000000000000000000 : ℚ), (241575642881967471295593/5000000000000000000000000000 : ℚ), (49154120553928322213551/1000000000000000000000000000 : ℚ), (249871506647954473057647/5000000000000000000000000000 : ℚ), (12693954352823311232257/250000000000000000000000000 : ℚ), (257794081916995146115147/5000000000000000000000000000 : ℚ), (261617234417390879409747/5000000000000000000000000000 : ℚ), (265349292878773694007287/5000000000000000000000000000 : ℚ), (268991010608282193663077/5000000000000000000000000000 : ℚ), (34067893217408351140973/625000000000000000000000000 : ℚ), (552012922121506340793803/10000000000000000000000000000 : ℚ), (558763447675761562265739/10000000000000000000000000000 : ℚ), (141334852812450278847129/2500000000000000000000000000 : ℚ), (571742364144383778240487/10000000000000000000000000000 : ℚ), (577973865457274968762973/10000000000000000000000000000 : ℚ), (292017740840574131829177/5000000000000000000000000000 : ℚ), (294964393148420531384687/5000000000000000000000000000 : ℚ), (18614229980123174705813/312500000000000000000000000 : ℚ), (120243357422093871682293/2000000000000000000000000000 : ℚ), (606614661523207387586409/10000000000000000000000000000 : ℚ), (611850579940052861630579/10000000000000000000000000000 : ℚ), (77115768080696715839307/1250000000000000000000000000 : ℚ), (621842962470792592364833/10000000000000000000000000000 : ℚ), (626602644398065919048889/10000000000000000000000000000 : ℚ), (63120680517178588392493/1000000000000000000000000000 : ℚ), (635657062915504282927369/10000000000000000000000000000 : ℚ), (159988759688990414042541/2500000000000000000000000000 : ℚ), (527295264508243576225637/2000000000000000000000000000 : ℚ), (2691166154741374789277923/10000000000000000000000000000 : ℚ), (136851273155423595618897/500000000000000000000000000 : ℚ), (110978622079865637880799/400000000000000000000000000 : ℚ), (1760072583204940561637417/5000000000000000000000000000 : ℚ), (1775244602054821600868129/5000000000000000000000000000 : ℚ), (3567143819119230831609073/10000000000000000000000000000 : ℚ), (3571079496877002723914923/10000000000000000000000000000 : ℚ), (4283803666203882434064467/10000000000000000000000000000 : ℚ), (4253072907481258769110001/10000000000000000000000000000 : ℚ), (2102884785297567115090069/5000000000000000000000000000 : ℚ), (2071858954793818664448797/5000000000000000000000000000 : ℚ), (593269839948939413527391/1250000000000000000000000000 : ℚ), (92509849600491742399051/200000000000000000000000000 : ℚ), (4490152656409407936527259/10000000000000000000000000000 : ℚ), (1239145258720483106287869/2500000000000000000000000000 : ℚ), (4749947441903428836051731/10000000000000000000000000000 : ℚ), (1017983262233536692834027/2000000000000000000000000000 : ℚ), (961547581913180001277691/2000000000000000000000000000 : ℚ), (501164360436153998406743/1000000000000000000000000000 : ℚ), (4661868473548322590415251/10000000000000000000000000000 : ℚ), (4736985516301619359073309/10000000000000000000000000000 : ℚ), (868086898726071078298071/2000000000000000000000000000 : ℚ), (4310939665477662436195133/10000000000000000000000000000 : ℚ), (3898051547956846386971031/10000000000000000000000000000 : ℚ), (1900014017688696373577901/5000000000000000000000000000 : ℚ), (1701928979993594992010083/5000000000000000000000000000 : ℚ), (1638101437727340517562267/5000000000000000000000000000 : ℚ), (1560644075155338307094623/5000000000000000000000000000 : ℚ), (147591113464860463466867/500000000000000000000000000 : ℚ), (655947597845925944518381/2500000000000000000000000000 : ℚ), (31113697498554268328697/125000000000000000000000000 : ℚ), (1178589100753128796026127/5000000000000000000000000000 : ℚ), (278852633586297711782219/1250000000000000000000000000 : ℚ), (2110685235661830683324729/10000000000000000000000000000 : ℚ), (249517841912178699409289/1250000000000000000000000000 : ℚ), (1886199677049058180759023/10000000000000000000000000000 : ℚ), (356040487888847702673113/2000000000000000000000000000 : ℚ), (1678126242868250257720729/10000000000000000000000000000 : ℚ), (32156386122272668851727/312500000000000000000000000 : ℚ)] := by
    change [blockChargeRow bflatBlockJ4B0 bflatBlocksJ4, blockChargeRow bflatBlockJ4B1 bflatBlocksJ4, blockChargeRow bflatBlockJ4B2 bflatBlocksJ4, blockChargeRow bflatBlockJ4B3 bflatBlocksJ4, blockChargeRow bflatBlockJ4B4 bflatBlocksJ4, blockChargeRow bflatBlockJ4B5 bflatBlocksJ4, blockChargeRow bflatBlockJ4B6 bflatBlocksJ4, blockChargeRow bflatBlockJ4B7 bflatBlocksJ4, blockChargeRow bflatBlockJ4B8 bflatBlocksJ4, blockChargeRow bflatBlockJ4B9 bflatBlocksJ4, blockChargeRow bflatBlockJ4B10 bflatBlocksJ4, blockChargeRow bflatBlockJ4B11 bflatBlocksJ4, blockChargeRow bflatBlockJ4B12 bflatBlocksJ4, blockChargeRow bflatBlockJ4B13 bflatBlocksJ4, blockChargeRow bflatBlockJ4B14 bflatBlocksJ4, blockChargeRow bflatBlockJ4B15 bflatBlocksJ4, blockChargeRow bflatBlockJ4B16 bflatBlocksJ4, blockChargeRow bflatBlockJ4B17 bflatBlocksJ4, blockChargeRow bflatBlockJ4B18 bflatBlocksJ4, blockChargeRow bflatBlockJ4B19 bflatBlocksJ4, blockChargeRow bflatBlockJ4B20 bflatBlocksJ4, blockChargeRow bflatBlockJ4B21 bflatBlocksJ4, blockChargeRow bflatBlockJ4B22 bflatBlocksJ4, blockChargeRow bflatBlockJ4B23 bflatBlocksJ4, blockChargeRow bflatBlockJ4B24 bflatBlocksJ4, blockChargeRow bflatBlockJ4B25 bflatBlocksJ4, blockChargeRow bflatBlockJ4B26 bflatBlocksJ4, blockChargeRow bflatBlockJ4B27 bflatBlocksJ4, blockChargeRow bflatBlockJ4B28 bflatBlocksJ4, blockChargeRow bflatBlockJ4B29 bflatBlocksJ4, blockChargeRow bflatBlockJ4B30 bflatBlocksJ4, blockChargeRow bflatBlockJ4B31 bflatBlocksJ4, blockChargeRow bflatBlockJ4B32 bflatBlocksJ4, blockChargeRow bflatBlockJ4B33 bflatBlocksJ4, blockChargeRow bflatBlockJ4B34 bflatBlocksJ4, blockChargeRow bflatBlockJ4B35 bflatBlocksJ4, blockChargeRow bflatBlockJ4B36 bflatBlocksJ4, blockChargeRow bflatBlockJ4B37 bflatBlocksJ4, blockChargeRow bflatBlockJ4B38 bflatBlocksJ4, blockChargeRow bflatBlockJ4B39 bflatBlocksJ4, blockChargeRow bflatBlockJ4B40 bflatBlocksJ4, blockChargeRow bflatBlockJ4B41 bflatBlocksJ4, blockChargeRow bflatBlockJ4B42 bflatBlocksJ4, blockChargeRow bflatBlockJ4B43 bflatBlocksJ4, blockChargeRow bflatBlockJ4B44 bflatBlocksJ4, blockChargeRow bflatBlockJ4B45 bflatBlocksJ4, blockChargeRow bflatBlockJ4B46 bflatBlocksJ4, blockChargeRow bflatBlockJ4B47 bflatBlocksJ4, blockChargeRow bflatBlockJ4B48 bflatBlocksJ4, blockChargeRow bflatBlockJ4B49 bflatBlocksJ4, blockChargeRow bflatBlockJ4B50 bflatBlocksJ4, blockChargeRow bflatBlockJ4B51 bflatBlocksJ4, blockChargeRow bflatBlockJ4B52 bflatBlocksJ4, blockChargeRow bflatBlockJ4B53 bflatBlocksJ4, blockChargeRow bflatBlockJ4B54 bflatBlocksJ4, blockChargeRow bflatBlockJ4B55 bflatBlocksJ4, blockChargeRow bflatBlockJ4B56 bflatBlocksJ4, blockChargeRow bflatBlockJ4B57 bflatBlocksJ4, blockChargeRow bflatBlockJ4B58 bflatBlocksJ4, blockChargeRow bflatBlockJ4B59 bflatBlocksJ4, blockChargeRow bflatBlockJ4B60 bflatBlocksJ4, blockChargeRow bflatBlockJ4B61 bflatBlocksJ4, blockChargeRow bflatBlockJ4B62 bflatBlocksJ4, blockChargeRow bflatBlockJ4B63 bflatBlocksJ4, blockChargeRow bflatBlockJ4B64 bflatBlocksJ4, blockChargeRow bflatBlockJ4B65 bflatBlocksJ4, blockChargeRow bflatBlockJ4B66 bflatBlocksJ4, blockChargeRow bflatBlockJ4B67 bflatBlocksJ4, blockChargeRow bflatBlockJ4B68 bflatBlocksJ4, blockChargeRow bflatBlockJ4B69 bflatBlocksJ4, blockChargeRow bflatBlockJ4B70 bflatBlocksJ4, blockChargeRow bflatBlockJ4B71 bflatBlocksJ4, blockChargeRow bflatBlockJ4B72 bflatBlocksJ4, blockChargeRow bflatBlockJ4B73 bflatBlocksJ4, blockChargeRow bflatBlockJ4B74 bflatBlocksJ4, blockChargeRow bflatBlockJ4B75 bflatBlocksJ4, blockChargeRow bflatBlockJ4B76 bflatBlocksJ4, blockChargeRow bflatBlockJ4B77 bflatBlocksJ4, blockChargeRow bflatBlockJ4B78 bflatBlocksJ4, blockChargeRow bflatBlockJ4B79 bflatBlocksJ4, blockChargeRow bflatBlockJ4B80 bflatBlocksJ4, blockChargeRow bflatBlockJ4B81 bflatBlocksJ4, blockChargeRow bflatBlockJ4B82 bflatBlocksJ4, blockChargeRow bflatBlockJ4B83 bflatBlocksJ4, blockChargeRow bflatBlockJ4B84 bflatBlocksJ4, blockChargeRow bflatBlockJ4B85 bflatBlocksJ4, blockChargeRow bflatBlockJ4B86 bflatBlocksJ4, blockChargeRow bflatBlockJ4B87 bflatBlocksJ4, blockChargeRow bflatBlockJ4B88 bflatBlocksJ4, blockChargeRow bflatBlockJ4B89 bflatBlocksJ4, blockChargeRow bflatBlockJ4B90 bflatBlocksJ4, blockChargeRow bflatBlockJ4B91 bflatBlocksJ4, blockChargeRow bflatBlockJ4B92 bflatBlocksJ4, blockChargeRow bflatBlockJ4B93 bflatBlocksJ4, blockChargeRow bflatBlockJ4B94 bflatBlocksJ4, blockChargeRow bflatBlockJ4B95 bflatBlocksJ4, blockChargeRow bflatBlockJ4B96 bflatBlocksJ4, blockChargeRow bflatBlockJ4B97 bflatBlocksJ4, blockChargeRow bflatBlockJ4B98 bflatBlocksJ4, blockChargeRow bflatBlockJ4B99 bflatBlocksJ4, blockChargeRow bflatBlockJ4B100 bflatBlocksJ4, blockChargeRow bflatBlockJ4B101 bflatBlocksJ4, blockChargeRow bflatBlockJ4B102 bflatBlocksJ4, blockChargeRow bflatBlockJ4B103 bflatBlocksJ4] = _
    rw [block_charge_row_j4_b0,
      block_charge_row_j4_b1,
      block_charge_row_j4_b2,
      block_charge_row_j4_b3,
      block_charge_row_j4_b4,
      block_charge_row_j4_b5,
      block_charge_row_j4_b6,
      block_charge_row_j4_b7,
      block_charge_row_j4_b8,
      block_charge_row_j4_b9,
      block_charge_row_j4_b10,
      block_charge_row_j4_b11,
      block_charge_row_j4_b12,
      block_charge_row_j4_b13,
      block_charge_row_j4_b14,
      block_charge_row_j4_b15,
      block_charge_row_j4_b16,
      block_charge_row_j4_b17,
      block_charge_row_j4_b18,
      block_charge_row_j4_b19,
      block_charge_row_j4_b20,
      block_charge_row_j4_b21,
      block_charge_row_j4_b22,
      block_charge_row_j4_b23,
      block_charge_row_j4_b24,
      block_charge_row_j4_b25,
      block_charge_row_j4_b26,
      block_charge_row_j4_b27,
      block_charge_row_j4_b28,
      block_charge_row_j4_b29,
      block_charge_row_j4_b30,
      block_charge_row_j4_b31,
      block_charge_row_j4_b32,
      block_charge_row_j4_b33,
      block_charge_row_j4_b34,
      block_charge_row_j4_b35,
      block_charge_row_j4_b36,
      block_charge_row_j4_b37,
      block_charge_row_j4_b38,
      block_charge_row_j4_b39,
      block_charge_row_j4_b40,
      block_charge_row_j4_b41,
      block_charge_row_j4_b42,
      block_charge_row_j4_b43,
      block_charge_row_j4_b44,
      block_charge_row_j4_b45,
      block_charge_row_j4_b46,
      block_charge_row_j4_b47,
      block_charge_row_j4_b48,
      block_charge_row_j4_b49,
      block_charge_row_j4_b50,
      block_charge_row_j4_b51,
      block_charge_row_j4_b52,
      block_charge_row_j4_b53,
      block_charge_row_j4_b54,
      block_charge_row_j4_b55,
      block_charge_row_j4_b56,
      block_charge_row_j4_b57,
      block_charge_row_j4_b58,
      block_charge_row_j4_b59,
      block_charge_row_j4_b60,
      block_charge_row_j4_b61,
      block_charge_row_j4_b62,
      block_charge_row_j4_b63,
      block_charge_row_j4_b64,
      block_charge_row_j4_b65,
      block_charge_row_j4_b66,
      block_charge_row_j4_b67,
      block_charge_row_j4_b68,
      block_charge_row_j4_b69,
      block_charge_row_j4_b70,
      block_charge_row_j4_b71,
      block_charge_row_j4_b72,
      block_charge_row_j4_b73,
      block_charge_row_j4_b74,
      block_charge_row_j4_b75,
      block_charge_row_j4_b76,
      block_charge_row_j4_b77,
      block_charge_row_j4_b78,
      block_charge_row_j4_b79,
      block_charge_row_j4_b80,
      block_charge_row_j4_b81,
      block_charge_row_j4_b82,
      block_charge_row_j4_b83,
      block_charge_row_j4_b84,
      block_charge_row_j4_b85,
      block_charge_row_j4_b86,
      block_charge_row_j4_b87,
      block_charge_row_j4_b88,
      block_charge_row_j4_b89,
      block_charge_row_j4_b90,
      block_charge_row_j4_b91,
      block_charge_row_j4_b92,
      block_charge_row_j4_b93,
      block_charge_row_j4_b94,
      block_charge_row_j4_b95,
      block_charge_row_j4_b96,
      block_charge_row_j4_b97,
      block_charge_row_j4_b98,
      block_charge_row_j4_b99,
      block_charge_row_j4_b100,
      block_charge_row_j4_b101,
      block_charge_row_j4_b102,
      block_charge_row_j4_b103]
  change (bflatBlocksJ4.map (fun a => blockChargeRow a bflatBlocksJ4)).sum = _
  rw [hrows]
  decide +kernel
theorem bflat_lower_j4 : blockLowerSum bflatBlocksJ4 = (9991631911802854962809/10000000000000000000000 : ℚ) := by
  decide +kernel
/-- Exact q3 covariance-integral cap, with a positive block majorant. -/
theorem bflat_cap_j4 : 2-2*q3Projection 4 512 < ((1/50 : ℚ) : ℝ) := by
  have h := block_certificate_sound 4 512 bflatBlocksJ4 block_cover_j4
    (List.all_eq_true.mp all_blocks_entries_j4) (List.all_eq_true.mp all_blocks_mass_j4)
  rw [bflat_lower_j4,bflat_charge_j4] at h
  have hc : (2-2*(9991631911802854962809/10000000000000000000000 : ℚ)^2+(8203060553804829142322999/500000000000000000000000000 : ℚ) : ℚ) < (1/50 : ℚ) := by decide +kernel
  exact h.trans_lt (by exact_mod_cast hc)
end ASDExplicitGamma.Numerics.Model
