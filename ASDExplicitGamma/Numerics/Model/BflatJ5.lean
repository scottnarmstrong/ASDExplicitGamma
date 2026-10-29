module
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part000
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part001
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part002
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part003
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part004
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part005
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part006
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part007
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part008
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part009
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part010
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part011
public import ASDExplicitGamma.Numerics.Model.ChargesJ5Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
theorem bflat_charge_j5 : blockCharge bflatBlocksJ5 = (29359646160404907584791069/5000000000000000000000000000 : ℚ) := by
  have hrows : bflatBlocksJ5.map (fun a => blockChargeRow a bflatBlocksJ5) = [(428113442860880132629/10000000000000000000000000000 : ℚ), (1048694345448452796967/10000000000000000000000000000 : ℚ), (104339405344039838669/625000000000000000000000000 : ℚ), (11440028878635583261/50000000000000000000000000 : ℚ), (2904410272513117375539/10000000000000000000000000000 : ℚ), (175932028906251650629/500000000000000000000000000 : ℚ), (2065345645778464701749/5000000000000000000000000000 : ℚ), (474055506088737651919/1000000000000000000000000000 : ℚ), (2674111335649452800147/5000000000000000000000000000 : ℚ), (1488420785909055062287/2500000000000000000000000000 : ℚ), (6556923842255100876421/10000000000000000000000000000 : ℚ), (3578965295445964910329/5000000000000000000000000000 : ℚ), (969585974403223895531/1250000000000000000000000000 : ℚ), (8353178570770873628237/10000000000000000000000000000 : ℚ), (71579078997809252449/80000000000000000000000000 : ℚ), (4769643820210569404273/5000000000000000000000000000 : ℚ), (1012886691302917923357/1000000000000000000000000000 : ℚ), (10716101985272014563601/10000000000000000000000000000 : ℚ), (2260194306381588849689/2000000000000000000000000000 : ℚ), (2376690748375913757647/2000000000000000000000000000 : ℚ), (6231763223546101783293/5000000000000000000000000000 : ℚ), (13041167246898459735607/10000000000000000000000000000 : ℚ), (1361635362747530405143/1000000000000000000000000000 : ℚ), (14189063075394559469771/10000000000000000000000000000 : ℚ), (1844909148100481086817/1250000000000000000000000000 : ℚ), (15326961757750152161683/10000000000000000000000000000 : ℚ), (15892106897290409758863/10000000000000000000000000000 : ℚ), (8227343546570620858191/5000000000000000000000000000 : ℚ), (680587251988854733357/400000000000000000000000000 : ℚ), (8786034503267284648321/5000000000000000000000000000 : ℚ), (145014642407416521981/80000000000000000000000000 : ℚ), (9339472961665252716831/5000000000000000000000000000 : ℚ), (30765435704271761697/16000000000000000000000000 : ℚ), (9887583329837146321963/5000000000000000000000000000 : ℚ), (10159618457939481355377/5000000000000000000000000000 : ℚ), (834423673845835234131/400000000000000000000000000 : ℚ), (2674902004695582358431/1250000000000000000000000000 : ℚ), (5483773729404383504437/2500000000000000000000000000 : ℚ), (5617053691127473574601/2500000000000000000000000000 : ℚ), (11499281356288608138259/5000000000000000000000000000 : ℚ), (4705225350636609804121/2000000000000000000000000000 : ℚ), (187897622902507380923/78125000000000000000000000 : ℚ), (1228642966986344339637/500000000000000000000000000 : ℚ), (25092008106698393600087/10000000000000000000000000000 : ℚ), (25608333385002849502373/10000000000000000000000000000 : ℚ), (26121827335241254499909/10000000000000000000000000000 : ℚ), (2663248290821519806607/1000000000000000000000000000 : ℚ), (6785073456306215954609/2500000000000000000000000000 : ℚ), (27645254556804850594203/10000000000000000000000000000 : ℚ), (14073680150091442355401/5000000000000000000000000000 : ℚ), (3580825869465570284463/1250000000000000000000000000 : ℚ), (29142991102605340494101/10000000000000000000000000000 : ℚ), (29636509973929426051841/10000000000000000000000000000 : ℚ), (1506358071574709069223/500000000000000000000000000 : ℚ), (30614943940378376956559/10000000000000000000000000000 : ℚ), (388748206793915083811/125000000000000000000000000 : ℚ), (7895474709094143568911/2500000000000000000000000000 : ℚ), (400763386774172158643/125000000000000000000000000 : ℚ), (16268686742965739446393/5000000000000000000000000000 : ℚ), (33010807572636848489867/10000000000000000000000000000 : ℚ), (16740687380549794050631/5000000000000000000000000000 : ℚ), (33949077042002038953687/10000000000000000000000000000 : ℚ), (34413916815150642175029/10000000000000000000000000000 : ℚ), (34875896867651535708161/10000000000000000000000000000 : ℚ), (266534082530884077782707/10000000000000000000000000000 : ℚ), (332245977033081185301847/10000000000000000000000000000 : ℚ), (406875318806716570206403/10000000000000000000000000000 : ℚ), (27370287760814974292541/625000000000000000000000000 : ℚ), (522573358572142643796351/10000000000000000000000000000 : ℚ), (984293925405832872609/16000000000000000000000000 : ℚ), (178778011644474554737473/2500000000000000000000000000 : ℚ), (888576241799180356314723/10000000000000000000000000000 : ℚ), (503372608867379599166557/5000000000000000000000000000 : ℚ), (1202015891007926509212771/10000000000000000000000000000 : ℚ), (1329301512862453133147397/10000000000000000000000000000 : ℚ), (383392585968141167586671/2500000000000000000000000000 : ℚ), (434498808716400126464201/2500000000000000000000000000 : ℚ), (121004354533637616072461/625000000000000000000000000 : ℚ), (1102145826000082980836707/5000000000000000000000000000 : ℚ), (1183443195572870580443477/5000000000000000000000000000 : ℚ), (129002597673997836961047/500000000000000000000000000 : ℚ), (137397956903860046749909/500000000000000000000000000 : ℚ), (733560138128975377667689/2500000000000000000000000000 : ℚ), (1520612942532588903822267/5000000000000000000000000000 : ℚ), (1529956781230875637655229/5000000000000000000000000000 : ℚ), (3045142707839503399202013/10000000000000000000000000000 : ℚ), (365858108247999101997157/1250000000000000000000000000 : ℚ), (2762850389454673947975527/10000000000000000000000000000 : ℚ), (503757027980188349396361/2000000000000000000000000000 : ℚ), (2259807009722935377122249/10000000000000000000000000000 : ℚ), (400653318939834089094569/2000000000000000000000000000 : ℚ), (109465950988550439149693/625000000000000000000000000 : ℚ), (1544430156792861153268921/10000000000000000000000000000 : ℚ), (344549015849186447395353/2500000000000000000000000000 : ℚ), (248158928689754958739943/2000000000000000000000000000 : ℚ), (1127937774428562621170323/10000000000000000000000000000 : ℚ), (1016111567745443141021367/10000000000000000000000000000 : ℚ), (920813991446902144195101/10000000000000000000000000000 : ℚ), (833282248905584908936721/10000000000000000000000000000 : ℚ), (170026650316130657072087/5000000000000000000000000000 : ℚ)] := by
    change [blockChargeRow bflatBlockJ5B0 bflatBlocksJ5, blockChargeRow bflatBlockJ5B1 bflatBlocksJ5, blockChargeRow bflatBlockJ5B2 bflatBlocksJ5, blockChargeRow bflatBlockJ5B3 bflatBlocksJ5, blockChargeRow bflatBlockJ5B4 bflatBlocksJ5, blockChargeRow bflatBlockJ5B5 bflatBlocksJ5, blockChargeRow bflatBlockJ5B6 bflatBlocksJ5, blockChargeRow bflatBlockJ5B7 bflatBlocksJ5, blockChargeRow bflatBlockJ5B8 bflatBlocksJ5, blockChargeRow bflatBlockJ5B9 bflatBlocksJ5, blockChargeRow bflatBlockJ5B10 bflatBlocksJ5, blockChargeRow bflatBlockJ5B11 bflatBlocksJ5, blockChargeRow bflatBlockJ5B12 bflatBlocksJ5, blockChargeRow bflatBlockJ5B13 bflatBlocksJ5, blockChargeRow bflatBlockJ5B14 bflatBlocksJ5, blockChargeRow bflatBlockJ5B15 bflatBlocksJ5, blockChargeRow bflatBlockJ5B16 bflatBlocksJ5, blockChargeRow bflatBlockJ5B17 bflatBlocksJ5, blockChargeRow bflatBlockJ5B18 bflatBlocksJ5, blockChargeRow bflatBlockJ5B19 bflatBlocksJ5, blockChargeRow bflatBlockJ5B20 bflatBlocksJ5, blockChargeRow bflatBlockJ5B21 bflatBlocksJ5, blockChargeRow bflatBlockJ5B22 bflatBlocksJ5, blockChargeRow bflatBlockJ5B23 bflatBlocksJ5, blockChargeRow bflatBlockJ5B24 bflatBlocksJ5, blockChargeRow bflatBlockJ5B25 bflatBlocksJ5, blockChargeRow bflatBlockJ5B26 bflatBlocksJ5, blockChargeRow bflatBlockJ5B27 bflatBlocksJ5, blockChargeRow bflatBlockJ5B28 bflatBlocksJ5, blockChargeRow bflatBlockJ5B29 bflatBlocksJ5, blockChargeRow bflatBlockJ5B30 bflatBlocksJ5, blockChargeRow bflatBlockJ5B31 bflatBlocksJ5, blockChargeRow bflatBlockJ5B32 bflatBlocksJ5, blockChargeRow bflatBlockJ5B33 bflatBlocksJ5, blockChargeRow bflatBlockJ5B34 bflatBlocksJ5, blockChargeRow bflatBlockJ5B35 bflatBlocksJ5, blockChargeRow bflatBlockJ5B36 bflatBlocksJ5, blockChargeRow bflatBlockJ5B37 bflatBlocksJ5, blockChargeRow bflatBlockJ5B38 bflatBlocksJ5, blockChargeRow bflatBlockJ5B39 bflatBlocksJ5, blockChargeRow bflatBlockJ5B40 bflatBlocksJ5, blockChargeRow bflatBlockJ5B41 bflatBlocksJ5, blockChargeRow bflatBlockJ5B42 bflatBlocksJ5, blockChargeRow bflatBlockJ5B43 bflatBlocksJ5, blockChargeRow bflatBlockJ5B44 bflatBlocksJ5, blockChargeRow bflatBlockJ5B45 bflatBlocksJ5, blockChargeRow bflatBlockJ5B46 bflatBlocksJ5, blockChargeRow bflatBlockJ5B47 bflatBlocksJ5, blockChargeRow bflatBlockJ5B48 bflatBlocksJ5, blockChargeRow bflatBlockJ5B49 bflatBlocksJ5, blockChargeRow bflatBlockJ5B50 bflatBlocksJ5, blockChargeRow bflatBlockJ5B51 bflatBlocksJ5, blockChargeRow bflatBlockJ5B52 bflatBlocksJ5, blockChargeRow bflatBlockJ5B53 bflatBlocksJ5, blockChargeRow bflatBlockJ5B54 bflatBlocksJ5, blockChargeRow bflatBlockJ5B55 bflatBlocksJ5, blockChargeRow bflatBlockJ5B56 bflatBlocksJ5, blockChargeRow bflatBlockJ5B57 bflatBlocksJ5, blockChargeRow bflatBlockJ5B58 bflatBlocksJ5, blockChargeRow bflatBlockJ5B59 bflatBlocksJ5, blockChargeRow bflatBlockJ5B60 bflatBlocksJ5, blockChargeRow bflatBlockJ5B61 bflatBlocksJ5, blockChargeRow bflatBlockJ5B62 bflatBlocksJ5, blockChargeRow bflatBlockJ5B63 bflatBlocksJ5, blockChargeRow bflatBlockJ5B64 bflatBlocksJ5, blockChargeRow bflatBlockJ5B65 bflatBlocksJ5, blockChargeRow bflatBlockJ5B66 bflatBlocksJ5, blockChargeRow bflatBlockJ5B67 bflatBlocksJ5, blockChargeRow bflatBlockJ5B68 bflatBlocksJ5, blockChargeRow bflatBlockJ5B69 bflatBlocksJ5, blockChargeRow bflatBlockJ5B70 bflatBlocksJ5, blockChargeRow bflatBlockJ5B71 bflatBlocksJ5, blockChargeRow bflatBlockJ5B72 bflatBlocksJ5, blockChargeRow bflatBlockJ5B73 bflatBlocksJ5, blockChargeRow bflatBlockJ5B74 bflatBlocksJ5, blockChargeRow bflatBlockJ5B75 bflatBlocksJ5, blockChargeRow bflatBlockJ5B76 bflatBlocksJ5, blockChargeRow bflatBlockJ5B77 bflatBlocksJ5, blockChargeRow bflatBlockJ5B78 bflatBlocksJ5, blockChargeRow bflatBlockJ5B79 bflatBlocksJ5, blockChargeRow bflatBlockJ5B80 bflatBlocksJ5, blockChargeRow bflatBlockJ5B81 bflatBlocksJ5, blockChargeRow bflatBlockJ5B82 bflatBlocksJ5, blockChargeRow bflatBlockJ5B83 bflatBlocksJ5, blockChargeRow bflatBlockJ5B84 bflatBlocksJ5, blockChargeRow bflatBlockJ5B85 bflatBlocksJ5, blockChargeRow bflatBlockJ5B86 bflatBlocksJ5, blockChargeRow bflatBlockJ5B87 bflatBlocksJ5, blockChargeRow bflatBlockJ5B88 bflatBlocksJ5, blockChargeRow bflatBlockJ5B89 bflatBlocksJ5, blockChargeRow bflatBlockJ5B90 bflatBlocksJ5, blockChargeRow bflatBlockJ5B91 bflatBlocksJ5, blockChargeRow bflatBlockJ5B92 bflatBlocksJ5, blockChargeRow bflatBlockJ5B93 bflatBlocksJ5, blockChargeRow bflatBlockJ5B94 bflatBlocksJ5, blockChargeRow bflatBlockJ5B95 bflatBlocksJ5, blockChargeRow bflatBlockJ5B96 bflatBlocksJ5, blockChargeRow bflatBlockJ5B97 bflatBlocksJ5, blockChargeRow bflatBlockJ5B98 bflatBlocksJ5, blockChargeRow bflatBlockJ5B99 bflatBlocksJ5] = _
    rw [block_charge_row_j5_b0,
      block_charge_row_j5_b1,
      block_charge_row_j5_b2,
      block_charge_row_j5_b3,
      block_charge_row_j5_b4,
      block_charge_row_j5_b5,
      block_charge_row_j5_b6,
      block_charge_row_j5_b7,
      block_charge_row_j5_b8,
      block_charge_row_j5_b9,
      block_charge_row_j5_b10,
      block_charge_row_j5_b11,
      block_charge_row_j5_b12,
      block_charge_row_j5_b13,
      block_charge_row_j5_b14,
      block_charge_row_j5_b15,
      block_charge_row_j5_b16,
      block_charge_row_j5_b17,
      block_charge_row_j5_b18,
      block_charge_row_j5_b19,
      block_charge_row_j5_b20,
      block_charge_row_j5_b21,
      block_charge_row_j5_b22,
      block_charge_row_j5_b23,
      block_charge_row_j5_b24,
      block_charge_row_j5_b25,
      block_charge_row_j5_b26,
      block_charge_row_j5_b27,
      block_charge_row_j5_b28,
      block_charge_row_j5_b29,
      block_charge_row_j5_b30,
      block_charge_row_j5_b31,
      block_charge_row_j5_b32,
      block_charge_row_j5_b33,
      block_charge_row_j5_b34,
      block_charge_row_j5_b35,
      block_charge_row_j5_b36,
      block_charge_row_j5_b37,
      block_charge_row_j5_b38,
      block_charge_row_j5_b39,
      block_charge_row_j5_b40,
      block_charge_row_j5_b41,
      block_charge_row_j5_b42,
      block_charge_row_j5_b43,
      block_charge_row_j5_b44,
      block_charge_row_j5_b45,
      block_charge_row_j5_b46,
      block_charge_row_j5_b47,
      block_charge_row_j5_b48,
      block_charge_row_j5_b49,
      block_charge_row_j5_b50,
      block_charge_row_j5_b51,
      block_charge_row_j5_b52,
      block_charge_row_j5_b53,
      block_charge_row_j5_b54,
      block_charge_row_j5_b55,
      block_charge_row_j5_b56,
      block_charge_row_j5_b57,
      block_charge_row_j5_b58,
      block_charge_row_j5_b59,
      block_charge_row_j5_b60,
      block_charge_row_j5_b61,
      block_charge_row_j5_b62,
      block_charge_row_j5_b63,
      block_charge_row_j5_b64,
      block_charge_row_j5_b65,
      block_charge_row_j5_b66,
      block_charge_row_j5_b67,
      block_charge_row_j5_b68,
      block_charge_row_j5_b69,
      block_charge_row_j5_b70,
      block_charge_row_j5_b71,
      block_charge_row_j5_b72,
      block_charge_row_j5_b73,
      block_charge_row_j5_b74,
      block_charge_row_j5_b75,
      block_charge_row_j5_b76,
      block_charge_row_j5_b77,
      block_charge_row_j5_b78,
      block_charge_row_j5_b79,
      block_charge_row_j5_b80,
      block_charge_row_j5_b81,
      block_charge_row_j5_b82,
      block_charge_row_j5_b83,
      block_charge_row_j5_b84,
      block_charge_row_j5_b85,
      block_charge_row_j5_b86,
      block_charge_row_j5_b87,
      block_charge_row_j5_b88,
      block_charge_row_j5_b89,
      block_charge_row_j5_b90,
      block_charge_row_j5_b91,
      block_charge_row_j5_b92,
      block_charge_row_j5_b93,
      block_charge_row_j5_b94,
      block_charge_row_j5_b95,
      block_charge_row_j5_b96,
      block_charge_row_j5_b97,
      block_charge_row_j5_b98,
      block_charge_row_j5_b99]
  change (bflatBlocksJ5.map (fun a => blockChargeRow a bflatBlocksJ5)).sum = _
  rw [hrows]
  decide +kernel
theorem bflat_lower_j5 : blockLowerSum bflatBlocksJ5 = (9997956762112368149281/10000000000000000000000 : ℚ) := by
  decide +kernel
/-- Exact q3 covariance-integral cap, with a positive block majorant. -/
theorem bflat_cap_j5 : 2-2*q3Projection 5 2048 < ((7/1000 : ℚ) : ℝ) := by
  have h := block_certificate_sound 5 2048 bflatBlocksJ5 block_cover_j5
    (List.all_eq_true.mp all_blocks_entries_j5) (List.all_eq_true.mp all_blocks_mass_j5)
  rw [bflat_lower_j5,bflat_charge_j5] at h
  have hc : (2-2*(9997956762112368149281/10000000000000000000000 : ℚ)^2+(29359646160404907584791069/5000000000000000000000000000 : ℚ) : ℚ) < (7/1000 : ℚ) := by decide +kernel
  exact h.trans_lt (by exact_mod_cast hc)
end ASDExplicitGamma.Numerics.Model
