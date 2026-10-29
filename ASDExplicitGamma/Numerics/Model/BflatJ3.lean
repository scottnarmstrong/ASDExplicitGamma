module
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part000
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part001
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part002
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part003
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part004
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part005
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part006
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part007
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part008
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part009
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part010
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part011
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part012
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part013
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part014
public import ASDExplicitGamma.Numerics.Model.ChargesJ3Part015

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
theorem bflat_charge_j3 : blockCharge bflatBlocksJ3 = (64202439152110007249889431/1250000000000000000000000000 : ℚ) := by
  have hrows : bflatBlocksJ3.map (fun a => blockChargeRow a bflatBlocksJ3) = [(151464673475349086352729/5000000000000000000000000000 : ℚ), (364039026653240950035739/5000000000000000000000000000 : ℚ), (283904019071504478302449/2500000000000000000000000000 : ℚ), (152422201406187361871087/1000000000000000000000000000 : ℚ), (1894258382500762686655921/10000000000000000000000000000 : ℚ), (2246095139065982880938569/10000000000000000000000000000 : ℚ), (2580103542585710258520113/10000000000000000000000000000 : ℚ), (2896656243889953985646979/10000000000000000000000000000 : ℚ), (799031840324922146489137/2500000000000000000000000000 : ℚ), (3478892524434634561738303/10000000000000000000000000000 : ℚ), (3745328887342976168535383/10000000000000000000000000000 : ℚ), (3995815112034035576974193/10000000000000000000000000000 : ℚ), (2115365661765411838476269/5000000000000000000000000000 : ℚ), (2225229518798157175620221/5000000000000000000000000000 : ℚ), (4655381062324737067665931/10000000000000000000000000000 : ℚ), (30286758592666031576139/62500000000000000000000000 : ℚ), (5022344974272627397749487/10000000000000000000000000000 : ℚ), (2592578856299175634082451/5000000000000000000000000000 : ℚ), (1333676526050757654105731/2500000000000000000000000000 : ℚ), (5471377116010736499963457/10000000000000000000000000000 : ℚ), (1398889484822145192720139/2500000000000000000000000000 : ℚ), (1141527148928821166399251/2000000000000000000000000000 : ℚ), (5807997421646223303319387/10000000000000000000000000000 : ℚ), (2948514652266515050623699/5000000000000000000000000000 : ℚ), (1493779221371175151127333/2500000000000000000000000000 : ℚ), (3021322258475120439140741/5000000000000000000000000000 : ℚ), (1219999020904598477370171/2000000000000000000000000000 : ℚ), (3073774895930614784033607/5000000000000000000000000000 : ℚ), (773210954893361603212871/1250000000000000000000000000 : ℚ), (3107392648283681870959263/5000000000000000000000000000 : ℚ), (1558804168573047815803527/2500000000000000000000000000 : ℚ), (6247352610398824829590863/10000000000000000000000000000 : ℚ), (3125780269089374102161583/5000000000000000000000000000 : ℚ), (6248204154228017342045687/10000000000000000000000000000 : ℚ), (155941077217355002928219/250000000000000000000000000 : ℚ), (777529072376904823190193/1250000000000000000000000000 : ℚ), (1549080787111244261197359/2500000000000000000000000000 : ℚ), (3083130145307608373839283/5000000000000000000000000000 : ℚ), (9578725252086546007497/15625000000000000000000000 : ℚ), (6089029278778524480203917/10000000000000000000000000000 : ℚ), (6042524233146373319739727/10000000000000000000000000000 : ℚ), (5991191406847621234713839/10000000000000000000000000000 : ℚ), (593534670616134136833751/1000000000000000000000000000 : ℚ), (1175059861058704922300989/2000000000000000000000000000 : ℚ), (1162270280733590321095223/2000000000000000000000000000 : ℚ), (229751919888966758021967/400000000000000000000000000 : ℚ), (1134585332885040595696569/2000000000000000000000000000 : ℚ), (699877170950775877211827/1250000000000000000000000000 : ℚ), (2761171135111404265013199/5000000000000000000000000000 : ℚ), (680395696310602131725807/1250000000000000000000000000 : ℚ), (5361743351787486430956771/10000000000000000000000000000 : ℚ), (2639161725139503051916727/5000000000000000000000000000 : ℚ), (2596572669914815803216927/5000000000000000000000000000 : ℚ), (5106440034595152825520329/10000000000000000000000000000 : ℚ), (5018430009295531975051143/10000000000000000000000000000 : ℚ), (1232332284314700957995739/2500000000000000000000000000 : ℚ), (967868529242198257923909/2000000000000000000000000000 : ℚ), (4748667091725111339151541/10000000000000000000000000000 : ℚ), (1164372587044144796561643/2500000000000000000000000000 : ℚ), (1141497904247174465838879/2500000000000000000000000000 : ℚ), (1118585362972667321980409/2500000000000000000000000000 : ℚ), (2191350900425943993553393/5000000000000000000000000000 : ℚ), (107280651607509303739663/250000000000000000000000000 : ℚ), (420005916918022431609449/1000000000000000000000000000 : ℚ), (2036500271091865655774613/2500000000000000000000000000 : ℚ), (7786496727793223310865437/10000000000000000000000000000 : ℚ), (7434025763426891216344943/10000000000000000000000000000 : ℚ), (3545057439642936095577119/5000000000000000000000000000 : ℚ), (1351210697919921516431363/2000000000000000000000000000 : ℚ), (6432905708135722469509727/10000000000000000000000000000 : ℚ), (3060761727643225029908587/5000000000000000000000000000 : ℚ), (2911280245981139382919147/5000000000000000000000000000 : ℚ), (2768243585408653048031651/5000000000000000000000000000 : ℚ), (5263605696353095858965999/10000000000000000000000000000 : ℚ), (5004065689805880247808531/10000000000000000000000000000 : ℚ), (4757879862155342737668733/10000000000000000000000000000 : ℚ), (4524939608797720424588137/10000000000000000000000000000 : ℚ), (4305030352061565342151197/10000000000000000000000000000 : ℚ), (2048923236221960633124409/5000000000000000000000000000 : ℚ), (3903005685822043411902803/10000000000000000000000000000 : ℚ), (3720062741555359690956533/10000000000000000000000000000 : ℚ), (1774261167468489970344947/5000000000000000000000000000 : ℚ), (628589403218804348246739/1250000000000000000000000000 : ℚ), (940173226242603621977057/2000000000000000000000000000 : ℚ), (4404459238566403378052393/10000000000000000000000000000 : ℚ), (4136530555721641606951449/10000000000000000000000000000 : ℚ), (778836803407619535037451/2000000000000000000000000000 : ℚ), (73493080226939515094027/200000000000000000000000000 : ℚ), (3475351747357937175526927/10000000000000000000000000000 : ℚ), (3293896800452337881636931/10000000000000000000000000000 : ℚ), (625627097493568046062883/2000000000000000000000000000 : ℚ), (1488073957977860657043521/5000000000000000000000000000 : ℚ), (1418122827942258780161123/5000000000000000000000000000 : ℚ), (2706961993126200386983591/10000000000000000000000000000 : ℚ), (646759164160802806819729/2500000000000000000000000000 : ℚ), (1237698389325253228137503/5000000000000000000000000000 : ℚ), (94845426560301881429311/400000000000000000000000000 : ℚ), (2273490726973672532843949/10000000000000000000000000000 : ℚ), (2181821715130107103895541/10000000000000000000000000000 : ℚ), (1388297778859130019417107/5000000000000000000000000000 : ℚ), (658703735635256668635823/2500000000000000000000000000 : ℚ), (100141160204075065903983/400000000000000000000000000 : ℚ), (476350984457817177224609/2000000000000000000000000000 : ℚ), (1134324285120006593053393/5000000000000000000000000000 : ℚ), (1081732005437842283036837/5000000000000000000000000000 : ℚ), (516381727176214422264789/2500000000000000000000000000 : ℚ), (493554697664831126549279/2500000000000000000000000000 : ℚ), (94448450504817104224503/500000000000000000000000000 : ℚ), (1809251556070366263898653/10000000000000000000000000000 : ℚ), (1734584344344857257041287/10000000000000000000000000000 : ℚ), (1664529227495332236026841/10000000000000000000000000000 : ℚ), (994398609657864263597469/5000000000000000000000000000 : ℚ), (946672445770094640628661/5000000000000000000000000000 : ℚ), (360925427858305602340059/2000000000000000000000000000 : ℚ), (861002554947993266430301/5000000000000000000000000000 : ℚ), (411231864269824966672663/2500000000000000000000000000 : ℚ), (786456723559591819200359/5000000000000000000000000000 : ℚ), (1505538040980902796980509/10000000000000000000000000000 : ℚ), (288484024930939698047287/2000000000000000000000000000 : ℚ), (1383214199643272929457031/10000000000000000000000000000 : ℚ), (132760514407183869122083/1000000000000000000000000000 : ℚ), (762234647790531157925587/5000000000000000000000000000 : ℚ), (123522385238796627263431/5000000000000000000000000000 : ℚ)] := by
    change [blockChargeRow bflatBlockJ3B0 bflatBlocksJ3, blockChargeRow bflatBlockJ3B1 bflatBlocksJ3, blockChargeRow bflatBlockJ3B2 bflatBlocksJ3, blockChargeRow bflatBlockJ3B3 bflatBlocksJ3, blockChargeRow bflatBlockJ3B4 bflatBlocksJ3, blockChargeRow bflatBlockJ3B5 bflatBlocksJ3, blockChargeRow bflatBlockJ3B6 bflatBlocksJ3, blockChargeRow bflatBlockJ3B7 bflatBlocksJ3, blockChargeRow bflatBlockJ3B8 bflatBlocksJ3, blockChargeRow bflatBlockJ3B9 bflatBlocksJ3, blockChargeRow bflatBlockJ3B10 bflatBlocksJ3, blockChargeRow bflatBlockJ3B11 bflatBlocksJ3, blockChargeRow bflatBlockJ3B12 bflatBlocksJ3, blockChargeRow bflatBlockJ3B13 bflatBlocksJ3, blockChargeRow bflatBlockJ3B14 bflatBlocksJ3, blockChargeRow bflatBlockJ3B15 bflatBlocksJ3, blockChargeRow bflatBlockJ3B16 bflatBlocksJ3, blockChargeRow bflatBlockJ3B17 bflatBlocksJ3, blockChargeRow bflatBlockJ3B18 bflatBlocksJ3, blockChargeRow bflatBlockJ3B19 bflatBlocksJ3, blockChargeRow bflatBlockJ3B20 bflatBlocksJ3, blockChargeRow bflatBlockJ3B21 bflatBlocksJ3, blockChargeRow bflatBlockJ3B22 bflatBlocksJ3, blockChargeRow bflatBlockJ3B23 bflatBlocksJ3, blockChargeRow bflatBlockJ3B24 bflatBlocksJ3, blockChargeRow bflatBlockJ3B25 bflatBlocksJ3, blockChargeRow bflatBlockJ3B26 bflatBlocksJ3, blockChargeRow bflatBlockJ3B27 bflatBlocksJ3, blockChargeRow bflatBlockJ3B28 bflatBlocksJ3, blockChargeRow bflatBlockJ3B29 bflatBlocksJ3, blockChargeRow bflatBlockJ3B30 bflatBlocksJ3, blockChargeRow bflatBlockJ3B31 bflatBlocksJ3, blockChargeRow bflatBlockJ3B32 bflatBlocksJ3, blockChargeRow bflatBlockJ3B33 bflatBlocksJ3, blockChargeRow bflatBlockJ3B34 bflatBlocksJ3, blockChargeRow bflatBlockJ3B35 bflatBlocksJ3, blockChargeRow bflatBlockJ3B36 bflatBlocksJ3, blockChargeRow bflatBlockJ3B37 bflatBlocksJ3, blockChargeRow bflatBlockJ3B38 bflatBlocksJ3, blockChargeRow bflatBlockJ3B39 bflatBlocksJ3, blockChargeRow bflatBlockJ3B40 bflatBlocksJ3, blockChargeRow bflatBlockJ3B41 bflatBlocksJ3, blockChargeRow bflatBlockJ3B42 bflatBlocksJ3, blockChargeRow bflatBlockJ3B43 bflatBlocksJ3, blockChargeRow bflatBlockJ3B44 bflatBlocksJ3, blockChargeRow bflatBlockJ3B45 bflatBlocksJ3, blockChargeRow bflatBlockJ3B46 bflatBlocksJ3, blockChargeRow bflatBlockJ3B47 bflatBlocksJ3, blockChargeRow bflatBlockJ3B48 bflatBlocksJ3, blockChargeRow bflatBlockJ3B49 bflatBlocksJ3, blockChargeRow bflatBlockJ3B50 bflatBlocksJ3, blockChargeRow bflatBlockJ3B51 bflatBlocksJ3, blockChargeRow bflatBlockJ3B52 bflatBlocksJ3, blockChargeRow bflatBlockJ3B53 bflatBlocksJ3, blockChargeRow bflatBlockJ3B54 bflatBlocksJ3, blockChargeRow bflatBlockJ3B55 bflatBlocksJ3, blockChargeRow bflatBlockJ3B56 bflatBlocksJ3, blockChargeRow bflatBlockJ3B57 bflatBlocksJ3, blockChargeRow bflatBlockJ3B58 bflatBlocksJ3, blockChargeRow bflatBlockJ3B59 bflatBlocksJ3, blockChargeRow bflatBlockJ3B60 bflatBlocksJ3, blockChargeRow bflatBlockJ3B61 bflatBlocksJ3, blockChargeRow bflatBlockJ3B62 bflatBlocksJ3, blockChargeRow bflatBlockJ3B63 bflatBlocksJ3, blockChargeRow bflatBlockJ3B64 bflatBlocksJ3, blockChargeRow bflatBlockJ3B65 bflatBlocksJ3, blockChargeRow bflatBlockJ3B66 bflatBlocksJ3, blockChargeRow bflatBlockJ3B67 bflatBlocksJ3, blockChargeRow bflatBlockJ3B68 bflatBlocksJ3, blockChargeRow bflatBlockJ3B69 bflatBlocksJ3, blockChargeRow bflatBlockJ3B70 bflatBlocksJ3, blockChargeRow bflatBlockJ3B71 bflatBlocksJ3, blockChargeRow bflatBlockJ3B72 bflatBlocksJ3, blockChargeRow bflatBlockJ3B73 bflatBlocksJ3, blockChargeRow bflatBlockJ3B74 bflatBlocksJ3, blockChargeRow bflatBlockJ3B75 bflatBlocksJ3, blockChargeRow bflatBlockJ3B76 bflatBlocksJ3, blockChargeRow bflatBlockJ3B77 bflatBlocksJ3, blockChargeRow bflatBlockJ3B78 bflatBlocksJ3, blockChargeRow bflatBlockJ3B79 bflatBlocksJ3, blockChargeRow bflatBlockJ3B80 bflatBlocksJ3, blockChargeRow bflatBlockJ3B81 bflatBlocksJ3, blockChargeRow bflatBlockJ3B82 bflatBlocksJ3, blockChargeRow bflatBlockJ3B83 bflatBlocksJ3, blockChargeRow bflatBlockJ3B84 bflatBlocksJ3, blockChargeRow bflatBlockJ3B85 bflatBlocksJ3, blockChargeRow bflatBlockJ3B86 bflatBlocksJ3, blockChargeRow bflatBlockJ3B87 bflatBlocksJ3, blockChargeRow bflatBlockJ3B88 bflatBlocksJ3, blockChargeRow bflatBlockJ3B89 bflatBlocksJ3, blockChargeRow bflatBlockJ3B90 bflatBlocksJ3, blockChargeRow bflatBlockJ3B91 bflatBlocksJ3, blockChargeRow bflatBlockJ3B92 bflatBlocksJ3, blockChargeRow bflatBlockJ3B93 bflatBlocksJ3, blockChargeRow bflatBlockJ3B94 bflatBlocksJ3, blockChargeRow bflatBlockJ3B95 bflatBlocksJ3, blockChargeRow bflatBlockJ3B96 bflatBlocksJ3, blockChargeRow bflatBlockJ3B97 bflatBlocksJ3, blockChargeRow bflatBlockJ3B98 bflatBlocksJ3, blockChargeRow bflatBlockJ3B99 bflatBlocksJ3, blockChargeRow bflatBlockJ3B100 bflatBlocksJ3, blockChargeRow bflatBlockJ3B101 bflatBlocksJ3, blockChargeRow bflatBlockJ3B102 bflatBlocksJ3, blockChargeRow bflatBlockJ3B103 bflatBlocksJ3, blockChargeRow bflatBlockJ3B104 bflatBlocksJ3, blockChargeRow bflatBlockJ3B105 bflatBlocksJ3, blockChargeRow bflatBlockJ3B106 bflatBlocksJ3, blockChargeRow bflatBlockJ3B107 bflatBlocksJ3, blockChargeRow bflatBlockJ3B108 bflatBlocksJ3, blockChargeRow bflatBlockJ3B109 bflatBlocksJ3, blockChargeRow bflatBlockJ3B110 bflatBlocksJ3, blockChargeRow bflatBlockJ3B111 bflatBlocksJ3, blockChargeRow bflatBlockJ3B112 bflatBlocksJ3, blockChargeRow bflatBlockJ3B113 bflatBlocksJ3, blockChargeRow bflatBlockJ3B114 bflatBlocksJ3, blockChargeRow bflatBlockJ3B115 bflatBlocksJ3, blockChargeRow bflatBlockJ3B116 bflatBlocksJ3, blockChargeRow bflatBlockJ3B117 bflatBlocksJ3, blockChargeRow bflatBlockJ3B118 bflatBlocksJ3, blockChargeRow bflatBlockJ3B119 bflatBlocksJ3, blockChargeRow bflatBlockJ3B120 bflatBlocksJ3, blockChargeRow bflatBlockJ3B121 bflatBlocksJ3, blockChargeRow bflatBlockJ3B122 bflatBlocksJ3] = _
    rw [block_charge_row_j3_b0,
      block_charge_row_j3_b1,
      block_charge_row_j3_b2,
      block_charge_row_j3_b3,
      block_charge_row_j3_b4,
      block_charge_row_j3_b5,
      block_charge_row_j3_b6,
      block_charge_row_j3_b7,
      block_charge_row_j3_b8,
      block_charge_row_j3_b9,
      block_charge_row_j3_b10,
      block_charge_row_j3_b11,
      block_charge_row_j3_b12,
      block_charge_row_j3_b13,
      block_charge_row_j3_b14,
      block_charge_row_j3_b15,
      block_charge_row_j3_b16,
      block_charge_row_j3_b17,
      block_charge_row_j3_b18,
      block_charge_row_j3_b19,
      block_charge_row_j3_b20,
      block_charge_row_j3_b21,
      block_charge_row_j3_b22,
      block_charge_row_j3_b23,
      block_charge_row_j3_b24,
      block_charge_row_j3_b25,
      block_charge_row_j3_b26,
      block_charge_row_j3_b27,
      block_charge_row_j3_b28,
      block_charge_row_j3_b29,
      block_charge_row_j3_b30,
      block_charge_row_j3_b31,
      block_charge_row_j3_b32,
      block_charge_row_j3_b33,
      block_charge_row_j3_b34,
      block_charge_row_j3_b35,
      block_charge_row_j3_b36,
      block_charge_row_j3_b37,
      block_charge_row_j3_b38,
      block_charge_row_j3_b39,
      block_charge_row_j3_b40,
      block_charge_row_j3_b41,
      block_charge_row_j3_b42,
      block_charge_row_j3_b43,
      block_charge_row_j3_b44,
      block_charge_row_j3_b45,
      block_charge_row_j3_b46,
      block_charge_row_j3_b47,
      block_charge_row_j3_b48,
      block_charge_row_j3_b49,
      block_charge_row_j3_b50,
      block_charge_row_j3_b51,
      block_charge_row_j3_b52,
      block_charge_row_j3_b53,
      block_charge_row_j3_b54,
      block_charge_row_j3_b55,
      block_charge_row_j3_b56,
      block_charge_row_j3_b57,
      block_charge_row_j3_b58,
      block_charge_row_j3_b59,
      block_charge_row_j3_b60,
      block_charge_row_j3_b61,
      block_charge_row_j3_b62,
      block_charge_row_j3_b63,
      block_charge_row_j3_b64,
      block_charge_row_j3_b65,
      block_charge_row_j3_b66,
      block_charge_row_j3_b67,
      block_charge_row_j3_b68,
      block_charge_row_j3_b69,
      block_charge_row_j3_b70,
      block_charge_row_j3_b71,
      block_charge_row_j3_b72,
      block_charge_row_j3_b73,
      block_charge_row_j3_b74,
      block_charge_row_j3_b75,
      block_charge_row_j3_b76,
      block_charge_row_j3_b77,
      block_charge_row_j3_b78,
      block_charge_row_j3_b79,
      block_charge_row_j3_b80,
      block_charge_row_j3_b81,
      block_charge_row_j3_b82,
      block_charge_row_j3_b83,
      block_charge_row_j3_b84,
      block_charge_row_j3_b85,
      block_charge_row_j3_b86,
      block_charge_row_j3_b87,
      block_charge_row_j3_b88,
      block_charge_row_j3_b89,
      block_charge_row_j3_b90,
      block_charge_row_j3_b91,
      block_charge_row_j3_b92,
      block_charge_row_j3_b93,
      block_charge_row_j3_b94,
      block_charge_row_j3_b95,
      block_charge_row_j3_b96,
      block_charge_row_j3_b97,
      block_charge_row_j3_b98,
      block_charge_row_j3_b99,
      block_charge_row_j3_b100,
      block_charge_row_j3_b101,
      block_charge_row_j3_b102,
      block_charge_row_j3_b103,
      block_charge_row_j3_b104,
      block_charge_row_j3_b105,
      block_charge_row_j3_b106,
      block_charge_row_j3_b107,
      block_charge_row_j3_b108,
      block_charge_row_j3_b109,
      block_charge_row_j3_b110,
      block_charge_row_j3_b111,
      block_charge_row_j3_b112,
      block_charge_row_j3_b113,
      block_charge_row_j3_b114,
      block_charge_row_j3_b115,
      block_charge_row_j3_b116,
      block_charge_row_j3_b117,
      block_charge_row_j3_b118,
      block_charge_row_j3_b119,
      block_charge_row_j3_b120,
      block_charge_row_j3_b121,
      block_charge_row_j3_b122]
  change (bflatBlocksJ3.map (fun a => blockChargeRow a bflatBlocksJ3)).sum = _
  rw [hrows]
  decide +kernel
theorem bflat_lower_j3 : blockLowerSum bflatBlocksJ3 = (1996796649127349043391/2000000000000000000000 : ℚ) := by
  decide +kernel
/-- Exact q3 covariance-integral cap, with a positive block majorant. -/
theorem bflat_cap_j3 : 2-2*q3Projection 3 256 < ((29/500 : ℚ) : ℝ) := by
  have h := block_certificate_sound 3 256 bflatBlocksJ3 block_cover_j3
    (List.all_eq_true.mp all_blocks_entries_j3) (List.all_eq_true.mp all_blocks_mass_j3)
  rw [bflat_lower_j3,bflat_charge_j3] at h
  have hc : (2-2*(1996796649127349043391/2000000000000000000000 : ℚ)^2+(64202439152110007249889431/1250000000000000000000000000 : ℚ) : ℚ) < (29/500 : ℚ) := by decide +kernel
  exact h.trans_lt (by exact_mod_cast hc)
end ASDExplicitGamma.Numerics.Model
