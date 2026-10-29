module
public import ASDExplicitGamma.Numerics.Cold.History

/-! Rowwise kernel checks of the outward depth-history formula.
The finite rows here keep each exact rational normalization within
Lean's default heartbeat budget. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Cold

/- Each row is checked in pieces of 16 terms of its depth-weighted sum, against exact intermediate
values: a whole row in one kernel check peaked at 7.4 GiB (row 128); a 16-term piece stays far below
the 6 GiB compile cap. The pieces are elaborated one at a time so that they are not held together. -/
set_option Elab.async false

private theorem coldHistory_foldl_range_split (F : ℚ → ℕ → ℚ) (a b : ℕ) (h : ℚ) :
    (List.range (a + b)).foldl F h = ((List.range b).map (a + ·)).foldl F ((List.range a).foldl F h) := by
  rw [List.range_add, List.foldl_append]

private theorem cold_history_row_100_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (4834679711715413908097851029933582798689/100000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_100_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (9847028604935110526783723576346230951367/200000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_100_prefix_16]
  decide +kernel

private theorem cold_history_row_100_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (49251158569265722371546993027245453612917/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_100_prefix_32]
  decide +kernel

private theorem cold_history_row_100_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (6156429926971896859103248659600751592989/125000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_100_prefix_48]
  decide +kernel

private theorem cold_history_row_100_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (1231286103743821677222112802316277096367/25000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_100_prefix_64]
  decide +kernel

private theorem cold_history_row_100_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (49251446110740479862188305742901531758461/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_100_prefix_80]
  decide +kernel

private theorem cold_history_row_100_prefix_100 :
    (List.range 100).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 100 r)) 0 =
      (49251491892709311935040902804991101957967/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 100 = List.range (96 + 4) from rfl, coldHistory_foldl_range_split, cold_history_row_100_prefix_96]
  decide +kernel

theorem cold_history_row_100 : coldHistoryAt 100 = coldHistoryExpected 100 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_100_prefix_100]
  decide +kernel

private theorem cold_history_row_102_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (46161523129320989872374795837892388430499/1000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_102_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (23505690817629464267306662533541808390171/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_102_prefix_16]
  decide +kernel

private theorem cold_history_row_102_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (4702674311502637198735411508565779793849/100000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_102_prefix_32]
  decide +kernel

private theorem cold_history_row_102_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (47027013374255377833265001319551541212843/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_102_prefix_48]
  decide +kernel

private theorem cold_history_row_102_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (11756754489187094296783676653247813603509/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_102_prefix_64]
  decide +kernel

private theorem cold_history_row_102_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (47027018237166946240174248794831972169933/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_102_prefix_80]
  decide +kernel

private theorem cold_history_row_102_prefix_102 :
    (List.range 102).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 102 r)) 0 =
      (23513526157193296227340174876836597455669/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 102 = List.range (96 + 6) from rfl, coldHistory_foldl_range_split, cold_history_row_102_prefix_96]
  decide +kernel

theorem cold_history_row_102 : coldHistoryAt 102 = coldHistoryExpected 102 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_102_prefix_102]
  decide +kernel

private theorem cold_history_row_104_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (11016679304181224126488021208926847938809/250000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_104_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (44879551205635523779726330778102427432517/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_104_prefix_16]
  decide +kernel

private theorem cold_history_row_104_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (8978856114061576975556988630324938514957/200000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_104_prefix_32]
  decide +kernel

private theorem cold_history_row_104_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (44894540524563363467210453551663952823097/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_104_prefix_48]
  decide +kernel

private theorem cold_history_row_104_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (44894544956307657027017600817315087849627/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_104_prefix_64]
  decide +kernel

private theorem cold_history_row_104_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (22447272524583730515204669417215813660551/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_104_prefix_80]
  decide +kernel

private theorem cold_history_row_104_prefix_104 :
    (List.range 104).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 104 r)) 0 =
      (1795782787451579729361016240130436161131/40000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 104 = List.range (96 + 8) from rfl, coldHistory_foldl_range_split, cold_history_row_104_prefix_96]
  decide +kernel

theorem cold_history_row_104 : coldHistoryAt 104 = coldHistoryExpected 104 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_104_prefix_104]
  decide +kernel

private theorem cold_history_row_106_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (4205929029284998855161829051718367967569/100000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_106_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (21418261548979870454783849634043224328807/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_106_prefix_16]
  decide +kernel

private theorem cold_history_row_106_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (21425320955571966842885189599145270274309/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_106_prefix_32]
  decide +kernel

private theorem cold_history_row_106_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (21425445925011542793961323178269454005967/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_106_prefix_48]
  decide +kernel

private theorem cold_history_row_106_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (42850896132398518652152610428894245824747/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_106_prefix_64]
  decide +kernel

private theorem cold_history_row_106_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (21425448101657982939589335401308720472023/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_106_prefix_80]
  decide +kernel

private theorem cold_history_row_106_prefix_106 :
    (List.range 106).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 106 r)) 0 =
      (21425456968680376708976621350930029660083/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 106 = List.range (96 + 10) from rfl, coldHistory_foldl_range_split, cold_history_row_106_prefix_96]
  decide +kernel

theorem cold_history_row_106 : coldHistoryAt 106 = coldHistoryExpected 106 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_106_prefix_106]
  decide +kernel

private theorem cold_history_row_108_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (20068109119929368410181836457875498224861/500000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_108_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (4087923347208036869787758725989218523231/100000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_108_prefix_16]
  decide +kernel

private theorem cold_history_row_108_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (20446381446498991744331414953989647169253/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_108_prefix_32]
  decide +kernel

private theorem cold_history_row_108_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (127790634707689067163460509539834222663/3125000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_108_prefix_48]
  decide +kernel

private theorem cold_history_row_108_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (40893007241414854478839635080366193110227/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_108_prefix_64]
  decide +kernel

private theorem cold_history_row_108_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (20446503654294748434055792069194971324053/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_108_prefix_80]
  decide +kernel

private theorem cold_history_row_108_prefix_108 :
    (List.range 108).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 108 r)) 0 =
      (20446510032579890338144069593724359557413/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 108 = List.range (96 + 12) from rfl, coldHistory_foldl_range_split, cold_history_row_108_prefix_96]
  decide +kernel

theorem cold_history_row_108 : coldHistoryAt 108 = coldHistoryExpected 108 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_108_prefix_108]
  decide +kernel

private theorem cold_history_row_110_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (38294533611662625632408148281068965028091/1000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_110_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (9751168775856406892804250078380200080099/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_110_prefix_16]
  decide +kernel

private theorem cold_history_row_110_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (2438602241691784668545645566778400388779/62500000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_110_prefix_32]
  decide +kernel

private theorem cold_history_row_110_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (19508933322837454872557247628874067409279/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_110_prefix_48]
  decide +kernel

private theorem cold_history_row_110_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (4877233829440790759833879449023292742001/125000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_110_prefix_64]
  decide +kernel

private theorem cold_history_row_110_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (39017870700846344870861026948510921899879/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_110_prefix_80]
  decide +kernel

private theorem cold_history_row_110_prefix_110 :
    (List.range 110).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 110 r)) 0 =
      (975446996902399143853147602401357282349/25000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 110 = List.range (96 + 14) from rfl, coldHistory_foldl_range_split, cold_history_row_110_prefix_96]
  decide +kernel

theorem cold_history_row_110 : coldHistoryAt 110 = coldHistoryExpected 110 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_110_prefix_110]
  decide +kernel

private theorem cold_history_row_112_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (7306267108348536139708448909145268866069/200000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_112_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (37209907395618199593147669640044311841211/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_112_prefix_16]
  decide +kernel

private theorem cold_history_row_112_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (18611159899142406162808553059678229467683/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_112_prefix_32]
  decide +kernel

private theorem cold_history_row_112_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (7444508286157672815925774880851683715977/200000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_112_prefix_48]
  decide +kernel

private theorem cold_history_row_112_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (3722254527808930761028665218282287667429/100000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_112_prefix_64]
  decide +kernel

private theorem cold_history_row_112_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (18611272670831914626479457288749821831939/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_112_prefix_80]
  decide +kernel

private theorem cold_history_row_112_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 112 r)) 0 =
      (18611275970493304378601808524976224174019/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_112_prefix_96]
  decide +kernel

theorem cold_history_row_112 : coldHistoryAt 112 = coldHistoryExpected 112 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_112_prefix_112]
  decide +kernel

private theorem cold_history_row_114_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (17421893077331801990375094956621634229351/500000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_114_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (35492052890393730555795814326442243367487/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_16]
  decide +kernel

private theorem cold_history_row_114_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (7100787355262946163667524355623622951549/200000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_32]
  decide +kernel

private theorem cold_history_row_114_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (4438018693629441509911483482662029957389/125000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_48]
  decide +kernel

private theorem cold_history_row_114_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (35504153256675494241478365112176033626331/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_64]
  decide +kernel

private theorem cold_history_row_114_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (35504153318460335404612806894688710589217/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_80]
  decide +kernel

private theorem cold_history_row_114_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (17752077268690845013283257059383024807149/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_96]
  decide +kernel

private theorem cold_history_row_114_prefix_114 :
    (List.range 114).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 114 r)) 0 =
      (17752079032549123894275580641748173057661/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 114 = List.range (112 + 2) from rfl, coldHistory_foldl_range_split, cold_history_row_114_prefix_112]
  decide +kernel

theorem cold_history_row_114 : coldHistoryAt 114 = coldHistoryExpected 114 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_114_prefix_114]
  decide +kernel

private theorem cold_history_row_116_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (1661455548748046545548351584602250980791/50000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_116_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (6769659553393105368063207435515800010609/200000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_16]
  decide +kernel

private theorem cold_history_row_116_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (16929836258942933555636600516815724052473/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_32]
  decide +kernel

private theorem cold_history_row_116_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (16929938357091544337524774816781653250093/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_48]
  decide +kernel

private theorem cold_history_row_116_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (8464970071305980592347373381171610802079/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_64]
  decide +kernel

private theorem cold_history_row_116_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (33859880345172458037336683390026577171921/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_80]
  decide +kernel

private theorem cold_history_row_116_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (16929940240692371073784968974553090099883/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_96]
  decide +kernel

private theorem cold_history_row_116_prefix_116 :
    (List.range 116).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 116 r)) 0 =
      (33859883759313844932380948619118168187483/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 116 = List.range (112 + 4) from rfl, coldHistory_foldl_range_split, cold_history_row_116_prefix_112]
  decide +kernel

theorem cold_history_row_116 : coldHistoryAt 116 = coldHistoryExpected 116 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_116_prefix_116]
  decide +kernel

private theorem cold_history_row_118_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (31684599527670225588133438982806541348629/1000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_118_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (16137946263123596879391267351882587063483/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_16]
  decide +kernel

private theorem cold_history_row_118_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (8071694263161116677899145021065565268883/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_32]
  decide +kernel

private theorem cold_history_row_118_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (16143486475903539153510520493387452614761/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_48]
  decide +kernel

private theorem cold_history_row_118_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (8071744097384344052261577908908554500091/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_64]
  decide +kernel

private theorem cold_history_row_118_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (32286976447623161931465728115266925932661/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_80]
  decide +kernel

private theorem cold_history_row_118_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (16143488231767219103531688411340056924851/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_96]
  decide +kernel

private theorem cold_history_row_118_prefix_118 :
    (List.range 118).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 118 r)) 0 =
      (32286978903401564735615204025612146444101/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 118 = List.range (112 + 6) from rfl, coldHistory_foldl_range_split, cold_history_row_118_prefix_112]
  decide +kernel

theorem cold_history_row_118 : coldHistoryAt 118 = coldHistoryExpected 118 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_118_prefix_118]
  decide +kernel

private theorem cold_history_row_120_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (30207605829904509974160518289442591553491/1000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_120_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (15386076279510410665275172018902263311933/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_16]
  decide +kernel

private theorem cold_history_row_120_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (15391282466003719243497512205472764499313/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_32]
  decide +kernel

private theorem cold_history_row_120_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (15391376404533603847059771830972876406367/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_48]
  decide +kernel

private theorem cold_history_row_120_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (30782756116934485622487301386362731181577/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_64]
  decide +kernel

private theorem cold_history_row_120_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (3847844521644409955345298164791611032319/125000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_80]
  decide +kernel

private theorem cold_history_row_120_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (7695689043923477080288383997093371552443/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_96]
  decide +kernel

private theorem cold_history_row_120_prefix_120 :
    (List.range 120).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 120 r)) 0 =
      (6156551587930142509756945736853031785843/200000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 120 = List.range (112 + 8) from rfl, coldHistory_foldl_range_split, cold_history_row_120_prefix_112]
  decide +kernel

theorem cold_history_row_120 : coldHistoryAt 120 = coldHistoryExpected 120 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_120_prefix_120]
  decide +kernel

private theorem cold_history_row_122_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (14397774968028177109969627863591896182567/500000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_122_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (14667229650436223391515698552408748782347/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_16]
  decide +kernel

private theorem cold_history_row_122_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (14672208696967603462385746176272025419767/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_32]
  decide +kernel

private theorem cold_history_row_122_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (29344597519725797899400000556702292039719/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_48]
  decide +kernel

private theorem cold_history_row_122_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (29344600701252521092315081178046540762327/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_64]
  decide +kernel

private theorem cold_history_row_122_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (1173784030224708266349052910000966875949/40000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_80]
  decide +kernel

private theorem cold_history_row_122_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (14672300378329835642157152558251227759653/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_96]
  decide +kernel

private theorem cold_history_row_122_prefix_122 :
    (List.range 122).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 122 r)) 0 =
      (29344602026357495945559518241937472280213/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 122 = List.range (112 + 10) from rfl, coldHistory_foldl_range_split, cold_history_row_122_prefix_112]
  decide +kernel

theorem cold_history_row_122 : coldHistoryAt 122 = coldHistoryExpected 122 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_122_prefix_122]
  decide +kernel

private theorem cold_history_row_124_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (1372295960143864094897650319241039984163/50000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_124_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (3495032749234580823958220344057371044307/125000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_16]
  decide +kernel

private theorem cold_history_row_124_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (27969783323367746632664511017374915516489/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_32]
  decide +kernel

private theorem cold_history_row_124_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (13984977981913396299889456100606766659239/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_48]
  decide +kernel

private theorem cold_history_row_124_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (27969959022581765148017012687914349360723/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_64]
  decide +kernel

private theorem cold_history_row_124_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (27969959075110087599682979204658601460853/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_80]
  decide +kernel

private theorem cold_history_row_124_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (27969959075971269962927582872634150023713/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_96]
  decide +kernel

private theorem cold_history_row_124_prefix_124 :
    (List.range 124).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 124 r)) 0 =
      (3496244998660419989335309859623355162663/125000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 124 = List.range (112 + 12) from rfl, coldHistory_foldl_range_split, cold_history_row_124_prefix_112]
  decide +kernel

theorem cold_history_row_124 : coldHistoryAt 124 = coldHistoryExpected 124 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_124_prefix_124]
  decide +kernel

private theorem cold_history_row_126_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (2615626866077797484002170532374395437447/100000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_126_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (13323539236582157126030060312723922485773/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_16]
  decide +kernel

private theorem cold_history_row_126_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (13328090031240331307592042719756110848187/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_32]
  decide +kernel

private theorem cold_history_row_126_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (266563454784421859203186546879804044663/10000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_48]
  decide +kernel

private theorem cold_history_row_126_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (6664087104498395624731148691300724952491/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_64]
  decide +kernel

private theorem cold_history_row_126_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (6664087117177342524373242854667590106047/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_80]
  decide +kernel

private theorem cold_history_row_126_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (26656348469534047972901851502986285517671/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_96]
  decide +kernel

private theorem cold_history_row_126_prefix_126 :
    (List.range 126).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 126 r)) 0 =
      (1332817456321244012122963463565601694637/50000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 126 = List.range (112 + 14) from rfl, coldHistory_foldl_range_split, cold_history_row_126_prefix_112]
  decide +kernel

theorem cold_history_row_126 : coldHistoryAt 126 = coldHistoryExpected 126 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_126_prefix_126]
  decide +kernel

private theorem cold_history_row_128_prefix_16 :
    (List.range 16).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (6231055463560519268668234299880434907711/250000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

private theorem cold_history_row_128_prefix_32 :
    (List.range 32).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (12696247963631172337227821886477432400683/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 32 = List.range (16 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_16]
  decide +kernel

private theorem cold_history_row_128_prefix_48 :
    (List.range 48).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (6350298576630211893537497344311168435953/250000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 48 = List.range (32 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_32]
  decide +kernel

private theorem cold_history_row_128_prefix_64 :
    (List.range 64).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (25401352753478293605231540434181153151109/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 64 = List.range (48 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_48]
  decide +kernel

private theorem cold_history_row_128_prefix_80 :
    (List.range 80).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (25401355577402535580047092613632093633603/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 80 = List.range (64 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_64]
  decide +kernel

private theorem cold_history_row_128_prefix_96 :
    (List.range 96).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (12700677813167662667294171005548573832041/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 96 = List.range (80 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_80]
  decide +kernel

private theorem cold_history_row_128_prefix_112 :
    (List.range 112).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (12700677813568892329881636564139077660589/500000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 112 = List.range (96 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_96]
  decide +kernel

private theorem cold_history_row_128_prefix_128 :
    (List.range 128).foldl (fun hist r => coldUpAdd hist (coldHistoryChoice 128 r)) 0 =
      (25401356099593344659274491294027494441953/1000000000000000000000000000000000000000000 : ℚ) := by
  rw [show List.range 128 = List.range (112 + 16) from rfl, coldHistory_foldl_range_split, cold_history_row_128_prefix_112]
  decide +kernel

theorem cold_history_row_128 : coldHistoryAt 128 = coldHistoryExpected 128 := by
  unfold coldHistoryExpected coldHistoryWeightedSum
  rw [cold_history_row_128_prefix_128]
  decide +kernel

end ASDExplicitGamma.Numerics.Cold
