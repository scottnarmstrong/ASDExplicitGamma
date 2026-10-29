module

public import ASDExplicitGamma.Numerics.Inverse.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invCov0Ar : ℚ := (558569601750757646795356981643455040825607189 / 200000000000000000000000000000000000000000000 : ℚ)

def invCov0BA : ℚ := (5027126415756818821158212834791095367430464701 / 625000000000000000000000000000000000000000000 : ℚ)

def invCov0BB : ℚ := (17773575892318349115694614939350789159476735683 / 3125000000000000000000000000000000000000000000 : ℚ)

def invCov0CA : ℚ := (1228981334276481190203153301701752195507661710283 / 100000000000000000000000000000000000000000000000 : ℚ)

def invCov0CB : ℚ := (1738042070837182007711449207315282937879721381591 / 200000000000000000000000000000000000000000000000 : ℚ)

def invCov0K0 : ℚ := (39 / 10 : ℚ)

def invCov0K1 : ℚ := (124097240098239090532348185549401006394488707119 / 7812500000000000000000000000000000000000000000 : ℚ)

def invCov0K2 : ℚ := (785949187288847573371538508479539707165095145087 / 125000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0_coefficient_roots :
    0 < invCov0Ar ∧ (78/5/2 : ℚ) < invCov0Ar^2 ∧ 0 < invCov0BA ∧ (1.440 : ℚ)^2*(2*78/5) < invCov0BA^2 ∧ 0 < invCov0BB ∧ (1.440 : ℚ)^2*(78/5) < invCov0BB^2 ∧ 0 < invCov0CA ∧ (0.285 : ℚ)^2*(2*(3432/5+(78/5)^2)) < invCov0CA^2 ∧ 0 < invCov0CB ∧ (0.285 : ℚ)^2*(3432/5+(78/5)^2) < invCov0CB^2 := by
  decide +kernel

def invCov0A1 : ℚ := invCov0Ar*(1 / 3 : ℚ)+invCov0BA*(1 / 243 : ℚ)+invCov0CA*(1 / 243 : ℚ)^2

def invCov0B1 : ℚ := invCov0Ar*(1 / 3 : ℚ)+invCov0BB*(1 / 243 : ℚ)+invCov0CB*(1 / 243 : ℚ)^2

def invCov0RowK1 : ℚ := invCov0K0*(1 / 3 : ℚ)^2+invCov0K1*(1 / 3 : ℚ)*(1 / 243 : ℚ)+invCov0K2*(1 / 243 : ℚ)^2

def invCov0Mu1 : ℚ := (1475897433710421256089335362465801450094690182967810261364678524868824167214687559284230379321267115649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu1_root :
    0 < invCov0Mu1 ∧ 0 ≤ 2*invCov0Mu1-invCov0A1^2 ∧ invCov0A1^4+4*(63/50)^2*invCov0A1^2*invCov0B1^2 < (2*invCov0Mu1-invCov0A1^2)^2 := by
  decide +kernel

def invCov0A2 : ℚ := invCov0Ar*(1 / 9 : ℚ)+invCov0BA*(1 / 243 : ℚ)+invCov0CA*(1 / 243 : ℚ)^2

def invCov0B2 : ℚ := invCov0Ar*(1 / 9 : ℚ)+invCov0BB*(1 / 243 : ℚ)+invCov0CB*(1 / 243 : ℚ)^2

def invCov0RowK2 : ℚ := invCov0K0*(1 / 9 : ℚ)^2+invCov0K1*(1 / 9 : ℚ)*(1 / 243 : ℚ)+invCov0K2*(1 / 243 : ℚ)^2

def invCov0Mu2 : ℚ := (185260337886577009330430611593945135825819804846874107853050726711950952735966603967111238119782381649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu2_root :
    0 < invCov0Mu2 ∧ 0 ≤ 2*invCov0Mu2-invCov0A2^2 ∧ invCov0A2^4+4*(63/50)^2*invCov0A2^2*invCov0B2^2 < (2*invCov0Mu2-invCov0A2^2)^2 := by
  decide +kernel

def invCov0A3 : ℚ := invCov0Ar*(1 / 27 : ℚ)+invCov0BA*(1 / 243 : ℚ)+invCov0CA*(1 / 243 : ℚ)^2

def invCov0B3 : ℚ := invCov0Ar*(1 / 27 : ℚ)+invCov0BB*(1 / 243 : ℚ)+invCov0CB*(1 / 243 : ℚ)^2

def invCov0RowK3 : ℚ := invCov0K0*(1 / 27 : ℚ)^2+invCov0K1*(1 / 27 : ℚ)*(1 / 243 : ℚ)+invCov0K2*(1 / 243 : ℚ)^2

def invCov0Mu3 : ℚ := (28535434407382652080885213350817377702738229354337613638003567308445596105310280620163459625936803649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu3_root :
    0 < invCov0Mu3 ∧ 0 ≤ 2*invCov0Mu3-invCov0A3^2 ∧ invCov0A3^4+4*(63/50)^2*invCov0A3^2*invCov0B3^2 < (2*invCov0Mu3-invCov0A3^2)^2 := by
  decide +kernel

def invCov0A4 : ℚ := invCov0Ar*(1 / 81 : ℚ)+invCov0BA*(1 / 243 : ℚ)+invCov0CA*(1 / 243 : ℚ)^2

def invCov0B4 : ℚ := invCov0Ar*(1 / 81 : ℚ)+invCov0BB*(1 / 243 : ℚ)+invCov0CB*(1 / 243 : ℚ)^2

def invCov0RowK4 : ℚ := invCov0K0*(1 / 81 : ℚ)^2+invCov0K1*(1 / 81 : ℚ)*(1 / 243 : ℚ)+invCov0K2*(1 / 243 : ℚ)^2

def invCov0Mu4 : ℚ := (6681675846999388348739044269275035311006820512901061153968822320105186287193431551783674413912277649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu4_root :
    0 < invCov0Mu4 ∧ 0 ≤ 2*invCov0Mu4-invCov0A4^2 ∧ invCov0A4^4+4*(63/50)^2*invCov0A4^2*invCov0B4^2 < (2*invCov0Mu4-invCov0A4^2)^2 := by
  decide +kernel

def invCov0A5 : ℚ := invCov0Ar*(1 / 243 : ℚ)+invCov0BA*(1 / 243 : ℚ)+invCov0CA*(1 / 243 : ℚ)^2

def invCov0B5 : ℚ := invCov0Ar*(1 / 243 : ℚ)+invCov0BB*(1 / 243 : ℚ)+invCov0CB*(1 / 243 : ℚ)^2

def invCov0RowK5 : ℚ := invCov0K0*(1 / 243 : ℚ)^2+invCov0K1*(1 / 243 : ℚ)*(1 / 243 : ℚ)+invCov0K2*(1 / 243 : ℚ)^2

def invCov0Mu5 : ℚ := (2773885548424069444339973846432613316441424876087109835695867488380017354350992089798132041673435649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu5_root :
    0 < invCov0Mu5 ∧ 0 ≤ 2*invCov0Mu5-invCov0A5^2 ∧ invCov0A5^4+4*(63/50)^2*invCov0A5^2*invCov0B5^2 < (2*invCov0Mu5-invCov0A5^2)^2 := by
  decide +kernel

def invCov0A6 : ℚ := invCov0Ar*(1 / 729 : ℚ)+invCov0BA*(1 / 729 : ℚ)+invCov0CA*(1 / 729 : ℚ)^2

def invCov0B6 : ℚ := invCov0Ar*(1 / 729 : ℚ)+invCov0BB*(1 / 729 : ℚ)+invCov0CB*(1 / 729 : ℚ)^2

def invCov0RowK6 : ℚ := invCov0K0*(1 / 729 : ℚ)^2+invCov0K1*(1 / 729 : ℚ)*(1 / 729 : ℚ)+invCov0K2*(1 / 729 : ℚ)^2

def invCov0Mu6 : ℚ := (24814628769044304458599310563886364047609060587364270829000760150708830505621428173774481264310952209 / 69735688020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu6_root :
    0 < invCov0Mu6 ∧ 0 ≤ 2*invCov0Mu6-invCov0A6^2 ∧ invCov0A6^4+4*(63/50)^2*invCov0A6^2*invCov0B6^2 < (2*invCov0Mu6-invCov0A6^2)^2 := by
  decide +kernel

def invCov0A7 : ℚ := invCov0Ar*(1 / 2187 : ℚ)+invCov0BA*(1 / 2187 : ℚ)+invCov0CA*(1 / 2187 : ℚ)^2

def invCov0B7 : ℚ := invCov0Ar*(1 / 2187 : ℚ)+invCov0BB*(1 / 2187 : ℚ)+invCov0CB*(1 / 2187 : ℚ)^2

def invCov0RowK7 : ℚ := invCov0K0*(1 / 2187 : ℚ)^2+invCov0K1*(1 / 2187 : ℚ)*(1 / 2187 : ℚ)+invCov0K2*(1 / 2187 : ℚ)^2

def invCov0Mu7 : ℚ := (222881543356715667624845888049462526088402468140571585443142989433996985977541367131174720162228257089 / 5648590729620000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu7_root :
    0 < invCov0Mu7 ∧ 0 ≤ 2*invCov0Mu7-invCov0A7^2 ∧ invCov0A7^4+4*(63/50)^2*invCov0A7^2*invCov0B7^2 < (2*invCov0Mu7-invCov0A7^2)^2 := by
  decide +kernel

def invCov0A8 : ℚ := invCov0Ar*(1 / 6561 : ℚ)+invCov0BA*(1 / 6561 : ℚ)+invCov0CA*(1 / 6561 : ℚ)^2

def invCov0B8 : ℚ := invCov0Ar*(1 / 6561 : ℚ)+invCov0BB*(1 / 6561 : ℚ)+invCov0CB*(1 / 6561 : ℚ)^2

def invCov0RowK8 : ℚ := invCov0K0*(1 / 6561 : ℚ)^2+invCov0K1*(1 / 6561 : ℚ)*(1 / 6561 : ℚ)+invCov0K2*(1 / 6561 : ℚ)^2

def invCov0Mu8 : ℚ := (2004584451451854587873286519755998226571027681741310323993617638950576896556278860352616157926022968529 / 457535849099220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu8_root :
    0 < invCov0Mu8 ∧ 0 ≤ 2*invCov0Mu8-invCov0A8^2 ∧ invCov0A8^4+4*(63/50)^2*invCov0A8^2*invCov0B8^2 < (2*invCov0Mu8-invCov0A8^2)^2 := by
  decide +kernel

def invCov0A9 : ℚ := invCov0Ar*(1 / 19683 : ℚ)+invCov0BA*(1 / 19683 : ℚ)+invCov0CA*(1 / 19683 : ℚ)^2

def invCov0B9 : ℚ := invCov0Ar*(1 / 19683 : ℚ)+invCov0BB*(1 / 19683 : ℚ)+invCov0CB*(1 / 19683 : ℚ)^2

def invCov0RowK9 : ℚ := invCov0K0*(1 / 19683 : ℚ)^2+invCov0K1*(1 / 19683 : ℚ)*(1 / 19683 : ℚ)+invCov0K2*(1 / 19683 : ℚ)^2

def invCov0Mu9 : ℚ := (18037212654726337550575911646951740746670156721748516772017473242500755625759290427160106960847792274049 / 37060403777036820000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu9_root :
    0 < invCov0Mu9 ∧ 0 ≤ 2*invCov0Mu9-invCov0A9^2 ∧ invCov0A9^4+4*(63/50)^2*invCov0A9^2*invCov0B9^2 < (2*invCov0Mu9-invCov0A9^2)^2 := by
  decide +kernel

def invCov0A10 : ℚ := invCov0Ar*(1 / 59049 : ℚ)+invCov0BA*(1 / 59049 : ℚ)+invCov0CA*(1 / 59049 : ℚ)^2

def invCov0B10 : ℚ := invCov0Ar*(1 / 59049 : ℚ)+invCov0BB*(1 / 59049 : ℚ)+invCov0CB*(1 / 59049 : ℚ)^2

def invCov0RowK10 : ℚ := invCov0K0*(1 / 59049 : ℚ)^2+invCov0K1*(1 / 59049 : ℚ)*(1 / 59049 : ℚ)+invCov0K2*(1 / 59049 : ℚ)^2

def invCov0Mu10 : ℚ := (162322772575451363137474511227579480768572373764971749797440924948155242790569516911871077776286566731409 / 3001892705939982420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu10_root :
    0 < invCov0Mu10 ∧ 0 ≤ 2*invCov0Mu10-invCov0A10^2 ∧ invCov0A10^4+4*(63/50)^2*invCov0A10^2*invCov0B10^2 < (2*invCov0Mu10-invCov0A10^2)^2 := by
  decide +kernel

def invCov0A11 : ℚ := invCov0Ar*(1 / 177147 : ℚ)+invCov0BA*(1 / 177147 : ℚ)+invCov0CA*(1 / 177147 : ℚ)^2

def invCov0B11 : ℚ := invCov0Ar*(1 / 177147 : ℚ)+invCov0BB*(1 / 177147 : ℚ)+invCov0CB*(1 / 177147 : ℚ)^2

def invCov0RowK11 : ℚ := invCov0K0*(1 / 177147 : ℚ)^2+invCov0K1*(1 / 177147 : ℚ)*(1 / 177147 : ℚ)+invCov0K2*(1 / 177147 : ℚ)^2

def invCov0Mu11 : ℚ := (1460868530135740623811315439988346719068642729096476634215878244120154263079810922424600475882664088970689 / 243153309181138576020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu11_root :
    0 < invCov0Mu11 ∧ 0 ≤ 2*invCov0Mu11-invCov0A11^2 ∧ invCov0A11^4+4*(63/50)^2*invCov0A11^2*invCov0B11^2 < (2*invCov0Mu11-invCov0A11^2)^2 := by
  decide +kernel

def invCov0A12 : ℚ := invCov0Ar*(1 / 531441 : ℚ)+invCov0BA*(1 / 531441 : ℚ)+invCov0CA*(1 / 531441 : ℚ)^2

def invCov0B12 : ℚ := invCov0Ar*(1 / 531441 : ℚ)+invCov0BB*(1 / 531441 : ℚ)+invCov0CB*(1 / 531441 : ℚ)^2

def invCov0RowK12 : ℚ := invCov0K0*(1 / 531441 : ℚ)^2+invCov0K1*(1 / 531441 : ℚ)*(1 / 531441 : ℚ)+invCov0K2*(1 / 531441 : ℚ)^2

def invCov0Mu12 : ℚ := (13147707502999636058925483803722539776162553103457160539080692878131471353100831673490157041142347445493329 / 19695418043672224657620000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu12_root :
    0 < invCov0Mu12 ∧ 0 ≤ 2*invCov0Mu12-invCov0A12^2 ∧ invCov0A12^4+4*(63/50)^2*invCov0A12^2*invCov0B12^2 < (2*invCov0Mu12-invCov0A12^2)^2 := by
  decide +kernel

def invCov0A13 : ℚ := invCov0Ar*(1 / 1594323 : ℚ)+invCov0BA*(1 / 1594323 : ℚ)+invCov0CA*(1 / 1594323 : ℚ)^2

def invCov0B13 : ℚ := invCov0Ar*(1 / 1594323 : ℚ)+invCov0BB*(1 / 1594323 : ℚ)+invCov0CB*(1 / 1594323 : ℚ)^2

def invCov0RowK13 : ℚ := invCov0K0*(1 / 1594323 : ℚ)^2+invCov0K1*(1 / 1594323 : ℚ)*(1 / 1594323 : ℚ)+invCov0K2*(1 / 1594323 : ℚ)^2

def invCov0Mu13 : ℚ := (118329039723238571241393208133243313820187859600077843455790660868623302885543562737433142075386354623304449 / 1595328861537450197267220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu13_root :
    0 < invCov0Mu13 ∧ 0 ≤ 2*invCov0Mu13-invCov0A13^2 ∧ invCov0A13^4+4*(63/50)^2*invCov0A13^2*invCov0B13^2 < (2*invCov0Mu13-invCov0A13^2)^2 := by
  decide +kernel

def invCov0A14 : ℚ := invCov0Ar*(1 / 4782969 : ℚ)+invCov0BA*(1 / 4782969 : ℚ)+invCov0CA*(1 / 4782969 : ℚ)^2

def invCov0B14 : ℚ := invCov0Ar*(1 / 4782969 : ℚ)+invCov0BB*(1 / 4782969 : ℚ)+invCov0CB*(1 / 4782969 : ℚ)^2

def invCov0RowK14 : ℚ := invCov0K0*(1 / 4782969 : ℚ)^2+invCov0K1*(1 / 4782969 : ℚ)*(1 / 4782969 : ℚ)+invCov0K2*(1 / 4782969 : ℚ)^2

def invCov0Mu14 : ℚ := (1064960374098780616682687153121549200411609298515798288780680281636219719844288775225978935224302990130926609 / 129221637784533465978644820000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu14_root :
    0 < invCov0Mu14 ∧ 0 ≤ 2*invCov0Mu14-invCov0A14^2 ∧ invCov0A14^4+4*(63/50)^2*invCov0A14^2*invCov0B14^2 < (2*invCov0Mu14-invCov0A14^2)^2 := by
  decide +kernel

def invCov0A15 : ℚ := invCov0Ar*(1 / 14348907 : ℚ)+invCov0BA*(1 / 14348907 : ℚ)+invCov0CA*(1 / 14348907 : ℚ)^2

def invCov0B15 : ℚ := invCov0Ar*(1 / 14348907 : ℚ)+invCov0BB*(1 / 14348907 : ℚ)+invCov0CB*(1 / 14348907 : ℚ)^2

def invCov0RowK15 : ℚ := invCov0K0*(1 / 14348907 : ℚ)^2+invCov0K1*(1 / 14348907 : ℚ)*(1 / 14348907 : ℚ)+invCov0K2*(1 / 14348907 : ℚ)^2

def invCov0Mu15 : ℚ := (9584640416658833912051507201907016002877202780286614136079776595104097271973277586362067857086714422421492289 / 10466952660547210744270230420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu15_root :
    0 < invCov0Mu15 ∧ 0 ≤ 2*invCov0Mu15-invCov0A15^2 ∧ invCov0A15^4+4*(63/50)^2*invCov0A15^2*invCov0B15^2 < (2*invCov0Mu15-invCov0A15^2)^2 := by
  decide +kernel

def invCov0A16 : ℚ := invCov0Ar*(1 / 43046721 : ℚ)+invCov0BA*(1 / 43046721 : ℚ)+invCov0CA*(1 / 43046721 : ℚ)^2

def invCov0B16 : ℚ := invCov0Ar*(1 / 43046721 : ℚ)+invCov0BB*(1 / 43046721 : ℚ)+invCov0CB*(1 / 43046721 : ℚ)^2

def invCov0RowK16 : ℚ := invCov0K0*(1 / 43046721 : ℚ)^2+invCov0K1*(1 / 43046721 : ℚ)*(1 / 43046721 : ℚ)+invCov0K2*(1 / 43046721 : ℚ)^2

def invCov0Mu16 : ℚ := (86261754899239838229562385027871510112986674777396147175622892595993524639635022582804398504414902451202482129 / 847823165504324070285888664020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov0Mu16_root :
    0 < invCov0Mu16 ∧ 0 ≤ 2*invCov0Mu16-invCov0A16^2 ∧ invCov0A16^4+4*(63/50)^2*invCov0A16^2*invCov0B16^2 < (2*invCov0Mu16-invCov0A16^2)^2 := by
  decide +kernel

def invCov0PlainK : ℚ := (1 / 1 : ℚ)^1*invCov0RowK1 + (1 / 1 : ℚ)^2*invCov0RowK2 + (1 / 1 : ℚ)^3*invCov0RowK3 + (1 / 1 : ℚ)^4*invCov0RowK4 + (1 / 1 : ℚ)^5*invCov0RowK5 + (1 / 1 : ℚ)^6*invCov0RowK6 + (1 / 1 : ℚ)^7*invCov0RowK7 + (1 / 1 : ℚ)^8*invCov0RowK8 + (1 / 1 : ℚ)^9*invCov0RowK9 + (1 / 1 : ℚ)^10*invCov0RowK10 + (1 / 1 : ℚ)^11*invCov0RowK11 + (1 / 1 : ℚ)^12*invCov0RowK12 + (1 / 1 : ℚ)^13*invCov0RowK13 + (1 / 1 : ℚ)^14*invCov0RowK14 + (1 / 1 : ℚ)^15*invCov0RowK15 + (1 / 1 : ℚ)^16*invCov0RowK16 + (invCov0K0+invCov0K1+invCov0K2)*((1/3^(2*0) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))

def invCov0PlainM : ℚ := (1 / 1 : ℚ)^1*invCov0Mu1 + (1 / 1 : ℚ)^2*invCov0Mu2 + (1 / 1 : ℚ)^3*invCov0Mu3 + (1 / 1 : ℚ)^4*invCov0Mu4 + (1 / 1 : ℚ)^5*invCov0Mu5 + (1 / 1 : ℚ)^6*invCov0Mu6 + (1 / 1 : ℚ)^7*invCov0Mu7 + (1 / 1 : ℚ)^8*invCov0Mu8 + (1 / 1 : ℚ)^9*invCov0Mu9 + (1 / 1 : ℚ)^10*invCov0Mu10 + (1 / 1 : ℚ)^11*invCov0Mu11 + (1 / 1 : ℚ)^12*invCov0Mu12 + (1 / 1 : ℚ)^13*invCov0Mu13 + (1 / 1 : ℚ)^14*invCov0Mu14 + (1 / 1 : ℚ)^15*invCov0Mu15 + (1 / 1 : ℚ)^16*invCov0Mu16 + (233/100)*((invCov0Ar+invCov0BA)^2*((1/3^(2*0) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))+2*(invCov0Ar+invCov0BA)*invCov0CA*((1/3^(3*0) : ℚ)*((1 / 1 : ℚ)/3^3)^17/(1-(1 / 1 : ℚ)/3^3))+invCov0CA^2*((1/3^(4*0) : ℚ)*((1 / 1 : ℚ)/3^4)^17/(1-(1 / 1 : ℚ)/3^4)))

def invCov0PlainSB : ℚ := (1 / 1 : ℚ)^1*(25 / 387420489 : ℚ)*invCov0B1^2 + (1 / 1 : ℚ)^2*(25 / 43046721 : ℚ)*invCov0B2^2 + (1 / 1 : ℚ)^3*(25 / 4782969 : ℚ)*invCov0B3^2 + (1 / 1 : ℚ)^4*(25 / 531441 : ℚ)*invCov0B4^2 + (1 / 1 : ℚ)^5*(25 / 59049 : ℚ)*invCov0B5^2 + (1 / 1 : ℚ)^6*(25 / 6561 : ℚ)*invCov0B6^2 + (1 / 1 : ℚ)^7*(25 / 729 : ℚ)*invCov0B7^2 + (1 / 1 : ℚ)^8*(25 / 81 : ℚ)*invCov0B8^2 + (1 / 1 : ℚ)^9*(1 / 1 : ℚ)*invCov0B9^2 + (1 / 1 : ℚ)^10*(1 / 1 : ℚ)*invCov0B10^2 + (1 / 1 : ℚ)^11*(1 / 1 : ℚ)*invCov0B11^2 + (1 / 1 : ℚ)^12*(1 / 1 : ℚ)*invCov0B12^2 + (1 / 1 : ℚ)^13*(1 / 1 : ℚ)*invCov0B13^2 + (1 / 1 : ℚ)^14*(1 / 1 : ℚ)*invCov0B14^2 + (1 / 1 : ℚ)^15*(1 / 1 : ℚ)*invCov0B15^2 + (1 / 1 : ℚ)^16*(1 / 1 : ℚ)*invCov0B16^2 + ((invCov0Ar+invCov0BB)^2*((1/3^(2*0) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))+2*(invCov0Ar+invCov0BB)*invCov0CB*((1/3^(3*0) : ℚ)*((1 / 1 : ℚ)/3^3)^17/(1-(1 / 1 : ℚ)/3^3))+invCov0CB^2*((1/3^(4*0) : ℚ)*((1 / 1 : ℚ)/3^4)^17/(1-(1 / 1 : ℚ)/3^4)))

def invCov0PlainB2 : ℚ := (1 / 1 : ℚ)^1*(1 / 1 : ℚ)*invCov0B1^2 + (1 / 1 : ℚ)^2*(1 / 1 : ℚ)*invCov0B2^2 + (1 / 1 : ℚ)^3*(1 / 1 : ℚ)*invCov0B3^2 + (1 / 1 : ℚ)^4*(1 / 1 : ℚ)*invCov0B4^2 + (1 / 1 : ℚ)^5*(1 / 1 : ℚ)*invCov0B5^2 + (1 / 1 : ℚ)^6*(1 / 1 : ℚ)*invCov0B6^2 + (1 / 1 : ℚ)^7*(1 / 1 : ℚ)*invCov0B7^2 + (1 / 1 : ℚ)^8*(1 / 1 : ℚ)*invCov0B8^2 + (1 / 1 : ℚ)^9*(1 / 1 : ℚ)*invCov0B9^2 + (1 / 1 : ℚ)^10*(1 / 1 : ℚ)*invCov0B10^2 + (1 / 1 : ℚ)^11*(1 / 1 : ℚ)*invCov0B11^2 + (1 / 1 : ℚ)^12*(1 / 1 : ℚ)*invCov0B12^2 + (1 / 1 : ℚ)^13*(1 / 1 : ℚ)*invCov0B13^2 + (1 / 1 : ℚ)^14*(1 / 1 : ℚ)*invCov0B14^2 + (1 / 1 : ℚ)^15*(1 / 1 : ℚ)*invCov0B15^2 + (1 / 1 : ℚ)^16*(1 / 1 : ℚ)*invCov0B16^2 + ((invCov0Ar+invCov0BB)^2*((1/3^(2*0) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))+2*(invCov0Ar+invCov0BB)*invCov0CB*((1/3^(3*0) : ℚ)*((1 / 1 : ℚ)/3^3)^17/(1-(1 / 1 : ℚ)/3^3))+invCov0CB^2*((1/3^(4*0) : ℚ)*((1 / 1 : ℚ)/3^4)^17/(1-(1 / 1 : ℚ)/3^4)))

theorem invCov0_plain_caps :
    invCov0PlainK < 0.520628885 ∧ invCov0PlainM < 1.97401021 ∧ (invCov0PlainB2+invCov0PlainK) < 1.56404708 ∧ invCov0PlainSB < 0.000002644114957 := by
  decide +kernel

def invCov0WeightedK : ℚ := (250000 / 249813 : ℚ)^1*invCov0RowK1 + (250000 / 249813 : ℚ)^2*invCov0RowK2 + (250000 / 249813 : ℚ)^3*invCov0RowK3 + (250000 / 249813 : ℚ)^4*invCov0RowK4 + (250000 / 249813 : ℚ)^5*invCov0RowK5 + (250000 / 249813 : ℚ)^6*invCov0RowK6 + (250000 / 249813 : ℚ)^7*invCov0RowK7 + (250000 / 249813 : ℚ)^8*invCov0RowK8 + (250000 / 249813 : ℚ)^9*invCov0RowK9 + (250000 / 249813 : ℚ)^10*invCov0RowK10 + (250000 / 249813 : ℚ)^11*invCov0RowK11 + (250000 / 249813 : ℚ)^12*invCov0RowK12 + (250000 / 249813 : ℚ)^13*invCov0RowK13 + (250000 / 249813 : ℚ)^14*invCov0RowK14 + (250000 / 249813 : ℚ)^15*invCov0RowK15 + (250000 / 249813 : ℚ)^16*invCov0RowK16 + (invCov0K0+invCov0K1+invCov0K2)*((1/3^(2*0) : ℚ)*((250000 / 249813 : ℚ)/3^2)^17/(1-(250000 / 249813 : ℚ)/3^2))

def invCov0WeightedM : ℚ := (250000 / 249813 : ℚ)^1*invCov0Mu1 + (250000 / 249813 : ℚ)^2*invCov0Mu2 + (250000 / 249813 : ℚ)^3*invCov0Mu3 + (250000 / 249813 : ℚ)^4*invCov0Mu4 + (250000 / 249813 : ℚ)^5*invCov0Mu5 + (250000 / 249813 : ℚ)^6*invCov0Mu6 + (250000 / 249813 : ℚ)^7*invCov0Mu7 + (250000 / 249813 : ℚ)^8*invCov0Mu8 + (250000 / 249813 : ℚ)^9*invCov0Mu9 + (250000 / 249813 : ℚ)^10*invCov0Mu10 + (250000 / 249813 : ℚ)^11*invCov0Mu11 + (250000 / 249813 : ℚ)^12*invCov0Mu12 + (250000 / 249813 : ℚ)^13*invCov0Mu13 + (250000 / 249813 : ℚ)^14*invCov0Mu14 + (250000 / 249813 : ℚ)^15*invCov0Mu15 + (250000 / 249813 : ℚ)^16*invCov0Mu16 + (233/100)*((invCov0Ar+invCov0BA)^2*((1/3^(2*0) : ℚ)*((250000 / 249813 : ℚ)/3^2)^17/(1-(250000 / 249813 : ℚ)/3^2))+2*(invCov0Ar+invCov0BA)*invCov0CA*((1/3^(3*0) : ℚ)*((250000 / 249813 : ℚ)/3^3)^17/(1-(250000 / 249813 : ℚ)/3^3))+invCov0CA^2*((1/3^(4*0) : ℚ)*((250000 / 249813 : ℚ)/3^4)^17/(1-(250000 / 249813 : ℚ)/3^4)))

def invCov0WeightedB2 : ℚ := (250000 / 249813 : ℚ)^1*(1 / 1 : ℚ)*invCov0B1^2 + (250000 / 249813 : ℚ)^2*(1 / 1 : ℚ)*invCov0B2^2 + (250000 / 249813 : ℚ)^3*(1 / 1 : ℚ)*invCov0B3^2 + (250000 / 249813 : ℚ)^4*(1 / 1 : ℚ)*invCov0B4^2 + (250000 / 249813 : ℚ)^5*(1 / 1 : ℚ)*invCov0B5^2 + (250000 / 249813 : ℚ)^6*(1 / 1 : ℚ)*invCov0B6^2 + (250000 / 249813 : ℚ)^7*(1 / 1 : ℚ)*invCov0B7^2 + (250000 / 249813 : ℚ)^8*(1 / 1 : ℚ)*invCov0B8^2 + (250000 / 249813 : ℚ)^9*(1 / 1 : ℚ)*invCov0B9^2 + (250000 / 249813 : ℚ)^10*(1 / 1 : ℚ)*invCov0B10^2 + (250000 / 249813 : ℚ)^11*(1 / 1 : ℚ)*invCov0B11^2 + (250000 / 249813 : ℚ)^12*(1 / 1 : ℚ)*invCov0B12^2 + (250000 / 249813 : ℚ)^13*(1 / 1 : ℚ)*invCov0B13^2 + (250000 / 249813 : ℚ)^14*(1 / 1 : ℚ)*invCov0B14^2 + (250000 / 249813 : ℚ)^15*(1 / 1 : ℚ)*invCov0B15^2 + (250000 / 249813 : ℚ)^16*(1 / 1 : ℚ)*invCov0B16^2 + ((invCov0Ar+invCov0BB)^2*((1/3^(2*0) : ℚ)*((250000 / 249813 : ℚ)/3^2)^17/(1-(250000 / 249813 : ℚ)/3^2))+2*(invCov0Ar+invCov0BB)*invCov0CB*((1/3^(3*0) : ℚ)*((250000 / 249813 : ℚ)/3^3)^17/(1-(250000 / 249813 : ℚ)/3^3))+invCov0CB^2*((1/3^(4*0) : ℚ)*((250000 / 249813 : ℚ)/3^4)^17/(1-(250000 / 249813 : ℚ)/3^4)))

theorem invCov0_weighted_hazard :
    invCov0WeightedK > 0.521 ∧ invCov0WeightedM > 1.975 ∧ (invCov0WeightedB2+invCov0WeightedK) > 1.565 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
