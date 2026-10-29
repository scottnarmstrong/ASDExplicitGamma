module

public import ASDExplicitGamma.Numerics.Inverse.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invCov1Ar : ℚ := (558569601750757646795356981643455040825607189 / 200000000000000000000000000000000000000000000 : ℚ)

def invCov1BA : ℚ := (5027126415756818821158212834791095367430464701 / 625000000000000000000000000000000000000000000 : ℚ)

def invCov1BB : ℚ := (17773575892318349115694614939350789159476735683 / 3125000000000000000000000000000000000000000000 : ℚ)

def invCov1CA : ℚ := (1228981334276481190203153301701752195507661710283 / 100000000000000000000000000000000000000000000000 : ℚ)

def invCov1CB : ℚ := (1738042070837182007711449207315282937879721381591 / 200000000000000000000000000000000000000000000000 : ℚ)

def invCov1K0 : ℚ := (39 / 10 : ℚ)

def invCov1K1 : ℚ := (124097240098239090532348185549401006394488707119 / 7812500000000000000000000000000000000000000000 : ℚ)

def invCov1K2 : ℚ := (785949187288847573371538508479539707165095145087 / 125000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1_mixed_roots :
    0 < invCov1K1 ∧ (1.440*(78/5) : ℚ)^2/2 < invCov1K1^2 ∧ 0 < invCov1K2 ∧ (0.285*(78/5) : ℚ)^2*2 < invCov1K2^2 := by
  decide +kernel

def invCov1A1 : ℚ := invCov1Ar*(1 / 9 : ℚ)+invCov1BA*(1 / 243 : ℚ)+invCov1CA*(1 / 243 : ℚ)^2

def invCov1B1 : ℚ := invCov1Ar*(1 / 9 : ℚ)+invCov1BB*(1 / 243 : ℚ)+invCov1CB*(1 / 243 : ℚ)^2

def invCov1RowK1 : ℚ := invCov1K0*(1 / 9 : ℚ)^2+invCov1K1*(1 / 9 : ℚ)*(1 / 243 : ℚ)+invCov1K2*(1 / 243 : ℚ)^2

def invCov1Mu1 : ℚ := (185260337886577009330430611593945135825819804846874107853050726711950952735966603967111238119782381649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu1_root :
    0 < invCov1Mu1 ∧ 0 ≤ 2*invCov1Mu1-invCov1A1^2 ∧ invCov1A1^4+4*(63/50)^2*invCov1A1^2*invCov1B1^2 < (2*invCov1Mu1-invCov1A1^2)^2 := by
  decide +kernel

def invCov1A2 : ℚ := invCov1Ar*(1 / 27 : ℚ)+invCov1BA*(1 / 243 : ℚ)+invCov1CA*(1 / 243 : ℚ)^2

def invCov1B2 : ℚ := invCov1Ar*(1 / 27 : ℚ)+invCov1BB*(1 / 243 : ℚ)+invCov1CB*(1 / 243 : ℚ)^2

def invCov1RowK2 : ℚ := invCov1K0*(1 / 27 : ℚ)^2+invCov1K1*(1 / 27 : ℚ)*(1 / 243 : ℚ)+invCov1K2*(1 / 243 : ℚ)^2

def invCov1Mu2 : ℚ := (28535434407382652080885213350817377702738229354337613638003567308445596105310280620163459625936803649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu2_root :
    0 < invCov1Mu2 ∧ 0 ≤ 2*invCov1Mu2-invCov1A2^2 ∧ invCov1A2^4+4*(63/50)^2*invCov1A2^2*invCov1B2^2 < (2*invCov1Mu2-invCov1A2^2)^2 := by
  decide +kernel

def invCov1A3 : ℚ := invCov1Ar*(1 / 81 : ℚ)+invCov1BA*(1 / 243 : ℚ)+invCov1CA*(1 / 243 : ℚ)^2

def invCov1B3 : ℚ := invCov1Ar*(1 / 81 : ℚ)+invCov1BB*(1 / 243 : ℚ)+invCov1CB*(1 / 243 : ℚ)^2

def invCov1RowK3 : ℚ := invCov1K0*(1 / 81 : ℚ)^2+invCov1K1*(1 / 81 : ℚ)*(1 / 243 : ℚ)+invCov1K2*(1 / 243 : ℚ)^2

def invCov1Mu3 : ℚ := (6681675846999388348739044269275035311006820512901061153968822320105186287193431551783674413912277649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu3_root :
    0 < invCov1Mu3 ∧ 0 ≤ 2*invCov1Mu3-invCov1A3^2 ∧ invCov1A3^4+4*(63/50)^2*invCov1A3^2*invCov1B3^2 < (2*invCov1Mu3-invCov1A3^2)^2 := by
  decide +kernel

def invCov1A4 : ℚ := invCov1Ar*(1 / 243 : ℚ)+invCov1BA*(1 / 243 : ℚ)+invCov1CA*(1 / 243 : ℚ)^2

def invCov1B4 : ℚ := invCov1Ar*(1 / 243 : ℚ)+invCov1BB*(1 / 243 : ℚ)+invCov1CB*(1 / 243 : ℚ)^2

def invCov1RowK4 : ℚ := invCov1K0*(1 / 243 : ℚ)^2+invCov1K1*(1 / 243 : ℚ)*(1 / 243 : ℚ)+invCov1K2*(1 / 243 : ℚ)^2

def invCov1Mu4 : ℚ := (2773885548424069444339973846432613316441424876087109835695867488380017354350992089798132041673435649 / 860934420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu4_root :
    0 < invCov1Mu4 ∧ 0 ≤ 2*invCov1Mu4-invCov1A4^2 ∧ invCov1A4^4+4*(63/50)^2*invCov1A4^2*invCov1B4^2 < (2*invCov1Mu4-invCov1A4^2)^2 := by
  decide +kernel

def invCov1A5 : ℚ := invCov1Ar*(1 / 729 : ℚ)+invCov1BA*(1 / 729 : ℚ)+invCov1CA*(1 / 729 : ℚ)^2

def invCov1B5 : ℚ := invCov1Ar*(1 / 729 : ℚ)+invCov1BB*(1 / 729 : ℚ)+invCov1CB*(1 / 729 : ℚ)^2

def invCov1RowK5 : ℚ := invCov1K0*(1 / 729 : ℚ)^2+invCov1K1*(1 / 729 : ℚ)*(1 / 729 : ℚ)+invCov1K2*(1 / 729 : ℚ)^2

def invCov1Mu5 : ℚ := (24814628769044304458599310563886364047609060587364270829000760150708830505621428173774481264310952209 / 69735688020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu5_root :
    0 < invCov1Mu5 ∧ 0 ≤ 2*invCov1Mu5-invCov1A5^2 ∧ invCov1A5^4+4*(63/50)^2*invCov1A5^2*invCov1B5^2 < (2*invCov1Mu5-invCov1A5^2)^2 := by
  decide +kernel

def invCov1A6 : ℚ := invCov1Ar*(1 / 2187 : ℚ)+invCov1BA*(1 / 2187 : ℚ)+invCov1CA*(1 / 2187 : ℚ)^2

def invCov1B6 : ℚ := invCov1Ar*(1 / 2187 : ℚ)+invCov1BB*(1 / 2187 : ℚ)+invCov1CB*(1 / 2187 : ℚ)^2

def invCov1RowK6 : ℚ := invCov1K0*(1 / 2187 : ℚ)^2+invCov1K1*(1 / 2187 : ℚ)*(1 / 2187 : ℚ)+invCov1K2*(1 / 2187 : ℚ)^2

def invCov1Mu6 : ℚ := (222881543356715667624845888049462526088402468140571585443142989433996985977541367131174720162228257089 / 5648590729620000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu6_root :
    0 < invCov1Mu6 ∧ 0 ≤ 2*invCov1Mu6-invCov1A6^2 ∧ invCov1A6^4+4*(63/50)^2*invCov1A6^2*invCov1B6^2 < (2*invCov1Mu6-invCov1A6^2)^2 := by
  decide +kernel

def invCov1A7 : ℚ := invCov1Ar*(1 / 6561 : ℚ)+invCov1BA*(1 / 6561 : ℚ)+invCov1CA*(1 / 6561 : ℚ)^2

def invCov1B7 : ℚ := invCov1Ar*(1 / 6561 : ℚ)+invCov1BB*(1 / 6561 : ℚ)+invCov1CB*(1 / 6561 : ℚ)^2

def invCov1RowK7 : ℚ := invCov1K0*(1 / 6561 : ℚ)^2+invCov1K1*(1 / 6561 : ℚ)*(1 / 6561 : ℚ)+invCov1K2*(1 / 6561 : ℚ)^2

def invCov1Mu7 : ℚ := (2004584451451854587873286519755998226571027681741310323993617638950576896556278860352616157926022968529 / 457535849099220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu7_root :
    0 < invCov1Mu7 ∧ 0 ≤ 2*invCov1Mu7-invCov1A7^2 ∧ invCov1A7^4+4*(63/50)^2*invCov1A7^2*invCov1B7^2 < (2*invCov1Mu7-invCov1A7^2)^2 := by
  decide +kernel

def invCov1A8 : ℚ := invCov1Ar*(1 / 19683 : ℚ)+invCov1BA*(1 / 19683 : ℚ)+invCov1CA*(1 / 19683 : ℚ)^2

def invCov1B8 : ℚ := invCov1Ar*(1 / 19683 : ℚ)+invCov1BB*(1 / 19683 : ℚ)+invCov1CB*(1 / 19683 : ℚ)^2

def invCov1RowK8 : ℚ := invCov1K0*(1 / 19683 : ℚ)^2+invCov1K1*(1 / 19683 : ℚ)*(1 / 19683 : ℚ)+invCov1K2*(1 / 19683 : ℚ)^2

def invCov1Mu8 : ℚ := (18037212654726337550575911646951740746670156721748516772017473242500755625759290427160106960847792274049 / 37060403777036820000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu8_root :
    0 < invCov1Mu8 ∧ 0 ≤ 2*invCov1Mu8-invCov1A8^2 ∧ invCov1A8^4+4*(63/50)^2*invCov1A8^2*invCov1B8^2 < (2*invCov1Mu8-invCov1A8^2)^2 := by
  decide +kernel

def invCov1A9 : ℚ := invCov1Ar*(1 / 59049 : ℚ)+invCov1BA*(1 / 59049 : ℚ)+invCov1CA*(1 / 59049 : ℚ)^2

def invCov1B9 : ℚ := invCov1Ar*(1 / 59049 : ℚ)+invCov1BB*(1 / 59049 : ℚ)+invCov1CB*(1 / 59049 : ℚ)^2

def invCov1RowK9 : ℚ := invCov1K0*(1 / 59049 : ℚ)^2+invCov1K1*(1 / 59049 : ℚ)*(1 / 59049 : ℚ)+invCov1K2*(1 / 59049 : ℚ)^2

def invCov1Mu9 : ℚ := (162322772575451363137474511227579480768572373764971749797440924948155242790569516911871077776286566731409 / 3001892705939982420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu9_root :
    0 < invCov1Mu9 ∧ 0 ≤ 2*invCov1Mu9-invCov1A9^2 ∧ invCov1A9^4+4*(63/50)^2*invCov1A9^2*invCov1B9^2 < (2*invCov1Mu9-invCov1A9^2)^2 := by
  decide +kernel

def invCov1A10 : ℚ := invCov1Ar*(1 / 177147 : ℚ)+invCov1BA*(1 / 177147 : ℚ)+invCov1CA*(1 / 177147 : ℚ)^2

def invCov1B10 : ℚ := invCov1Ar*(1 / 177147 : ℚ)+invCov1BB*(1 / 177147 : ℚ)+invCov1CB*(1 / 177147 : ℚ)^2

def invCov1RowK10 : ℚ := invCov1K0*(1 / 177147 : ℚ)^2+invCov1K1*(1 / 177147 : ℚ)*(1 / 177147 : ℚ)+invCov1K2*(1 / 177147 : ℚ)^2

def invCov1Mu10 : ℚ := (1460868530135740623811315439988346719068642729096476634215878244120154263079810922424600475882664088970689 / 243153309181138576020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu10_root :
    0 < invCov1Mu10 ∧ 0 ≤ 2*invCov1Mu10-invCov1A10^2 ∧ invCov1A10^4+4*(63/50)^2*invCov1A10^2*invCov1B10^2 < (2*invCov1Mu10-invCov1A10^2)^2 := by
  decide +kernel

def invCov1A11 : ℚ := invCov1Ar*(1 / 531441 : ℚ)+invCov1BA*(1 / 531441 : ℚ)+invCov1CA*(1 / 531441 : ℚ)^2

def invCov1B11 : ℚ := invCov1Ar*(1 / 531441 : ℚ)+invCov1BB*(1 / 531441 : ℚ)+invCov1CB*(1 / 531441 : ℚ)^2

def invCov1RowK11 : ℚ := invCov1K0*(1 / 531441 : ℚ)^2+invCov1K1*(1 / 531441 : ℚ)*(1 / 531441 : ℚ)+invCov1K2*(1 / 531441 : ℚ)^2

def invCov1Mu11 : ℚ := (13147707502999636058925483803722539776162553103457160539080692878131471353100831673490157041142347445493329 / 19695418043672224657620000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu11_root :
    0 < invCov1Mu11 ∧ 0 ≤ 2*invCov1Mu11-invCov1A11^2 ∧ invCov1A11^4+4*(63/50)^2*invCov1A11^2*invCov1B11^2 < (2*invCov1Mu11-invCov1A11^2)^2 := by
  decide +kernel

def invCov1A12 : ℚ := invCov1Ar*(1 / 1594323 : ℚ)+invCov1BA*(1 / 1594323 : ℚ)+invCov1CA*(1 / 1594323 : ℚ)^2

def invCov1B12 : ℚ := invCov1Ar*(1 / 1594323 : ℚ)+invCov1BB*(1 / 1594323 : ℚ)+invCov1CB*(1 / 1594323 : ℚ)^2

def invCov1RowK12 : ℚ := invCov1K0*(1 / 1594323 : ℚ)^2+invCov1K1*(1 / 1594323 : ℚ)*(1 / 1594323 : ℚ)+invCov1K2*(1 / 1594323 : ℚ)^2

def invCov1Mu12 : ℚ := (118329039723238571241393208133243313820187859600077843455790660868623302885543562737433142075386354623304449 / 1595328861537450197267220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu12_root :
    0 < invCov1Mu12 ∧ 0 ≤ 2*invCov1Mu12-invCov1A12^2 ∧ invCov1A12^4+4*(63/50)^2*invCov1A12^2*invCov1B12^2 < (2*invCov1Mu12-invCov1A12^2)^2 := by
  decide +kernel

def invCov1A13 : ℚ := invCov1Ar*(1 / 4782969 : ℚ)+invCov1BA*(1 / 4782969 : ℚ)+invCov1CA*(1 / 4782969 : ℚ)^2

def invCov1B13 : ℚ := invCov1Ar*(1 / 4782969 : ℚ)+invCov1BB*(1 / 4782969 : ℚ)+invCov1CB*(1 / 4782969 : ℚ)^2

def invCov1RowK13 : ℚ := invCov1K0*(1 / 4782969 : ℚ)^2+invCov1K1*(1 / 4782969 : ℚ)*(1 / 4782969 : ℚ)+invCov1K2*(1 / 4782969 : ℚ)^2

def invCov1Mu13 : ℚ := (1064960374098780616682687153121549200411609298515798288780680281636219719844288775225978935224302990130926609 / 129221637784533465978644820000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu13_root :
    0 < invCov1Mu13 ∧ 0 ≤ 2*invCov1Mu13-invCov1A13^2 ∧ invCov1A13^4+4*(63/50)^2*invCov1A13^2*invCov1B13^2 < (2*invCov1Mu13-invCov1A13^2)^2 := by
  decide +kernel

def invCov1A14 : ℚ := invCov1Ar*(1 / 14348907 : ℚ)+invCov1BA*(1 / 14348907 : ℚ)+invCov1CA*(1 / 14348907 : ℚ)^2

def invCov1B14 : ℚ := invCov1Ar*(1 / 14348907 : ℚ)+invCov1BB*(1 / 14348907 : ℚ)+invCov1CB*(1 / 14348907 : ℚ)^2

def invCov1RowK14 : ℚ := invCov1K0*(1 / 14348907 : ℚ)^2+invCov1K1*(1 / 14348907 : ℚ)*(1 / 14348907 : ℚ)+invCov1K2*(1 / 14348907 : ℚ)^2

def invCov1Mu14 : ℚ := (9584640416658833912051507201907016002877202780286614136079776595104097271973277586362067857086714422421492289 / 10466952660547210744270230420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu14_root :
    0 < invCov1Mu14 ∧ 0 ≤ 2*invCov1Mu14-invCov1A14^2 ∧ invCov1A14^4+4*(63/50)^2*invCov1A14^2*invCov1B14^2 < (2*invCov1Mu14-invCov1A14^2)^2 := by
  decide +kernel

def invCov1A15 : ℚ := invCov1Ar*(1 / 43046721 : ℚ)+invCov1BA*(1 / 43046721 : ℚ)+invCov1CA*(1 / 43046721 : ℚ)^2

def invCov1B15 : ℚ := invCov1Ar*(1 / 43046721 : ℚ)+invCov1BB*(1 / 43046721 : ℚ)+invCov1CB*(1 / 43046721 : ℚ)^2

def invCov1RowK15 : ℚ := invCov1K0*(1 / 43046721 : ℚ)^2+invCov1K1*(1 / 43046721 : ℚ)*(1 / 43046721 : ℚ)+invCov1K2*(1 / 43046721 : ℚ)^2

def invCov1Mu15 : ℚ := (86261754899239838229562385027871510112986674777396147175622892595993524639635022582804398504414902451202482129 / 847823165504324070285888664020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu15_root :
    0 < invCov1Mu15 ∧ 0 ≤ 2*invCov1Mu15-invCov1A15^2 ∧ invCov1A15^4+4*(63/50)^2*invCov1A15^2*invCov1B15^2 < (2*invCov1Mu15-invCov1A15^2)^2 := by
  decide +kernel

def invCov1A16 : ℚ := invCov1Ar*(1 / 129140163 : ℚ)+invCov1BA*(1 / 129140163 : ℚ)+invCov1CA*(1 / 129140163 : ℚ)^2

def invCov1B16 : ℚ := invCov1Ar*(1 / 129140163 : ℚ)+invCov1BB*(1 / 129140163 : ℚ)+invCov1CB*(1 / 129140163 : ℚ)^2

def invCov1RowK16 : ℚ := invCov1K0*(1 / 129140163 : ℚ)^2+invCov1K1*(1 / 129140163 : ℚ)*(1 / 129140163 : ℚ)+invCov1K2*(1 / 129140163 : ℚ)^2

def invCov1Mu16 : ℚ := (776355767541090451064734768873985021798785245436754327664266784143033959144093264639437965382068050124729086849 / 68673676405850249693156981785620000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invCov1Mu16_root :
    0 < invCov1Mu16 ∧ 0 ≤ 2*invCov1Mu16-invCov1A16^2 ∧ invCov1A16^4+4*(63/50)^2*invCov1A16^2*invCov1B16^2 < (2*invCov1Mu16-invCov1A16^2)^2 := by
  decide +kernel

def invCov1PlainK : ℚ := (1 / 1 : ℚ)^1*invCov1RowK1 + (1 / 1 : ℚ)^2*invCov1RowK2 + (1 / 1 : ℚ)^3*invCov1RowK3 + (1 / 1 : ℚ)^4*invCov1RowK4 + (1 / 1 : ℚ)^5*invCov1RowK5 + (1 / 1 : ℚ)^6*invCov1RowK6 + (1 / 1 : ℚ)^7*invCov1RowK7 + (1 / 1 : ℚ)^8*invCov1RowK8 + (1 / 1 : ℚ)^9*invCov1RowK9 + (1 / 1 : ℚ)^10*invCov1RowK10 + (1 / 1 : ℚ)^11*invCov1RowK11 + (1 / 1 : ℚ)^12*invCov1RowK12 + (1 / 1 : ℚ)^13*invCov1RowK13 + (1 / 1 : ℚ)^14*invCov1RowK14 + (1 / 1 : ℚ)^15*invCov1RowK15 + (1 / 1 : ℚ)^16*invCov1RowK16 + (invCov1K0+invCov1K1+invCov1K2)*((1/3^(2*1) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))

def invCov1PlainM : ℚ := (1 / 1 : ℚ)^1*invCov1Mu1 + (1 / 1 : ℚ)^2*invCov1Mu2 + (1 / 1 : ℚ)^3*invCov1Mu3 + (1 / 1 : ℚ)^4*invCov1Mu4 + (1 / 1 : ℚ)^5*invCov1Mu5 + (1 / 1 : ℚ)^6*invCov1Mu6 + (1 / 1 : ℚ)^7*invCov1Mu7 + (1 / 1 : ℚ)^8*invCov1Mu8 + (1 / 1 : ℚ)^9*invCov1Mu9 + (1 / 1 : ℚ)^10*invCov1Mu10 + (1 / 1 : ℚ)^11*invCov1Mu11 + (1 / 1 : ℚ)^12*invCov1Mu12 + (1 / 1 : ℚ)^13*invCov1Mu13 + (1 / 1 : ℚ)^14*invCov1Mu14 + (1 / 1 : ℚ)^15*invCov1Mu15 + (1 / 1 : ℚ)^16*invCov1Mu16 + (233/100)*((invCov1Ar+invCov1BA)^2*((1/3^(2*1) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))+2*(invCov1Ar+invCov1BA)*invCov1CA*((1/3^(3*1) : ℚ)*((1 / 1 : ℚ)/3^3)^17/(1-(1 / 1 : ℚ)/3^3))+invCov1CA^2*((1/3^(4*1) : ℚ)*((1 / 1 : ℚ)/3^4)^17/(1-(1 / 1 : ℚ)/3^4)))

def invCov1PlainSB : ℚ := (1 / 1 : ℚ)^1*(25 / 387420489 : ℚ)*invCov1B1^2 + (1 / 1 : ℚ)^2*(25 / 43046721 : ℚ)*invCov1B2^2 + (1 / 1 : ℚ)^3*(25 / 4782969 : ℚ)*invCov1B3^2 + (1 / 1 : ℚ)^4*(25 / 531441 : ℚ)*invCov1B4^2 + (1 / 1 : ℚ)^5*(25 / 59049 : ℚ)*invCov1B5^2 + (1 / 1 : ℚ)^6*(25 / 6561 : ℚ)*invCov1B6^2 + (1 / 1 : ℚ)^7*(25 / 729 : ℚ)*invCov1B7^2 + (1 / 1 : ℚ)^8*(25 / 81 : ℚ)*invCov1B8^2 + (1 / 1 : ℚ)^9*(1 / 1 : ℚ)*invCov1B9^2 + (1 / 1 : ℚ)^10*(1 / 1 : ℚ)*invCov1B10^2 + (1 / 1 : ℚ)^11*(1 / 1 : ℚ)*invCov1B11^2 + (1 / 1 : ℚ)^12*(1 / 1 : ℚ)*invCov1B12^2 + (1 / 1 : ℚ)^13*(1 / 1 : ℚ)*invCov1B13^2 + (1 / 1 : ℚ)^14*(1 / 1 : ℚ)*invCov1B14^2 + (1 / 1 : ℚ)^15*(1 / 1 : ℚ)*invCov1B15^2 + (1 / 1 : ℚ)^16*(1 / 1 : ℚ)*invCov1B16^2 + ((invCov1Ar+invCov1BB)^2*((1/3^(2*1) : ℚ)*((1 / 1 : ℚ)/3^2)^17/(1-(1 / 1 : ℚ)/3^2))+2*(invCov1Ar+invCov1BB)*invCov1CB*((1/3^(3*1) : ℚ)*((1 / 1 : ℚ)/3^3)^17/(1-(1 / 1 : ℚ)/3^3))+invCov1CB^2*((1/3^(4*1) : ℚ)*((1 / 1 : ℚ)/3^4)^17/(1-(1 / 1 : ℚ)/3^4)))

theorem invCov1_plain_caps :
    invCov1PlainK < 0.065399707 ∧ invCov1PlainM < 0.259713047 ∧ invCov1PlainSB < 0.000000344556052 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
