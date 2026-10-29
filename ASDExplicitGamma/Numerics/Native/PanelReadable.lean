module
public import ASDExplicitGamma.Numerics.Native.PanelNodes

/-! A readable real formula for the OLD panel with its boundary-only correction.
The general D is 1+3^(-1/4); no Df substitution or panelwise minimum occurs here.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics.Mirror

noncomputable def nativeOldBoundaryPanel
    (v a2 kap kd op om betaPlus betaMinus x y delta meanslope xislope H0 a0 xi0 ybar s : ℝ) : ℝ :=
  let b : ℝ := 3683/2500
  let eps : ℝ := 3/10^46
  let s2 := Real.sqrt 2
  let s3 := Real.sqrt 3
  let z4 := Real.sqrt s3
  let z8 := Real.sqrt (Real.sqrt (Real.sqrt 105))
  let alpha := 1/z4
  let D := 1+alpha
  let H := (Real.sqrt (H0+delta*s)+Real.sqrt (2*v*s)*(z4*Real.sqrt b+z8*Real.sqrt eps))^2
  let abar := a0+meanslope*s
  let xi := xi0+xislope*s
  let t := Real.sqrt xi
  let m := 1+2*H+Real.sqrt (2*H)
  let tm := Real.sqrt (D*m*H)
  let bm := Real.sqrt (b*m)
  let co := bm+1
  let q2 := Real.sqrt ((b+1)^2*op^2+bm^2*om^2)
  let L := s2*t*x*op+2*s2*tm*y*om+b*op^2+m*om^2+2*kd*(t*y+s2*co*om)
  let K := kap^2*b
  let AV := 2*kap*t*Real.sqrt v+2*kap*q2+2*kd*D*kap*b*s2
  let AG := 2*kd*(t*(x+y)/s2+D*b*op+co*om)
  let AVG := 2*kd*D*kap*b
  let err := L+K*xi+AV*t+AG*s2*t+AVG*xi+2*betaPlus*t+2*betaMinus*s2*t
  let aff := ybar/2*abar+2*v*(b-1)+(4+2*s2)*(156/5)*a2/9
  aff+err

theorem nativePanelValue_readable
    (v a2 kap kd op om betaPlus betaMinus x y delta meanslope xislope H0 a0 xi0 ybar s : ℝ) :
    nativePanelValue [v,a2,kap,kd,op,om,betaPlus,betaMinus,x,y,delta,meanslope,xislope,H0,a0,xi0,ybar] s =
      nativeOldBoundaryPanel v a2 kap kd op om betaPlus betaMinus x y delta meanslope xislope H0 a0 xi0 ybar s := by
  rw [nativePanelValue_node]
  let inputs : List ℝ := [s,ybar,xi0,a0,H0,xislope,meanslope,delta,y,x,betaMinus,betaPlus,om,op,kd,kap,a2,v]
  obtain ⟨b,hbdef⟩ : ∃ z : ℝ, z = 3683/2500 := ⟨_,rfl⟩
  obtain ⟨eps,hepsdef⟩ : ∃ z : ℝ, z = 3/10^46 := ⟨_,rfl⟩
  obtain ⟨s2,hs2def⟩ : ∃ z : ℝ, z = Real.sqrt 2 := ⟨_,rfl⟩
  obtain ⟨s3,hs3def⟩ : ∃ z : ℝ, z = Real.sqrt 3 := ⟨_,rfl⟩
  obtain ⟨z4,hz4def⟩ : ∃ z : ℝ, z = Real.sqrt s3 := ⟨_,rfl⟩
  obtain ⟨z8,hz8def⟩ : ∃ z : ℝ, z = Real.sqrt (Real.sqrt (Real.sqrt 105)) := ⟨_,rfl⟩
  obtain ⟨alpha,halphadef⟩ : ∃ z : ℝ, z = 1/z4 := ⟨_,rfl⟩
  obtain ⟨D,hDdef⟩ : ∃ z : ℝ, z = 1+alpha := ⟨_,rfl⟩
  obtain ⟨H,hHdef⟩ : ∃ z : ℝ, z = (Real.sqrt (H0+delta*s)+Real.sqrt (2*v*s)*(z4*Real.sqrt b+z8*Real.sqrt eps))^2 := ⟨_,rfl⟩
  obtain ⟨abar,habardef⟩ : ∃ z : ℝ, z = a0+meanslope*s := ⟨_,rfl⟩
  obtain ⟨xi,hxidef⟩ : ∃ z : ℝ, z = xi0+xislope*s := ⟨_,rfl⟩
  obtain ⟨t,htdef⟩ : ∃ z : ℝ, z = Real.sqrt xi := ⟨_,rfl⟩
  obtain ⟨m,hmdef⟩ : ∃ z : ℝ, z = 1+2*H+Real.sqrt (2*H) := ⟨_,rfl⟩
  obtain ⟨tm,htmdef⟩ : ∃ z : ℝ, z = Real.sqrt (D*m*H) := ⟨_,rfl⟩
  obtain ⟨bm,hbmdef⟩ : ∃ z : ℝ, z = Real.sqrt (b*m) := ⟨_,rfl⟩
  obtain ⟨co,hcodef⟩ : ∃ z : ℝ, z = bm+1 := ⟨_,rfl⟩
  obtain ⟨q2,hq2def⟩ : ∃ z : ℝ, z = Real.sqrt ((b+1)^2*op^2+bm^2*om^2) := ⟨_,rfl⟩
  obtain ⟨L,hLdef⟩ : ∃ z : ℝ, z = s2*t*x*op+2*s2*tm*y*om+b*op^2+m*om^2+2*kd*(t*y+s2*co*om) := ⟨_,rfl⟩
  obtain ⟨K,hKdef⟩ : ∃ z : ℝ, z = kap^2*b := ⟨_,rfl⟩
  obtain ⟨AV,hAVdef⟩ : ∃ z : ℝ, z = 2*kap*t*Real.sqrt v+2*kap*q2+2*kd*D*kap*b*s2 := ⟨_,rfl⟩
  obtain ⟨AG,hAGdef⟩ : ∃ z : ℝ, z = 2*kd*(t*(x+y)/s2+D*b*op+co*om) := ⟨_,rfl⟩
  obtain ⟨AVG,hAVGdef⟩ : ∃ z : ℝ, z = 2*kd*D*kap*b := ⟨_,rfl⟩
  obtain ⟨err,herrdef⟩ : ∃ z : ℝ, z = L+K*xi+AV*t+AG*s2*t+AVG*xi+2*betaPlus*t+2*betaMinus*s2*t := ⟨_,rfl⟩
  obtain ⟨aff,haffdef⟩ : ∃ z : ℝ, z = ybar/2*abar+2*v*(b-1)+(4+2*s2)*(156/5)*a2/9 := ⟨_,rfl⟩
  have hs2 : nativePanelNode001 inputs = s2 := by
    norm_num only [nativePanelNode001,nativePanelNode000,inputs,hbdef,hepsdef,hs2def,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hs3 : nativePanelNode003 inputs = s3 := by
    norm_num only [nativePanelNode003,nativePanelNode002,hs2,inputs,hbdef,hepsdef,hs3def,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hz4 : nativePanelNode004 inputs = z4 := by
    norm_num only [nativePanelNode004,hs2,hs3,inputs,hbdef,hepsdef,hz4def,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hz8 : nativePanelNode008 inputs = z8 := by
    norm_num only [nativePanelNode008,nativePanelNode007,nativePanelNode006,nativePanelNode005,hs2,hs3,hz4,inputs,hbdef,hepsdef,hz8def,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have halpha : nativePanelNode010 inputs = alpha := by
    norm_num only [nativePanelNode010,nativePanelNode009,hs2,hs3,hz4,hz8,inputs,hbdef,hepsdef,halphadef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hD : nativePanelNode011 inputs = D := by
    norm_num only [nativePanelNode011,nativePanelNode009,hs2,hs3,hz4,hz8,halpha,inputs,hbdef,hepsdef,hDdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm]
  have hH : nativePanelNode028 inputs = H := by
    norm_num only [nativePanelNode028,nativePanelNode027,nativePanelNode009,nativePanelNode026,nativePanelNode014,nativePanelNode013,nativePanelNode012,nativePanelNode025,nativePanelNode017,nativePanelNode016,nativePanelNode015,nativePanelNode000,nativePanelNode024,nativePanelNode020,nativePanelNode019,nativePanelNode018,nativePanelNode023,nativePanelNode022,nativePanelNode021,hs2,hs3,hz4,hz8,halpha,hD,inputs,hbdef,hepsdef,hHdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [mul_comm,mul_left_comm]
  have hat : nativePanelNode030 inputs = abar := by
    norm_num only [nativePanelNode030,nativePanelNode029,hs2,hs3,hz4,hz8,halpha,hD,hH,inputs,hbdef,hepsdef,habardef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hxi : nativePanelNode032 inputs = xi := by
    norm_num only [nativePanelNode032,nativePanelNode031,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,inputs,hbdef,hepsdef,hxidef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have ht : nativePanelNode033 inputs = t := by
    norm_num only [nativePanelNode033,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,inputs,hbdef,hepsdef,htdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hm : nativePanelNode037 inputs = m := by
    norm_num only [nativePanelNode037,nativePanelNode035,nativePanelNode034,nativePanelNode000,nativePanelNode009,nativePanelNode036,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,inputs,hbdef,hepsdef,hmdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,add_assoc,mul_comm]
  have htm : nativePanelNode040 inputs = tm := by
    norm_num only [nativePanelNode040,nativePanelNode039,nativePanelNode038,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,inputs,hbdef,hepsdef,htmdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hbm : nativePanelNode042 inputs = bm := by
    norm_num only [nativePanelNode042,nativePanelNode041,nativePanelNode018,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,inputs,hbdef,hepsdef,hbmdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [mul_comm]
  have hco : nativePanelNode043 inputs = co := by
    norm_num only [nativePanelNode043,nativePanelNode009,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,inputs,hbdef,hepsdef,hcodef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hq2 : nativePanelNode054 inputs = q2 := by
    norm_num only [nativePanelNode054,nativePanelNode053,nativePanelNode047,nativePanelNode045,nativePanelNode044,nativePanelNode009,nativePanelNode046,nativePanelNode052,nativePanelNode049,nativePanelNode048,nativePanelNode051,nativePanelNode050,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,inputs,hbdef,hepsdef,hq2def,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,mul_comm,mul_left_comm,mul_assoc]
  have hL : nativePanelNode073 inputs = L := by
    norm_num only [nativePanelNode073,nativePanelNode066,nativePanelNode064,nativePanelNode062,nativePanelNode057,nativePanelNode056,nativePanelNode055,nativePanelNode061,nativePanelNode060,nativePanelNode059,nativePanelNode058,nativePanelNode000,nativePanelNode063,nativePanelNode045,nativePanelNode044,nativePanelNode009,nativePanelNode018,nativePanelNode065,nativePanelNode051,nativePanelNode050,nativePanelNode072,nativePanelNode067,nativePanelNode071,nativePanelNode068,nativePanelNode070,nativePanelNode069,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,inputs,hbdef,hepsdef,hLdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc]
  have hK : nativePanelNode076 inputs = K := by
    norm_num only [nativePanelNode076,nativePanelNode075,nativePanelNode074,nativePanelNode009,nativePanelNode018,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,inputs,hbdef,hepsdef,hKdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  have hAV : nativePanelNode087 inputs = AV := by
    norm_num only [nativePanelNode087,nativePanelNode082,nativePanelNode080,nativePanelNode078,nativePanelNode077,nativePanelNode000,nativePanelNode079,nativePanelNode081,nativePanelNode086,nativePanelNode085,nativePanelNode084,nativePanelNode083,nativePanelNode067,nativePanelNode018,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,hK,inputs,hbdef,hepsdef,hAVdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,add_left_comm,mul_comm,mul_left_comm,mul_assoc]
  have hAG : nativePanelNode096 inputs = AG := by
    norm_num only [nativePanelNode096,nativePanelNode067,nativePanelNode000,nativePanelNode095,nativePanelNode093,nativePanelNode090,nativePanelNode089,nativePanelNode088,nativePanelNode092,nativePanelNode091,nativePanelNode018,nativePanelNode094,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,hK,hAV,inputs,hbdef,hepsdef,hAGdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,mul_comm,mul_assoc]
  have hAVG : nativePanelNode085 inputs = AVG := by
    norm_num only [nativePanelNode085,nativePanelNode084,nativePanelNode083,nativePanelNode067,nativePanelNode000,nativePanelNode018,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,hK,hAV,hAG,inputs,hbdef,hepsdef,hAVGdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [mul_comm,mul_left_comm,mul_assoc]
  have herr : nativePanelNode112 inputs = err := by
    norm_num only [nativePanelNode112,nativePanelNode108,nativePanelNode105,nativePanelNode103,nativePanelNode100,nativePanelNode098,nativePanelNode097,nativePanelNode099,nativePanelNode102,nativePanelNode101,nativePanelNode104,nativePanelNode107,nativePanelNode106,nativePanelNode000,nativePanelNode111,nativePanelNode110,nativePanelNode109,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,hK,hAV,hAG,hAVG,inputs,hbdef,hepsdef,herrdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm]
  have haff : nativePanelNode125 inputs = aff := by
    norm_num only [nativePanelNode125,nativePanelNode117,nativePanelNode114,nativePanelNode113,nativePanelNode000,nativePanelNode116,nativePanelNode015,nativePanelNode115,nativePanelNode124,nativePanelNode122,nativePanelNode121,nativePanelNode119,nativePanelNode058,nativePanelNode118,nativePanelNode120,nativePanelNode123,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,hK,hAV,hAG,hAVG,herr,inputs,hbdef,hepsdef,haffdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
    all_goals simp only [add_comm,add_left_comm,mul_comm,mul_assoc]
  have hresult : nativePanelNode126 inputs = aff+err := by
    norm_num only [nativePanelNode126,hs2,hs3,hz4,hz8,halpha,hD,hH,hat,hxi,ht,hm,htm,hbm,hco,hq2,hL,hK,hAV,hAG,hAVG,herr,haff,inputs,hbdef,hepsdef,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,one_mul,pow_two]
  apply hresult.trans
  symm
  dsimp only [nativeOldBoundaryPanel]
  rw [← hbdef,← hepsdef,← hs2def,← hs3def,← hz4def,← hz8def,← halphadef,← hDdef,← hHdef,← habardef,← hxidef,← htdef,← hmdef,← htmdef,← hbmdef,← hcodef,← hq2def,← hLdef,← hKdef,← hAVdef,← hAGdef,← hAVGdef,← herrdef,← haffdef]

end ASDExplicitGamma.Numerics.Native
