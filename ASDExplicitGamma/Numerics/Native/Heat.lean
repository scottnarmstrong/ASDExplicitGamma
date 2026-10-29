module
public import ASDExplicitGamma.Numerics.Native.Arithmetic
public import ASDExplicitGamma.Numerics.Native.State

/-! Numeric refined-child heat formulas. All old-law, individual, and parameter inputs are bound by separate concrete certificates.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativePowUp (x q : ℚ) : ℚ :=
  if q.den=1 then x^q.num.toNat else nativeRootUp (x^q.num.toNat) q.den

def nativeShiftedFrame (h : ℕ) (t : ℚ) : ℚ :=
  let r := nativeE (2*nativeGamma*h)
  let c := (r+1/r)/2
  let d := (r-1/r)/2
  nativeUp (c*t+d*nativeRootUp (t*(t+8))+4*(c-1))

def nativeHeatRQ : ℚ := nativeE (2*nativeGamma)
def nativeHeatB : ℚ := nativeHeatRQ*nativeB
def nativeHeatEps : ℚ := nativeHeatRQ*nativeEps
def nativeHeatK : ℚ := 65399707/10^9
def nativeHeatM : ℚ := 259713047/10^9
def nativeHeatSB : ℚ := 86139013/250000000000000
def nativeHeatTheta : ℚ := 3/1000

structure NativeHeatParameters where
  hp : ℚ
  gm : List ℚ
  cross : List ℚ
  deriving DecidableEq

def nativeInitialMeanMoment (p : NativeHeatParameters) (k : ℕ) : ℚ :=
  if k=0 then 1 else nativeUp (nativeQstar^k*
    nativePowUp ((nativeQstar+(50/3^9)*p.hp)/nativeQstar) ((20*(k-1 : ℕ) : ℕ)/(19 : ℚ)))

def nativeHeatVariance (h : ℕ) (old : NativeOldRow) : ℚ × ℚ :=
  (nativeUp ((1+nativeHeatTheta)*old.e*h),
    nativeUp ((1+nativeHeatTheta)*old.e*min (h : ℚ) ((max (h-8) 0 : ℕ)+(25/72 : ℚ))))

def nativeGaussianMomentStep (variance spectral : ℚ) (qm : List ℚ) (j : ℕ) : List ℚ :=
  qm ++ [nativeUp (qm.getLast!*(variance+2*(j-1 : ℕ)*spectral))]

def nativeGaussianMoments (variance spectral : ℚ) : List ℚ :=
  (List.range 20).foldl (fun qm j => nativeGaussianMomentStep variance spectral qm (j+1)) [1]

def nativeHeatInitialAt (p : NativeHeatParameters) (qm : List ℚ) (variance : ℚ) (k : ℕ) : ℚ :=
  if k=0 then 1 else if k=1 then nativeUp (nativeQstar+2*(nativeHeatB+nativeHeatEps)*variance) else
  let base := nativeUp (((List.range (k+1)).map fun j =>
    (Nat.choose k j : ℚ)*nativeInitialMeanMoment p (k-j)*(2*nativeHeatB)^j*qm.getD j 0).sum)
  let qh := (k+1)/2
  let cross := nativeUp (p.cross.getD k 0*nativeRootUp (nativeRootUp (qm.getD qh 0) qh))
  let rare := nativeUp (2*nativeHeatEps*p.gm.getD k 0*variance)
  nativeUp ((nativeRootUp base k+cross+rare)^k)

def nativeHeatInitial (p : NativeHeatParameters) (qm : List ℚ) (variance : ℚ) : List ℚ :=
  (List.range 21).map (nativeHeatInitialAt p qm variance)

structure NativeHeatFrameInputs where
  x : ℚ
  y : ℚ
  raw : ℚ
  deriving DecidableEq

def nativeHeatFrames (p : NativeHeatParameters) (old : NativeOldRow) (individual variance qn : ℚ) : NativeHeatFrameInputs :=
  let x := nativeShiftedFrame 1 (min old.x individual)
  let y := x
  let f := nativeHeatRQ*old.f
  let xp := nativeUp ((nativeRootUp x+nativeRootUp (2*nativeHeatB*p.gm.getD 20 0*variance))^2)
  let yp := nativeUp ((nativeRootUp y+nativeRootUp (2*nativeHeatB*qn+2*nativeHeatEps*p.gm.getD 20 0*variance))^2)
  let fr := nativeUp ((nativeRootUp f+nativeRootUp (2*nativeHeatB*255*variance))^2)
  ⟨xp,yp,fr⟩

def nativeHeatExpArg (old : NativeOldRow) : ℚ :=
  old.e*(2*nativeHeatK*nativeHeatB+nativeHeatM*nativeHeatB^2)

def nativeHeatExpUpper (c : ℚ) : ℚ :=
  nativeUp ((((List.range 49).map fun j => c^j/(Nat.factorial j : ℚ)).sum)+
    c^49/(Nat.factorial 49 : ℚ)/(1-c/50))

def nativeHeatCoefficients (ee : ℚ) : List ℚ :=
  (List.range 21).map fun j => nativeUp ((Nat.choose 20 j : ℚ)*ee^j*(4*(ee-1))^(20-j))

def nativeHeatBase (coef init : List ℚ) : ℚ :=
  nativeUp ((List.zipWith (·*·) coef init).sum)

def nativeHeatRareJ (frames : NativeHeatFrameInputs) (j l : ℕ) : ℚ :=
  nativeUp (nativeHeatEps^j*frames.x^l*
    (if l=20 then nativePowUp (frames.raw/frames.x) ((j*20 : ℕ)/(108 : ℚ)) else 1))

def nativeHeatFixedAt (old : NativeOldRow) (frames : NativeHeatFrameInputs) (k : ℕ) : ℚ :=
  let j1prev := nativeHeatRareJ frames 1 (k-1)
  let j1 := nativeHeatRareJ frames 1 k
  let j2prev := nativeHeatRareJ frames 2 (k-1)
  let j2 := nativeHeatRareJ frames 2 k
  let er := (k : ℚ)*old.e*((2*nativeHeatK+2*nativeHeatB*nativeHeatM)*(4*j1prev+j1)+nativeHeatM*(4*j2prev+j2))
  let er := if k≥2 then er+2*k*(k-1)*old.e*nativeHeatSB*(1+1/nativeHeatTheta)*
    (2*nativeHeatB*(4*j1prev+j1)+4*j2prev+j2) else er
  nativeUp er

def nativeHeatForcingAt (old : NativeOldRow) (frames : NativeHeatFrameInputs) (fixed : List ℚ) (y : ℚ) (k : ℕ) : ℚ :=
  let er := fixed.getD (k-1) 0
  let er := if k≥2 then er+2*k*(k-1)*old.e*nativeHeatSB*(1+1/nativeHeatTheta)*
    nativeHeatB^2*y^(k-2)*(4*frames.x+frames.x^2) else er
  nativeUp er

def nativeHeatPass (old : NativeOldRow) (frames : NativeHeatFrameInputs) (coef fixed : List ℚ) (base y : ℚ) : ℚ :=
  let forcing := (List.range 20).map fun j => nativeHeatForcingAt old frames fixed y (j+1)
  let mp := nativeUp (base+((List.range 20).map fun j => coef.getD (j+1) 0*forcing.getD j 0/(20-j : ℕ)).sum)
  min y (nativeRootUp mp 20)

def nativeHeatPasses (old : NativeOldRow) (frames : NativeHeatFrameInputs) (coef fixed : List ℚ) (base : ℚ) : ℕ → ℚ → ℚ
  | 0, y => y
  | n+1, y => nativeHeatPasses old frames coef fixed base n (nativeHeatPass old frames coef fixed base y)

end ASDExplicitGamma.Numerics.Native
