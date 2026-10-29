module

public import ASDExplicitGamma.Main.ErrorSupport

/-! Literal scalar coefficients of the main-return code. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

/-- Common column/row coefficient after the prescribed Gaussian conversion. -/
def mainKd (v : ℝ) : ℝ :=
  (637/1000)*Real.sqrt ((156/5)*mainA2 v)+
    (440/1000)*(304/1000)*Real.sqrt ((46488/25)*mainA4 v)

def mainKrem (v : ℝ) : ℝ :=
  (2018/1000)*Real.sqrt ((156/5)*mainA2 v)+(285/1000)*Real.sqrt ((46488/25)*mainA4 v)

def mainOp (v : ℝ) : ℝ := (1+Real.sqrt 2)*(440/1000)*Real.sqrt ((156/5)*mainA2 v)
def mainOm (v : ℝ) : ℝ := (440/1000)*Real.sqrt ((156/5)*mainA2 v)

/-- The parent-gap coefficient uses the actual observer covariance-cap input. -/
def mainBe (v q : ℝ) : ℝ :=
  v*(Real.sqrt (q/2)+(304/1000)*Real.sqrt (156/5)*(3:ℝ)^(-6:ℤ)*(Real.sqrt (q/2)+2))

def mainEcov (v q : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt (v*(v*q)/2)+(319/1000)*Real.sqrt ((156/5)*mainA2 v)*mainOp v)^2+
    (Real.sqrt (v*(v*q)/2)+(319/1000)*Real.sqrt ((156/5)*mainA2 v)*mainOm v)^2)

/-- The complete source linear/oscillation term, independent of f. -/
def mainLinearError (v H xi q : ℝ) : ℝ :=
  Real.sqrt 2*mainT0 xi*Real.sqrt (v+v*q/2)*mainOp v+
    2*Real.sqrt 2*mainTm H*Real.sqrt v*mainOm v+
    mainBeta*(mainOp v)^2+mainM0 H*(mainOm v)^2+
    2*mainKd v*(mainT0 xi*Real.sqrt v+Real.sqrt 2*mainC H*mainOm v)

/-- The four-load aggregate retains G=sqrt(2 xi), rather than the two-load gap. -/
def mainFourLoadAG (v H xi q : ℝ) : ℝ :=
  2*mainBe v q+2*mainKd v*(mainT0 xi*(Real.sqrt (v+v*q/2)+Real.sqrt v)/Real.sqrt 2+
    (63/50)*mainBeta*mainOp v+mainC H*mainOm v)

/-- The actual scalar source error, with every coefficient instantiated by
its literal source formula; this definition contains no analytic estimate. -/
def mainSourceError (v a f H xi q : ℝ) : ℝ :=
  mainError v a f H xi (mainLinearError v H xi q) (mainEcov v q) (mainFourLoadAG v H xi q)
    (mainBe v q) (mainKd v) (mainKrem v) (mainOp v) (mainOm v)

theorem mainKd_nonneg (v : ℝ) : 0 ≤ mainKd v := by unfold mainKd; positivity
theorem mainKrem_nonneg (v : ℝ) : 0 ≤ mainKrem v := by unfold mainKrem; positivity
theorem mainEcov_nonneg (v q : ℝ) : 0 ≤ mainEcov v q := Real.sqrt_nonneg _
theorem mainBe_nonneg {v : ℝ} (hv : 0 ≤ v) (q : ℝ) : 0 ≤ mainBe v q := by unfold mainBe; positivity

end
end ASDExplicitGamma.Main
