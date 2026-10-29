module

public import ASDExplicitGamma.Numerics.CeilDiv
public import ASDExplicitGamma.Numerics.Spike.MainCertTypes

/-! Fixed-grid upper composition for the generated affine maps. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Spike

def ceilGridProduct (a b : ℕ) : ℕ := ceilDiv (a * b) gridScale

def advancePanel (value : ℕ) (panel : PanelCert) : ℕ :=
  ceilGridProduct value panel.rhoUpper + panel.offsetUpper

def advanceInsertion (value : ℕ) (insertion : InsertionCert) : ℕ :=
  ceilGridProduct (insertion.panels.foldl advancePanel value) insertion.frameUpper

def composeUpper (insertions : List InsertionCert) : ℕ :=
  insertions.foldl advanceInsertion cold40Upper

end ASDExplicitGamma.Numerics.Spike
