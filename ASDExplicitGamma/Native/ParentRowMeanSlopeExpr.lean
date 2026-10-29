module

public import ASDExplicitGamma.Native.ParentRowWeightedClocks

/-! Exact symbolic mean-slope program shared by the sixteen parent setups. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The fourth-order mesh-five shell weight. -/
def parentRowA4Weight (k : ℕ) : ℚ := (1/9)^(2*(k+6))

/-- The exact affine full-response base at mesh depth five. -/
def parentRowRawBase (height : ℕ) : ℚ :=
  1009309/500000+(17/50000)*(32474*((height:ℚ)+6)+11483216)

/-- The exact source expression for the unrounded parent mean slope. -/
def parentRowMeanSlopeExpr (height : ℕ) : Expr :=
  let v := parentRowVarianceExpr height
  let a2 := parentRowWeightedExpr parentRowA2Weight height
  let a4 := parentRowWeightedExpr parentRowA4Weight height
  let a := .add (.add (.add (.const 0) (.sqrt (.mul a2 (.const (39/5)))))
    (.mul (.sqrt (.mul a2 (.const (156/5)))) (.const (36/25))))
    (.mul (.sqrt (.mul a4 (.const (46488/25)))) (.const (57/200)))
  let f := .mul (.exp (.mul (.var 2) (.const ((17/50000)*(2*(height:ℚ)+24))))) (.const 4)
  let j := .add (.mul (.mul f (.const (176338357/78125000))) (.const (parentRowRawBase height)))
    (.mul (.mul (.mul v (.const 52)) (.sqrt (.const 3))) (.const (49958012987/15625000000)))
  let kj := .add (.mul (.mul f (.const (47879/31250))) (.const (parentRowRawBase height)))
    (.mul (.mul (.mul (.mul v (.const 52)) (.sqrt (.const 3))) (.const (3683/2500))) (.const (3683/2500)))
  let k := .mul (.mul a2 (.const (78/5)))
    (.add (.add (.divPos (.const (36/25)) (.sqrt (.const 2))) (.const (1/4)))
      (.mul (.sqrt (.const 2)) (.const (57/200))))
  .add (.add (.mul (.mul (.mul (.mul (.const 1) a) a) (.const (232/125))) j)
    (.mul (.mul k (.const 2)) kj))
    (.mul (.mul v (.const 2)) (.add (.mul (.sqrt (.const 3)) (.const (3/10^46))) (.const (3683/2500))))

end
end ASDExplicitGamma.Native
