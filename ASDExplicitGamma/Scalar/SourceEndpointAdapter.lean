module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! Small Part B adapter for the endpoint-proportional rows supplied by the
Part C smaller-gamma source theorem. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

/-- Displayed endpoint caps for the six completed source means. -/
noncomputable def sourceMeanEndpointCaps (r : Fin 6) : ℝ :=
  match r.val with
  | 0 => 3/50
  | 1 => 8503/125000
  | 2 => 73809/1000000
  | 3 => 78965/1000000
  | 4 => 83927/1000000
  | _ => 44411/500000

/-- Displayed endpoint caps for the six weak inverse source rows. -/
noncomputable def weakSourceEndpointCaps (r : Fin 6) : ℝ :=
  match r.val with
  | 0 => 50817/500000
  | 1 => 22237/200000
  | 2 => 11907/100000
  | 3 => 126483/1000000
  | 4 => 133757/1000000
  | _ => 141001/1000000

/-- The unpatched depth-14 endpoint cap used by the upper source bounds. -/
noncomputable def safeDepth14EndpointCap : ℝ :=
  13276004954337698463246677797499 / (10 : ℝ)^32

end ASDExplicitGamma.Scalar
