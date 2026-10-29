module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-! Exact scalar endpoint comparison for the boundary-fixed Part C q1 input. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

noncomputable def q1BoundaryEndpointCap : ℝ :=
  1095712671923674591833653217481626040963161 /
    (15625 * (10 : ℝ)^39)

noncomputable def q1SourceTargetCap : ℝ :=
  109585425260485981721911610633 /
    1562500000000000000000000000000

theorem q1BoundaryEndpoint_below_sourceTarget :
    q1BoundaryEndpointCap < q1SourceTargetCap := by
  norm_num [q1BoundaryEndpointCap, q1SourceTargetCap]

end ASDExplicitGamma.Scalar
