module

public import ASDExplicitGamma.Response.Analytic

/-! The actual doubled variational response as an inverse quadratic form of
the Lax--Milgram operator compressed to its correction space. -/
@[expose] public section

open Homogenization
open ASDExplicitGamma.Response
open scoped InnerProduct InnerProductSpace

namespace ASDExplicitGamma.Scalar

noncomputable section

/-- The Lax--Milgram operator obtained by compressing the actual coefficient
energy to the closed correction space. -/
noncomputable def compressed_variational_operator {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : MuHilbertRealization U a) :
    M.correctionSpace.correctionSpace.toSubmodule ≃L[ℝ]
      M.correctionSpace.correctionSpace.toSubmodule := by
  exact (isCoercive_restrictBilin M.correctionSpace.correctionSpace M.energyCoercive).continuousLinearEquivOfBilin

end

end ASDExplicitGamma.Scalar
