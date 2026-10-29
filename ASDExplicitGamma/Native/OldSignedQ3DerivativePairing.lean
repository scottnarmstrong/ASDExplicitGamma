module

public import ASDExplicitGamma.Native.OldSignedDerivativePairing
public import ASDExplicitGamma.Native.OldSignedDerivativeFeedback
public import ASDExplicitGamma.Main.Q3W2Jets
public import ASDExplicitGamma.Triadic.PlanarDirectionVolume

/-! The zero-boundary derivative identity for the actual physical q3 modes,
with the literal column-divergence convention of the OLD row estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- Literal column divergence of the physical q3 skew direction. -/
def oldSignedQ3ColumnDivergence (b : ℝ) (L : {l : ℝ // 0<l}) (v : WhiteNoise)
    (x : Vec 2) (k : Fin 2) : ℝ :=
  ∑ j : Fin 2,responsePlanarJ j k*q3Convolution b L (mainQ3JetIndex (.first j)) v x

/-- The actual weak multiplier's column divergence is the same literal
q3 first-jet row used in AN (3.2). -/
theorem old_signed_q3_column_divergence (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : WhiteNoise) :
    lemmaVPlanarWeakColumnDivergence (mainQ3DirectionW2 Q b L v).value=
      oldSignedQ3ColumnDivergence b L v := by
  funext x k
  have hg (j : Fin 2) : (mainQ3DirectionW2 Q b L v).value.grad x j=
      q3Convolution b L (mainQ3JetIndex (.first j)) v x :=
    mainQ3DirectionW2_jet Q b L v (.first j) x
  fin_cases k <;> simp [lemmaVPlanarWeakColumnDivergence,oldSignedQ3ColumnDivergence,
    matVecMul,responsePlanarJ,Fin.sum_univ_two,hg]

/-- AN (3.4) for an actual q3 coefficient mode; no multiplier regularity
or derivative formula is left as an assumed premise. -/
theorem old_signed_q3_zero_trace_pairing (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : WhiteNoise)
    (phi : H10Function (openCubeSet Q)) (g : H1Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero v x • matVecMul responsePlanarJ (phi.toH1Function.grad x))
      (g.grad x))=
      volumeAverage (openCubeSet Q) (fun x => vecDot
        (phi.toH1Function x • oldSignedQ3ColumnDivergence b L v x) (g.grad x)) := by
  have h := old_signed_zero_trace_derivative_pairing Q (mainQ3DirectionW2 Q b L v).value phi g
    (mainQ3DirectionW2 Q b L v).value_memLp_top
    (mainQ3DirectionW2 Q b L v).gradient_memLp_top_volume
  rw [old_signed_q3_column_divergence] at h
  exact h

end
end ASDExplicitGamma.Native
