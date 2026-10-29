module

public import ASDExplicitGamma.Native.OldSignedDirichletProjection
public import ASDExplicitGamma.Cold.SquareStreamFunction

/-! Actual finite-square Dirichlet, gradient and zero-normal solenoidal
fields. The planar stream theorem identifies the complementary field as a
genuine H1 gradient; no Hodge decomposition is assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Response
open ASDExplicitGamma.Variational ASDExplicitGamma.Cold
noncomputable section

/-- Changing an H1 gradient representative on a null set preserves its
literal potential witness. -/
theorem old_signed_isPotentialOn_congr_ae {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → Vec d} (hF : IsPotentialOn U F) (hFG : F =ᵐ[volumeMeasureOn U] G) :
    IsPotentialOn U G := by
  obtain ⟨u,hu⟩ := hF
  have ha : u.grad =ᵐ[volumeMeasureOn U] G := by simpa only [hu] using hFG
  refine ⟨{ toFun := u.toFun
            grad := G
            memL2 := u.memL2
            gradMemL2 := ?_
            hasWeakGradient := ?_ },rfl⟩
  · intro i
    exact (u.gradMemL2 i).ae_eq (ha.mono fun x hx => congrFun hx i)
  · intro i φ hφ hc hs
    have hw := u.hasWeakGradient i φ hφ hc hs
    have he : (∫ x in U,u.grad x i*φ x ∂volume)=(∫ x in U,G x i*φ x ∂volume) := by
      apply integral_congr_ae
      filter_upwards [ha] with x hx
      rw [hx]
    exact hw.trans (congrArg Neg.neg he)

/-- A quarter turn of an actual divergence-free square field is an H1
gradient. The witness is supplied by the proved square stream theorem. -/
theorem old_signed_rotated_solenoidal_potential (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hdiv : IsSolenoidalOn (openCubeSet Q) F) :
    IsPotentialOn (openCubeSet Q) (fun x => matVecMul responsePlanarJ (F x)) := by
  obtain ⟨u,_,hu⟩ := square_stream_function Q hF hdiv
  apply old_signed_isPotentialOn_congr_ae (-u).isPotentialOn
  filter_upwards [hu] with x hx
  rw [hx]
  ext i
  fin_cases i <;> simp [H1Function.neg_grad,squareQuarterTurn,matVecMul,responsePlanarJ,Fin.sum_univ_two]

end
end ASDExplicitGamma.Native
