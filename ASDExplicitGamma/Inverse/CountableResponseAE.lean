module

public import Algsuperdiff.Section3.Provider.Whitney.SubadditivityCountable

/-! Countable hybrid response comparison for Sobolev representatives whose
constant values on cells hold almost everywhere. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider
noncomputable section

/-- The countable variational response comparison is insensitive to null
sets in the piecewise constant competitor. It therefore applies to the one
common weak-gradient field from the actual planar construction. -/
theorem countable_response_le_of_ae_constant {ι : Type} [Countable ι]
    {Q : Book.Ch02.Domain 2} {S : ι → Book.Ch02.Domain 2}
    (a : Book.Ch02.CoeffOn Q) (aS : ∀ i, Book.Ch02.CoeffOn (S i))
    (haS : ∀ i, (aS i).toCoeffField=a.toCoeffField)
    (hsub : ∀ i, (S i:Set (Vec 2)) ⊆ Q)
    (hdisj : Pairwise fun i j => Disjoint (S i:Set (Vec 2)) (S j:Set (Vec 2)))
    (hcover : volume ((Q:Set (Vec 2)) \ ⋃ i, (S i:Set (Vec 2)))=0)
    (p q : Vec 2) (F G : Vec 2 → Vec 2) (Fc Gc : ι → Vec 2)
    (hF : Book.Ch01.PotentialZeroTraceFieldOn (Q:Set (Vec 2)) (fun x => F x-p))
    (hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (Q:Set (Vec 2)) (fun x => G x-q))
    (hFc : ∀ i, ∀ᵐ x ∂volumeMeasureOn (Q:Set (Vec 2)), x ∈ (S i:Set (Vec 2)) → F x=Fc i)
    (hGc : ∀ i, ∀ᵐ x ∂volumeMeasureOn (Q:Set (Vec 2)), x ∈ (S i:Set (Vec 2)) → G x=Gc i) :
    ENNReal.ofReal (blockVecDot (p,q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix Q a) (p,q))) ≤
      ∑' i, ENNReal.ofReal (((volume (S i:Set (Vec 2))).toReal/(volume (Q:Set (Vec 2))).toReal)*
        blockVecDot (Fc i,Gc i) (blockMatVecMul (Book.Ch02.coarseBlockMatrix (S i) (aS i)) (Fc i,Gc i))) := by
  classical
  let T := fun (C : ι → Vec 2) (W : Vec 2 → Vec 2) (x : Vec 2) =>
    if hi : ∃ i, x ∈ (S i:Set (Vec 2)) then C hi.choose else W x
  have hTc (C : ι → Vec 2) (W : Vec 2 → Vec 2) (i : ι) (x : Vec 2)
      (hx : x ∈ (S i:Set (Vec 2))) : T C W x=C i := by
    have hi : ∃ j, x ∈ (S j:Set (Vec 2)) := ⟨i,hx⟩
    dsimp only [T]
    rw [dite_eq_left hi]
    have he : hi.choose=i := by
      by_contra hn
      exact Set.disjoint_left.mp (hdisj hn) hi.choose_spec hx
    rw [he]
  have hTa (C : ι → Vec 2) (W : Vec 2 → Vec 2)
      (hWC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (Q:Set (Vec 2)), x ∈ (S i:Set (Vec 2)) → W x=C i) :
      T C W =ᵐ[volumeMeasureOn (Q:Set (Vec 2))] W := by
    filter_upwards [ae_all_iff.mpr hWC] with x hx
    by_cases hi : ∃ i, x ∈ (S i:Set (Vec 2))
    · exact (hTc C W hi.choose x hi.choose_spec).trans (hx hi.choose hi.choose_spec).symm
    · simp only [T,dite_eq_right hi]
  have hFe : (fun x => T Fc F x-p) =ᵐ[volumeMeasureOn (Q:Set (Vec 2))] (fun x => F x-p) := by
    filter_upwards [hTa Fc F hFc] with x hx
    rw [hx]
  have hGe : (fun x => T Gc G x-q) =ᵐ[volumeMeasureOn (Q:Set (Vec 2))] (fun x => G x-q) := by
    filter_upwards [hTa Gc G hGc] with x hx
    rw [hx]
  have hF' : Book.Ch01.PotentialZeroTraceFieldOn (Q:Set (Vec 2)) (fun x => T Fc F x-p) := by
    refine ⟨(memLp_congr_ae hFe).mpr hF.1,?_⟩
    obtain ⟨u,hu⟩ := hF.2
    exact ⟨u,hFe.trans hu⟩
  have hG' : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (Q:Set (Vec 2)) (fun x => T Gc G x-q) := by
    refine ⟨(memLp_congr_ae hGe).mpr hG.1,?_⟩
    intro φ
    calc
      (∫ x in (Q:Set (Vec 2)), vecDot (T Gc G x-q) (φ.grad x))=
          ∫ x in (Q:Set (Vec 2)), vecDot (G x-q) (φ.grad x) := by
        apply integral_congr_ae
        filter_upwards [hGe] with x hx
        rw [hx]
      _ = 0 := hG.2 φ
  exact Whitney.ofReal_bfA_quadratic_le_simplex_weighted_tsum a aS haS hsub hdisj hcover
    p q (T Fc F) (T Gc G) Fc Gc hF' hG' (hTc Fc F) (hTc Gc G)

end
end ASDExplicitGamma.Inverse
