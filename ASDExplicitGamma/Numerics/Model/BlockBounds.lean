module

public import ASDExplicitGamma.Numerics.Model.ProjectionIdentity
public import ASDExplicitGamma.Numerics.Model.ModeIntervals

/-! Positive block majorants for the finite q3 projection. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Model

structure ModeBlock where
  start : ℕ
  stop : ℕ
  sineUpper : ℚ
  differenceUpper : ℚ

def blockModes (b : ModeBlock) : List ℕ := List.range' b.start (b.stop-b.start)
def blockWeight (a b : ModeBlock) : ℚ :=
  (a.stop : ℚ)^2/((a.stop : ℚ)^2+((b.start+1 : ℕ) : ℚ)^2)

theorem block_mode_limits (b : ModeBlock) (n : ℕ) (hn : n ∈ blockModes b) :
    b.start ≤ n ∧ n+1 ≤ b.stop := by
  have h := List.mem_range'.mp hn
  omega

theorem mode_weight_block_bound (a b : ModeBlock) (m n : ℕ)
    (hm : m ∈ blockModes a) (hn : n ∈ blockModes b) :
    modeWeight m n ≤ (blockWeight a b : ℝ) := by
  obtain ⟨_,hm⟩ := block_mode_limits a m hm
  obtain ⟨hn,_⟩ := block_mode_limits b n hn
  have hmR : ((m+1 : ℕ) : ℝ) ≤ (a.stop : ℝ) := by exact_mod_cast hm
  have hnR : ((b.start+1 : ℕ) : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hn 1
  have hm2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((m+1 : ℕ):ℝ)) hmR 2
  have hn2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((b.start+1 : ℕ):ℝ)) hnR 2
  have hprod := mul_le_mul hm2 hn2 (sq_nonneg (((b.start+1 : ℕ):ℝ))) (sq_nonneg (a.stop:ℝ))
  have hden : (0:ℝ) < ((m+1 : ℕ):ℝ)^2+((n+1 : ℕ):ℝ)^2 := by positivity
  have hden' : (0:ℝ) < (a.stop:ℝ)^2+((b.start+1 : ℕ):ℝ)^2 := by positivity
  simp only [modeWeight,blockWeight,Rat.cast_div,Rat.cast_add,Rat.cast_pow,Rat.cast_natCast]
  apply (div_le_div_iff₀ hden hden').mpr
  nlinarith only [hprod]

noncomputable def blockCorrection (bs : List ModeBlock) : ℝ :=
  listSum bs (fun a => listSum bs (fun b =>
    (blockWeight a b : ℝ)*(a.differenceUpper : ℝ)*(b.sineUpper : ℝ)))

theorem block_pair_bound (j : ℕ) (a b : ModeBlock)
    (hd : ∀ m ∈ blockModes a, 0 ≤ q3ModeDifference j m)
    (hs : ∀ n ∈ blockModes b, 0 ≤ q3ModeSine j n)
    (hD : listSum (blockModes a) (q3ModeDifference j) ≤ (a.differenceUpper : ℝ))
    (hS : listSum (blockModes b) (q3ModeSine j) ≤ (b.sineUpper : ℝ)) :
    listSum (blockModes a) (fun m => listSum (blockModes b)
      (fun n => modeWeight m n*q3ModeDifference j m*q3ModeSine j n)) ≤
      (blockWeight a b : ℝ)*(a.differenceUpper : ℝ)*(b.sineUpper : ℝ) := by
  have hw : (0:ℝ) ≤ (blockWeight a b : ℝ) := by
    unfold blockWeight
    push_cast
    positivity
  calc
    _ ≤ listSum (blockModes a) (fun m => listSum (blockModes b)
        (fun n => (blockWeight a b : ℝ)*q3ModeDifference j m*q3ModeSine j n)) := by
      apply list_sum_le
      intro m hm
      apply list_sum_le
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mode_weight_block_bound a b m n hm hn) (hd m hm)) (hs n hn)
    _ = (blockWeight a b : ℝ)*listSum (blockModes a) (q3ModeDifference j)*
        listSum (blockModes b) (q3ModeSine j) := by
      simp only [list_sum_mul_left,list_sum_mul_right]
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hD hw) hS
      (list_sum_nonneg _ _ hs) (mul_nonneg hw ((list_sum_nonneg _ _ hd).trans hD))

/-- Only one-dimensional covariance enclosures and positive block masses are needed. -/
theorem projection_block_bound (j N : ℕ) (bs : List ModeBlock) (L : ℝ)
    (hcover : bs.flatMap blockModes = List.range N)
    (hmode : ∀ n < N, 0 ≤ q3ModeDifference j n ∧ 0 ≤ q3ModeSine j n)
    (hD : ∀ b ∈ bs, listSum (blockModes b) (q3ModeDifference j) ≤ (b.differenceUpper : ℝ))
    (hS : ∀ b ∈ bs, listSum (blockModes b) (q3ModeSine j) ≤ (b.sineUpper : ℝ))
    (hL0 : 0 ≤ L) (hL : L ≤ listSum (List.range N) (q3ModeSine j)) :
    2-2*q3Projection j N ≤ 2-2*L^2+4*blockCorrection bs := by
  have hmem (b : ModeBlock) (hb : b ∈ bs) (n : ℕ) (hn : n ∈ blockModes b) : n < N := by
    apply List.mem_range.mp
    rw [← hcover]
    exact List.mem_flatMap.mpr ⟨b,hb,hn⟩
  have hW : listSum (List.range N) (fun m => listSum (List.range N)
      (fun n => modeWeight m n*q3ModeDifference j m*q3ModeSine j n)) ≤ blockCorrection bs := by
    rw [← hcover,list_sum_flatMap]
    unfold blockCorrection
    apply list_sum_le
    intro a ha
    calc
      _ = listSum bs (fun b => listSum (blockModes a) (fun m => listSum (blockModes b)
          (fun n => modeWeight m n*q3ModeDifference j m*q3ModeSine j n))) := by
        simp only [list_sum_flatMap]
        exact list_sum_comm _ _ _
      _ ≤ _ := list_sum_le _ _ _ (fun b hb => block_pair_bound j a b
        (fun m hm => (hmode m (hmem a ha m hm)).1)
        (fun n hn => (hmode n (hmem b hb n hn)).2) (hD a ha) (hS b hb))
  have hsquare := pow_le_pow_left₀ hL0 hL 2
  rw [projection_difference_identity]
  nlinarith only [hsquare,hW]

end ASDExplicitGamma.Numerics.Model
