module
public import ASDExplicitGamma.Numerics.Model.BlockBounds

/-! The finite data interface for the q3 block certificate. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Model

structure ModeBlockData where
  bound : ModeBlock
  entries : List (ℕ × ModeData)
  sineLower : ℚ

def entryChecks (j : ℕ) (es : List (ℕ × ModeData)) : Bool :=
  es.all (fun e => modeDataCheck j e.1 e.2)

def entrySum (es : List (ℕ × ModeData)) (f : ModeEnclosure → ℚ) : ℚ :=
  (es.map (fun e => f e.2.enclosure)).sum

def blockMassCheck (b : ModeBlockData) : Bool := decide
  (b.entries.map Prod.fst = blockModes b.bound ∧ 0 ≤ b.sineLower ∧
    b.sineLower ≤ entrySum b.entries (fun I => I.sine.lo) ∧
    entrySum b.entries (fun I => I.sine.hi) ≤ b.bound.sineUpper ∧
    entrySum b.entries (fun I => I.difference.hi) ≤ b.bound.differenceUpper)

theorem cast_rational_list_sum {α : Type*} (xs : List α) (f : α → ℚ) :
    ((xs.map f).sum : ℝ) = listSum xs (fun x => (f x : ℝ)) := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,Rat.cast_zero,list_sum_nil]
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,Rat.cast_add,list_sum_cons,ih]

theorem list_sum_map {α β : Type*} (xs : List α) (g : α → β) (f : β → ℝ) :
    listSum (xs.map g) f = listSum xs (fun x => f (g x)) := by
  simp only [listSum,List.map_map,Function.comp_def]

theorem block_data_sound (j : ℕ) (b : ModeBlockData)
    (hc : entryChecks j b.entries = true) (hm : blockMassCheck b = true) :
    (∀ n ∈ blockModes b.bound, 0 ≤ q3ModeDifference j n ∧ 0 ≤ q3ModeSine j n) ∧
    (b.sineLower : ℝ) ≤ listSum (blockModes b.bound) (q3ModeSine j) ∧
    listSum (blockModes b.bound) (q3ModeSine j) ≤ (b.bound.sineUpper : ℝ) ∧
    listSum (blockModes b.bound) (q3ModeDifference j) ≤ (b.bound.differenceUpper : ℝ) ∧
    0 ≤ (b.sineLower : ℝ) := by
  obtain ⟨hmap,hlo,hl,hS,hD⟩ := of_decide_eq_true hm
  have hs (e : ℕ × ModeData) (he : e ∈ b.entries) :=
    mode_data_sound j e.1 e.2 (List.all_eq_true.mp hc e he)
  have heS : listSum (blockModes b.bound) (q3ModeSine j) =
      listSum b.entries (fun e => q3ModeSine j e.1) := by rw [← hmap,list_sum_map]
  have heD : listSum (blockModes b.bound) (q3ModeDifference j) =
      listSum b.entries (fun e => q3ModeDifference j e.1) := by rw [← hmap,list_sum_map]
  refine ⟨?_,?_,?_,?_,by exact_mod_cast hlo⟩
  · intro n hn
    rw [← hmap] at hn
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    exact ⟨(hs e he).2.2.2.2.2,(hs e he).2.2.2.2.1⟩
  · rw [heS]
    have hcast : (b.sineLower : ℝ) ≤ (entrySum b.entries (fun I => I.sine.lo) : ℝ) := by exact_mod_cast hl
    apply hcast.trans
    rw [entrySum,cast_rational_list_sum]
    exact list_sum_le _ _ _ (fun e he => (hs e he).2.1.1)
  · rw [heS]
    have hcast : (entrySum b.entries (fun I => I.sine.hi) : ℝ) ≤ (b.bound.sineUpper : ℝ) := by exact_mod_cast hS
    apply le_trans _ hcast
    rw [entrySum,cast_rational_list_sum]
    exact list_sum_le _ _ _ (fun e he => (hs e he).2.1.2)
  · rw [heD]
    have hcast : (entrySum b.entries (fun I => I.difference.hi) : ℝ) ≤ (b.bound.differenceUpper : ℝ) := by exact_mod_cast hD
    apply le_trans _ hcast
    rw [entrySum,cast_rational_list_sum]
    exact list_sum_le _ _ _ (fun e he => (hs e he).2.2.1.2)

def blockLowerSum (bs : List ModeBlockData) : ℚ := (bs.map ModeBlockData.sineLower).sum

def blockChargeRow (a : ModeBlockData) (bs : List ModeBlockData) : ℚ :=
  (bs.map (fun b => Mirror.roundUp 28 (4*blockWeight a.bound b.bound*
    a.bound.differenceUpper*b.bound.sineUpper))).sum

def blockCharge (bs : List ModeBlockData) : ℚ := (bs.map (fun a => blockChargeRow a bs)).sum

theorem block_charge_sound (bs : List ModeBlockData) :
    4*blockCorrection (bs.map ModeBlockData.bound) ≤ (blockCharge bs : ℝ) := by
  simp only [blockCorrection,list_sum_map,blockCharge,cast_rational_list_sum]
  rw [← list_sum_mul_left]
  apply list_sum_le
  intro a _
  rw [← list_sum_mul_left]
  simp only [blockChargeRow,cast_rational_list_sum]
  apply list_sum_le
  intro b _
  have h : ((4*blockWeight a.bound b.bound*a.bound.differenceUpper*b.bound.sineUpper : ℚ) : ℝ) ≤
      (Mirror.roundUp 28 (4*blockWeight a.bound b.bound*a.bound.differenceUpper*b.bound.sineUpper) : ℝ) := by
    exact_mod_cast Mirror.le_roundUp 28 (4*blockWeight a.bound b.bound*a.bound.differenceUpper*b.bound.sineUpper)
  simpa only [Rat.cast_mul,Rat.cast_ofNat,mul_assoc] using h

/-- Closed data checks yield a cap for the exact covariance-integral projection. -/
theorem block_certificate_sound (j N : ℕ) (bs : List ModeBlockData)
    (hcover : (bs.map ModeBlockData.bound).flatMap blockModes = List.range N)
    (hc : ∀ b ∈ bs, entryChecks j b.entries = true)
    (hm : ∀ b ∈ bs, blockMassCheck b = true) :
    2-2*q3Projection j N ≤ ((2-2*(blockLowerSum bs)^2+blockCharge bs : ℚ) : ℝ) := by
  have hs (b : ModeBlockData) (hb : b ∈ bs) := block_data_sound j b (hc b hb) (hm b hb)
  have hnonneg : ∀ n < N, 0 ≤ q3ModeDifference j n ∧ 0 ≤ q3ModeSine j n := by
    intro n hn
    have hmem : n ∈ (bs.map ModeBlockData.bound).flatMap blockModes := by rw [hcover]; exact List.mem_range.mpr hn
    obtain ⟨a,ha,hn⟩ := List.mem_flatMap.mp hmem
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact (hs b hb).1 n hn
  have hL : (blockLowerSum bs : ℝ) ≤ listSum (List.range N) (q3ModeSine j) := by
    rw [← hcover,list_sum_flatMap,list_sum_map,blockLowerSum,cast_rational_list_sum]
    exact list_sum_le _ _ _ (fun b hb => (hs b hb).2.1)
  have hL0 : (0 : ℝ) ≤ (blockLowerSum bs : ℝ) := by
    rw [blockLowerSum,cast_rational_list_sum]
    exact list_sum_nonneg _ _ (fun b hb => (hs b hb).2.2.2.2)
  have hD : ∀ a ∈ bs.map ModeBlockData.bound,
      listSum (blockModes a) (q3ModeDifference j) ≤ (a.differenceUpper : ℝ) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact (hs b hb).2.2.2.1
  have hS : ∀ a ∈ bs.map ModeBlockData.bound,
      listSum (blockModes a) (q3ModeSine j) ≤ (a.sineUpper : ℝ) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact (hs b hb).2.2.1
  have h := projection_block_bound j N _ _ hcover hnonneg hD hS hL0 hL
  have hcharge := block_charge_sound bs
  push_cast
  linarith only [h,hcharge]

end ASDExplicitGamma.Numerics.Model
