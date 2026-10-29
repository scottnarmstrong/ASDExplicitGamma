module

public import ASDExplicitGamma.Model.BflatModeTail
public import ASDExplicitGamma.Numerics.Model.BflatCaps
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.BlockListJ3
public import ASDExplicitGamma.Numerics.Model.BlockListJ4
public import ASDExplicitGamma.Numerics.Model.BlockListJ5

/-! # Exact source rationals for the finite q3 harmonic-defect caps -/

@[expose] public section

namespace ASDExplicitGamma.Model

open ASDExplicitGamma.Numerics.Model

def bflatSingletonModeBlock (e : ℕ × ModeData) : ModeBlockData :=
  { bound := ⟨e.1, e.1 + 1, e.2.enclosure.sine.hi,
      e.2.enclosure.difference.hi⟩,
    entries := [e]
    sineLower := e.2.enclosure.sine.lo }

def bflatSingletonModeBlocks (bs : List ModeBlockData) : List ModeBlockData :=
  bs.flatMap (fun b => b.entries.map bflatSingletonModeBlock)

def bflatExactSingletonBlocksJ3 : List ModeBlockData :=
  bflatSingletonModeBlocks bflatBlocksJ3

def bflatExactChargeRowsJ3 : List ℚ :=
  bflatExactSingletonBlocksJ3.map
    (fun a => blockChargeRow a bflatExactSingletonBlocksJ3)

theorem bflatExactChargeRowsJ3_length : bflatExactChargeRowsJ3.length = 256 := by
  decide +kernel

theorem bflatExactLowerSumJ3 :
    blockLowerSum bflatExactSingletonBlocksJ3 =
      (1996796649127349043391 / 2000000000000000000000 : ℚ) := by
  decide +kernel

def bflatExactSingletonBlocksJ4 : List ModeBlockData :=
  bflatSingletonModeBlocks bflatBlocksJ4

def bflatExactChargeRowsJ4 : List ℚ :=
  bflatExactSingletonBlocksJ4.map
    (fun a => blockChargeRow a bflatExactSingletonBlocksJ4)

theorem bflatExactChargeRowsJ4_length : bflatExactChargeRowsJ4.length = 512 := by
  decide +kernel

theorem bflatExactLowerSumJ4 :
    blockLowerSum bflatExactSingletonBlocksJ4 =
      (9991631911802854962809 / 10000000000000000000000 : ℚ) := by
  decide +kernel

def bflatExactSingletonBlocksJ5 : List ModeBlockData :=
  bflatSingletonModeBlocks bflatBlocksJ5

theorem bflatSingletonModeBlock_modes (e : ℕ × ModeData) :
    blockModes (bflatSingletonModeBlock e).bound = [e.1] := by
  simp [bflatSingletonModeBlock, blockModes]

theorem mode_sine_interval_lower_nonneg (j n : ℕ) (d : ModeData)
    (h : modeDataCheck j n d = true) : 0 ≤ d.enclosure.sine.lo := by
  unfold modeDataCheck at h
  split_ifs at h with htrig
  · cases he : modeCovarianceIntervals j n d.smallSine d.smallCosine with
    | none => simp [he] at h
    | some I =>
      rw [he] at h
      obtain ⟨_, _, _, _, hsine, _⟩ := of_decide_eq_true h
      exact_mod_cast hsine

theorem bflatSingletonModeBlock_mass_checked (j : ℕ) (e : ℕ × ModeData)
    (he : modeDataCheck j e.1 e.2 = true) :
    blockMassCheck (bflatSingletonModeBlock e) = true := by
  have hlo := mode_sine_interval_lower_nonneg j e.1 e.2 he
  apply of_decide_eq_true
  simp [blockMassCheck, bflatSingletonModeBlock, blockModes, entrySum, hlo]

theorem bflatSingleton_entries_flatten (es : List (ℕ × ModeData)) :
    ((es.map bflatSingletonModeBlock).map ModeBlockData.bound).flatMap blockModes =
      es.map Prod.fst := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [bflatSingletonModeBlock_modes, ih]
    rfl

theorem bflatSingleton_blocks_flatten (bs : List ModeBlockData) :
    ((bflatSingletonModeBlocks bs).map ModeBlockData.bound).flatMap blockModes =
      bs.flatMap (fun b => b.entries.map Prod.fst) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [bflatSingletonModeBlocks]
    simp only [List.flatMap_cons, List.map_append, List.flatMap_append]
    have ih' : List.flatMap blockModes
        (List.map ModeBlockData.bound
          (List.flatMap (fun b => b.entries.map bflatSingletonModeBlock) bs)) =
        bs.flatMap (fun b => b.entries.map Prod.fst) := by
      simpa [bflatSingletonModeBlocks] using ih
    rw [bflatSingleton_entries_flatten, ih']

theorem entries_flatten_eq_blocks (bs : List ModeBlockData)
    (hm : ∀ b ∈ bs, blockMassCheck b = true) :
    bs.flatMap (fun b => b.entries.map Prod.fst) =
      (bs.map ModeBlockData.bound).flatMap blockModes := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.map_cons]
    have hb := of_decide_eq_true (hm b (by simp))
    have ht : ∀ c ∈ bs, blockMassCheck c = true := fun c hc => hm c (by simp [hc])
    rw [hb.1, ih ht]

theorem bflatSingleton_blocks_cover {bs : List ModeBlockData} {N : ℕ}
    (hcover : (bs.map ModeBlockData.bound).flatMap blockModes = List.range N)
    (hm : ∀ b ∈ bs, blockMassCheck b = true) :
    ((bflatSingletonModeBlocks bs).map ModeBlockData.bound).flatMap blockModes =
      List.range N := by
  calc
    ((bflatSingletonModeBlocks bs).map ModeBlockData.bound).flatMap blockModes =
        bs.flatMap (fun b => b.entries.map Prod.fst) := by
          exact bflatSingleton_blocks_flatten bs
    _ = (bs.map ModeBlockData.bound).flatMap blockModes := entries_flatten_eq_blocks bs hm
    _ = List.range N := hcover

theorem bflatSingleton_blocks_entries_checked {j : ℕ} {bs : List ModeBlockData}
    (hc : ∀ b ∈ bs, entryChecks j b.entries = true) :
    ∀ b ∈ bflatSingletonModeBlocks bs, entryChecks j b.entries = true := by
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨a, ha, hb⟩
  rcases List.mem_map.mp hb with ⟨e, he, rfl⟩
  have hcheck := List.all_eq_true.mp (hc a ha) e he
  simp [entryChecks, bflatSingletonModeBlock, hcheck]

theorem bflatSingleton_blocks_mass_checked {j : ℕ} {bs : List ModeBlockData}
    (hc : ∀ b ∈ bs, entryChecks j b.entries = true) :
    ∀ b ∈ bflatSingletonModeBlocks bs, blockMassCheck b = true := by
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨a, ha, hb⟩
  rcases List.mem_map.mp hb with ⟨e, he, rfl⟩
  exact bflatSingletonModeBlock_mass_checked j e
    (List.all_eq_true.mp (hc a ha) e he)

end ASDExplicitGamma.Model
