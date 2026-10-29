module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B31 : ModeBlockData :=
  ⟨⟨31, 32, (76977475061819972851/5000000000000000000000 : ℚ), (2513800110889670001/10000000000000000000000 : ℚ)⟩, [
    (31, modeDataJ3M32)], (153954950123639945701/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b31 : entryChecks 3 bflatBlockJ3B31.entries = true := by
  simp only [entryChecks,bflatBlockJ3B31,List.all_cons,List.all_nil,
    mode_checked_j3_m32,Bool.and_self]
theorem block_mass_checked_j3_b31 : blockMassCheck bflatBlockJ3B31 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
