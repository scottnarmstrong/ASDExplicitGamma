module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B31 : ModeBlockData :=
  ⟨⟨31, 32, (12550465597644975759/5000000000000000000000 : ℚ), (9849012855206681/2500000000000000000000 : ℚ)⟩, [
    (31, modeDataJ5M32)], (25100931195289951517/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b31 : entryChecks 5 bflatBlockJ5B31.entries = true := by
  simp only [entryChecks,bflatBlockJ5B31,List.all_cons,List.all_nil,
    mode_checked_j5_m32,Bool.and_self]
theorem block_mass_checked_j5_b31 : blockMassCheck bflatBlockJ5B31 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
