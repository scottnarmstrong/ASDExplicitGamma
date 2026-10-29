module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B24 : ModeBlockData :=
  ⟨⟨24, 25, (12573721721698400317/5000000000000000000000 : ℚ), (19721216293947137/5000000000000000000000 : ℚ)⟩, [
    (24, modeDataJ5M25)], (25147443443396800633/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b24 : entryChecks 5 bflatBlockJ5B24.entries = true := by
  simp only [entryChecks,bflatBlockJ5B24,List.all_cons,List.all_nil,
    mode_checked_j5_m25,Bool.and_self]
theorem block_mass_checked_j5_b24 : blockMassCheck bflatBlockJ5B24 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
