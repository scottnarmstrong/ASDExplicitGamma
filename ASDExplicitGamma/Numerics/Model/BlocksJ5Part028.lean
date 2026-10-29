module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B28 : ModeBlockData :=
  ⟨⟨28, 29, (25122254158564044277/10000000000000000000000 : ℚ), (19708658287714449/5000000000000000000000 : ℚ)⟩, [
    (28, modeDataJ5M29)], (6280563539641011069/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b28 : entryChecks 5 bflatBlockJ5B28.entries = true := by
  simp only [entryChecks,bflatBlockJ5B28,List.all_cons,List.all_nil,
    mode_checked_j5_m29,Bool.and_self]
theorem block_mass_checked_j5_b28 : blockMassCheck bflatBlockJ5B28 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
