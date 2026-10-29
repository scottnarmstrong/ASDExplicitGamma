module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B49 : ModeBlockData :=
  ⟨⟨49, 50, (68144086916076296957/10000000000000000000000 : ℚ), (16643564967024177/500000000000000000000 : ℚ)⟩, [
    (49, modeDataJ4M50)], (17036021729019074239/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b49 : entryChecks 4 bflatBlockJ4B49.entries = true := by
  simp only [entryChecks,bflatBlockJ4B49,List.all_cons,List.all_nil,
    mode_checked_j4_m50,Bool.and_self]
theorem block_mass_checked_j4_b49 : blockMassCheck bflatBlockJ4B49 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
