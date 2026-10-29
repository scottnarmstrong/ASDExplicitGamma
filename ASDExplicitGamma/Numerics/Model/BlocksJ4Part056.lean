module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B56 : ModeBlockData :=
  ⟨⟨56, 57, (66028029762752232593/10000000000000000000000 : ℚ), (326366523505898699/10000000000000000000000 : ℚ)⟩, [
    (56, modeDataJ4M57)], (4126751860172014537/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b56 : entryChecks 4 bflatBlockJ4B56.entries = true := by
  simp only [entryChecks,bflatBlockJ4B56,List.all_cons,List.all_nil,
    mode_checked_j4_m57,Bool.and_self]
theorem block_mass_checked_j4_b56 : blockMassCheck bflatBlockJ4B56 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
