module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B6 : ModeBlockData :=
  ⟨⟨6, 7, (25214727211193827467/10000000000000000000000 : ℚ), (39509494236522381/10000000000000000000000 : ℚ)⟩, [
    (6, modeDataJ5M7)], (12607363605596913733/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b6 : entryChecks 5 bflatBlockJ5B6.entries = true := by
  simp only [entryChecks,bflatBlockJ5B6,List.all_cons,List.all_nil,
    mode_checked_j5_m7,Bool.and_self]
theorem block_mass_checked_j5_b6 : blockMassCheck bflatBlockJ5B6 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
