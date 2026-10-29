module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B46 : ModeBlockData :=
  ⟨⟨46, 47, (68982708487809348047/10000000000000000000000 : ℚ), (16771848461925451/500000000000000000000 : ℚ)⟩, [
    (46, modeDataJ4M47)], (34491354243904674023/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b46 : entryChecks 4 bflatBlockJ4B46.entries = true := by
  simp only [entryChecks,bflatBlockJ4B46,List.all_cons,List.all_nil,
    mode_checked_j4_m47,Bool.and_self]
theorem block_mass_checked_j4_b46 : blockMassCheck bflatBlockJ4B46 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
