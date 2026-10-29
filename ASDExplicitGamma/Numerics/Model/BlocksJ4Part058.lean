module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B58 : ModeBlockData :=
  ⟨⟨58, 59, (65384811064335880873/10000000000000000000000 : ℚ), (40547532200401849/1250000000000000000000 : ℚ)⟩, [
    (58, modeDataJ4M59)], (8173101383041985109/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b58 : entryChecks 4 bflatBlockJ4B58.entries = true := by
  simp only [entryChecks,bflatBlockJ4B58,List.all_cons,List.all_nil,
    mode_checked_j4_m59,Bool.and_self]
theorem block_mass_checked_j4_b58 : blockMassCheck bflatBlockJ4B58 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
