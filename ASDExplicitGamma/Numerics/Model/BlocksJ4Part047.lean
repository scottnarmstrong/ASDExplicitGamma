module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B47 : ModeBlockData :=
  ⟨⟨47, 48, (68707905612882938873/10000000000000000000000 : ℚ), (334596992570672171/10000000000000000000000 : ℚ)⟩, [
    (47, modeDataJ4M48)], (8588488201610367359/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b47 : entryChecks 4 bflatBlockJ4B47.entries = true := by
  simp only [entryChecks,bflatBlockJ4B47,List.all_cons,List.all_nil,
    mode_checked_j4_m48,Bool.and_self]
theorem block_mass_checked_j4_b47 : blockMassCheck bflatBlockJ4B47 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
