module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B41 : ModeBlockData :=
  ⟨⟨41, 42, (70283298895381040801/10000000000000000000000 : ℚ), (339402616989825979/10000000000000000000000 : ℚ)⟩, [
    (41, modeDataJ4M42)], (87854123619226301/12500000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b41 : entryChecks 4 bflatBlockJ4B41.entries = true := by
  simp only [entryChecks,bflatBlockJ4B41,List.all_cons,List.all_nil,
    mode_checked_j4_m42,Bool.and_self]
theorem block_mass_checked_j4_b41 : blockMassCheck bflatBlockJ4B41 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
