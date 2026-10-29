module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B41 : ModeBlockData :=
  ⟨⟨41, 42, (1563429683400477369/625000000000000000000 : ℚ), (3931018907746881/1000000000000000000000 : ℚ)⟩, [
    (41, modeDataJ5M42)], (25014874934407637903/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b41 : entryChecks 5 bflatBlockJ5B41.entries = true := by
  simp only [entryChecks,bflatBlockJ5B41,List.all_cons,List.all_nil,
    mode_checked_j5_m42,Bool.and_self]
theorem block_mass_checked_j5_b41 : blockMassCheck bflatBlockJ5B41 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
