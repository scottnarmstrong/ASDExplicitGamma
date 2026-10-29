module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B42 : ModeBlockData :=
  ⟨⟨42, 43, (2797087828900733819/10000000000000000000000 : ℚ), (1190132800257004603/5000000000000000000000 : ℚ)⟩, [
    (42, modeDataJ2M43)], (1398543914450366909/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b42 : entryChecks 2 bflatBlockJ2B42.entries = true := by
  simp only [entryChecks,bflatBlockJ2B42,List.all_cons,List.all_nil,
    mode_checked_j2_m43,Bool.and_self]
theorem block_mass_checked_j2_b42 : blockMassCheck bflatBlockJ2B42 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
