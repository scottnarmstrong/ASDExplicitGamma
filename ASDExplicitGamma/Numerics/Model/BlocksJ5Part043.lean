module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B43 : ModeBlockData :=
  ⟨⟨43, 44, (6248727784639877867/2500000000000000000000 : ℚ), (9822565305964603/2500000000000000000000 : ℚ)⟩, [
    (43, modeDataJ5M44)], (24994911138559511467/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b43 : entryChecks 5 bflatBlockJ5B43.entries = true := by
  simp only [entryChecks,bflatBlockJ5B43,List.all_cons,List.all_nil,
    mode_checked_j5_m44,Bool.and_self]
theorem block_mass_checked_j5_b43 : blockMassCheck bflatBlockJ5B43 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
