module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B0 : ModeBlockData :=
  ⟨⟨0, 1, (25220341575773687167/10000000000000000000000 : ℚ), (7903017666688253/2000000000000000000000 : ℚ)⟩, [
    (0, modeDataJ5M1)], (12610170787886843583/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b0 : entryChecks 5 bflatBlockJ5B0.entries = true := by
  simp only [entryChecks,bflatBlockJ5B0,List.all_cons,List.all_nil,
    mode_checked_j5_m1,Bool.and_self]
theorem block_mass_checked_j5_b0 : blockMassCheck bflatBlockJ5B0 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
