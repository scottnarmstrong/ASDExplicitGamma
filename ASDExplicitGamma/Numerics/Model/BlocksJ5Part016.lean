module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B16 : ModeBlockData :=
  ⟨⟨16, 17, (25186672435491936159/10000000000000000000000 : ℚ), (39481536740071989/10000000000000000000000 : ℚ)⟩, [
    (16, modeDataJ5M17)], (12593336217745968079/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b16 : entryChecks 5 bflatBlockJ5B16.entries = true := by
  simp only [entryChecks,bflatBlockJ5B16,List.all_cons,List.all_nil,
    mode_checked_j5_m17,Bool.and_self]
theorem block_mass_checked_j5_b16 : blockMassCheck bflatBlockJ5B16 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
