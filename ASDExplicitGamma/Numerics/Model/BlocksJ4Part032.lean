module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B32 : ModeBlockData :=
  ⟨⟨32, 33, (1807468037487351899/250000000000000000000 : ℚ), (172758327241656561/5000000000000000000000 : ℚ)⟩, [
    (32, modeDataJ4M33)], (72298721499494075959/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b32 : entryChecks 4 bflatBlockJ4B32.entries = true := by
  simp only [entryChecks,bflatBlockJ4B32,List.all_cons,List.all_nil,
    mode_checked_j4_m33,Bool.and_self]
theorem block_mass_checked_j4_b32 : blockMassCheck bflatBlockJ4B32 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
