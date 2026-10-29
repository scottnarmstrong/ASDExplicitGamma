module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B1 : ModeBlockData :=
  ⟨⟨1, 2, (1340319739791182062761/5000000000000000000000 : ℚ), (1196798709746146467819/10000000000000000000000 : ℚ)⟩, [
    (1, modeDataJ0M2)], (2680639479582364125521/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b1 : entryChecks 0 bflatBlockJ0B1.entries = true := by
  simp only [entryChecks,bflatBlockJ0B1,List.all_cons,List.all_nil,
    mode_checked_j0_m2,Bool.and_self]
theorem block_mass_checked_j0_b1 : blockMassCheck bflatBlockJ0B1 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
