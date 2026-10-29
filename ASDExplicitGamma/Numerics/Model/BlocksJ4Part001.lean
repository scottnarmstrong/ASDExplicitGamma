module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B1 : ModeBlockData :=
  ⟨⟨1, 2, (236402400439323521/31250000000000000000 : ℚ), (4444988537128197/125000000000000000000 : ℚ)⟩, [
    (1, modeDataJ4M2)], (75648768140583526719/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b1 : entryChecks 4 bflatBlockJ4B1.entries = true := by
  simp only [entryChecks,bflatBlockJ4B1,List.all_cons,List.all_nil,
    mode_checked_j4_m2,Bool.and_self]
theorem block_mass_checked_j4_b1 : blockMassCheck bflatBlockJ4B1 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
