module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B89 : ModeBlockData :=
  ⟨⟨121, 124, (1031999441904590099/10000000000000000000000 : ℚ), (176606443103247943/2000000000000000000000 : ℚ)⟩, [
    (121, modeDataJ3M122),
    (122, modeDataJ3M123),
    (123, modeDataJ3M124)], (64499965119036881/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b89 : entryChecks 3 bflatBlockJ3B89.entries = true := by
  simp only [entryChecks,bflatBlockJ3B89,List.all_cons,List.all_nil,
    mode_checked_j3_m122,
    mode_checked_j3_m123,
    mode_checked_j3_m124,Bool.and_self]
theorem block_mass_checked_j3_b89 : blockMassCheck bflatBlockJ3B89 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
