module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part008
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B96 : ModeBlockData :=
  ⟨⟨142, 145, (970358657832064171/10000000000000000000000 : ℚ), (625291407676799831/10000000000000000000000 : ℚ)⟩, [
    (142, modeDataJ3M143),
    (143, modeDataJ3M144),
    (144, modeDataJ3M145)], (121294832229008021/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b96 : entryChecks 3 bflatBlockJ3B96.entries = true := by
  simp only [entryChecks,bflatBlockJ3B96,List.all_cons,List.all_nil,
    mode_checked_j3_m143,
    mode_checked_j3_m144,
    mode_checked_j3_m145,Bool.and_self]
theorem block_mass_checked_j3_b96 : blockMassCheck bflatBlockJ3B96 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
