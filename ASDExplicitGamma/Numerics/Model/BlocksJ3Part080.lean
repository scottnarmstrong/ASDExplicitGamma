module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B80 : ModeBlockData :=
  ⟨⟨96, 98, (2965426382734783143/5000000000000000000000 : ℚ), (1031166041771474139/10000000000000000000000 : ℚ)⟩, [
    (96, modeDataJ3M97),
    (97, modeDataJ3M98)], (1482713191367391571/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b80 : entryChecks 3 bflatBlockJ3B80.entries = true := by
  simp only [entryChecks,bflatBlockJ3B80,List.all_cons,List.all_nil,
    mode_checked_j3_m97,
    mode_checked_j3_m98,Bool.and_self]
theorem block_mass_checked_j3_b80 : blockMassCheck bflatBlockJ3B80 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
