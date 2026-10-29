module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B0 : ModeBlockData :=
  ⟨⟨0, 1, (9457277950232889287/1250000000000000000000 : ℚ), (71125480662852077/2000000000000000000000 : ℚ)⟩, [
    (0, modeDataJ4M1)], (15131644720372622859/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b0 : entryChecks 4 bflatBlockJ4B0.entries = true := by
  simp only [entryChecks,bflatBlockJ4B0,List.all_cons,List.all_nil,
    mode_checked_j4_m1,Bool.and_self]
theorem block_mass_checked_j4_b0 : blockMassCheck bflatBlockJ4B0 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
