module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B13 : ModeBlockData :=
  ⟨⟨13, 14, (15009170280321330331/2000000000000000000000 : ℚ), (353791701697219289/10000000000000000000000 : ℚ)⟩, [
    (13, modeDataJ4M14)], (37522925700803325827/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b13 : entryChecks 4 bflatBlockJ4B13.entries = true := by
  simp only [entryChecks,bflatBlockJ4B13,List.all_cons,List.all_nil,
    mode_checked_j4_m14,Bool.and_self]
theorem block_mass_checked_j4_b13 : blockMassCheck bflatBlockJ4B13 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
