module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B15 : ModeBlockData :=
  ⟨⟨15, 16, (284411111756914711957/10000000000000000000000 : ℚ), (8450838073554149237/5000000000000000000000 : ℚ)⟩, [
    (15, modeDataJ2M16)], (71102777939228677989/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b15 : entryChecks 2 bflatBlockJ2B15.entries = true := by
  simp only [entryChecks,bflatBlockJ2B15,List.all_cons,List.all_nil,
    mode_checked_j2_m16,Bool.and_self]
theorem block_mass_checked_j2_b15 : blockMassCheck bflatBlockJ2B15 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
