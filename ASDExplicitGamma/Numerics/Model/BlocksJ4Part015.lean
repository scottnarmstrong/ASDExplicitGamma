module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B15 : ModeBlockData :=
  ⟨⟨15, 16, (74858338967144475019/10000000000000000000000 : ℚ), (17661447901849027/500000000000000000000 : ℚ)⟩, [
    (15, modeDataJ4M16)], (37429169483572237509/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b15 : entryChecks 4 bflatBlockJ4B15.entries = true := by
  simp only [entryChecks,bflatBlockJ4B15,List.all_cons,List.all_nil,
    mode_checked_j4_m16,Bool.and_self]
theorem block_mass_checked_j4_b15 : blockMassCheck bflatBlockJ4B15 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
