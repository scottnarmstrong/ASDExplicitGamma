module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B5 : ModeBlockData :=
  ⟨⟨5, 6, (75547976803169776031/10000000000000000000000 : ℚ), (355297152718465663/10000000000000000000000 : ℚ)⟩, [
    (5, modeDataJ4M6)], (7554797680316977603/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b5 : entryChecks 4 bflatBlockJ4B5.entries = true := by
  simp only [entryChecks,bflatBlockJ4B5,List.all_cons,List.all_nil,
    mode_checked_j4_m6,Bool.and_self]
theorem block_mass_checked_j4_b5 : blockMassCheck bflatBlockJ4B5 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
