module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B37 : ModeBlockData :=
  ⟨⟨37, 38, (35616148840026111963/5000000000000000000000 : ℚ), (6845723598377351/200000000000000000000 : ℚ)⟩, [
    (37, modeDataJ4M38)], (2849291907202088957/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b37 : entryChecks 4 bflatBlockJ4B37.entries = true := by
  simp only [entryChecks,bflatBlockJ4B37,List.all_cons,List.all_nil,
    mode_checked_j4_m38,Bool.and_self]
theorem block_mass_checked_j4_b37 : blockMassCheck bflatBlockJ4B37 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
