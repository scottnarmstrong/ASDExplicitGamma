module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B22 : ModeBlockData :=
  ⟨⟨22, 23, (74010530188183516337/10000000000000000000000 : ℚ), (350680816364316693/10000000000000000000000 : ℚ)⟩, [
    (22, modeDataJ4M23)], (4625658136761469771/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b22 : entryChecks 4 bflatBlockJ4B22.entries = true := by
  simp only [entryChecks,bflatBlockJ4B22,List.all_cons,List.all_nil,
    mode_checked_j4_m23,Bool.and_self]
theorem block_mass_checked_j4_b22 : blockMassCheck bflatBlockJ4B22 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
