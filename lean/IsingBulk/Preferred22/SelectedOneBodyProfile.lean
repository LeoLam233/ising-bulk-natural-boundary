import IsingBulk.Preferred22.SelectedOneBody

/-! A finite, continuous and periodic version of the manuscript's independent
angular square-root envelope. Its eventual norm estimates are uniform in the
positive regularization parameter. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped Topology

def preferredSelectedOneBodyProfile (d : PreferredBranchData) (ε θ : ℝ) : ℝ :=
  (Real.sqrt (|Real.cos d.b-Real.cos θ|+ε))⁻¹

lemma preferred_selected_oneBody_profile_pos (d : PreferredBranchData)
    {ε : ℝ} (hε : 0<ε) (θ : ℝ) : 0<preferredSelectedOneBodyProfile d ε θ := by
  unfold preferredSelectedOneBodyProfile
  positivity

lemma preferred_selected_oneBody_profile_continuous (d : PreferredBranchData)
    {ε : ℝ} (hε : 0<ε) : Continuous (preferredSelectedOneBodyProfile d ε) := by
  unfold preferredSelectedOneBodyProfile
  apply Continuous.inv₀
  · fun_prop
  · intro θ
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

lemma preferred_selected_oneBody_profile_periodic (d : PreferredBranchData) (ε : ℝ) :
    Function.Periodic (preferredSelectedOneBodyProfile d ε) (2*Real.pi) := by
  intro θ
  simp only [preferredSelectedOneBodyProfile,Real.cos_add_two_pi]

lemma preferred_selected_oneBody_profile_even (d : PreferredBranchData) (ε θ : ℝ) :
    preferredSelectedOneBodyProfile d ε (-θ)=preferredSelectedOneBodyProfile d ε θ := by
  simp [preferredSelectedOneBodyProfile]

end
end IsingBulk.Preferred22
