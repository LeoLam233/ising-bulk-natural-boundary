import IsingBulk.HT22.Anchor.ActualPointwise
import IsingBulk.HT22.Selected.SignedConvolution
import IsingBulk.HT22.First.LocalLimit.ThreeParticleSelected.ConstrainedMass
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem real_continuous_integrableOn_angularBox {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : IntegrableOn f (angularBox n) := by
  have hh : IntegrableOn f (Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi)) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  apply hh.mono_set
  intro θ hθ
  have ht : ∀i,-Real.pi<θ i ∧ θ i≤Real.pi := by simpa [angularBox] using hθ
  exact ⟨fun i => (ht i).1.le,fun i => (ht i).2⟩

theorem signed_anchor_profile_integrable (d : PreferredBranchData) (negative : Bool) (n : ℕ)
    {ε : ℝ} (hε : 0<ε) (a : Fin (n+1)) :
    IntegrableOn (fun θ => preferredAnchorProfile d ε a (Physical.constrainedAngles negative n θ))
      (angularBox n) :=
  real_continuous_integrableOn_angularBox ((preferredAnchorProfile_continuous d hε a).comp
    (Physical.constrainedAngles_continuous negative n))

theorem signed_full_profile_integrable (d : PreferredBranchData) (negative : Bool) (n : ℕ)
    {ε : ℝ} (hε : 0<ε) :
    IntegrableOn (fun θ => ∏ i : Fin (n+1),preferredSelectedOneBodyProfile d ε
      (Physical.constrainedAngles negative n θ i)) (angularBox n) := by
  apply real_continuous_integrableOn_angularBox
  apply continuous_finsetProd
  intro i _
  exact (preferred_selected_oneBody_profile_continuous d hε).comp
    ((continuous_apply i).comp (Physical.constrainedAngles_continuous negative n))

/-- True signed anchor mass for every retained odd order at least three.
N=3 is separately controlled by the proved L^(3/2) triple convolution;
N≥5 uses the proved fourfold estimate. No finite order is discarded. -/
theorem signed_anchor_profile_mass (d : PreferredBranchData) :
    ∃ C : ℝ,0<C ∧ ∀ negative : Bool,∀ n : ℕ,3≤n+1 → ∀ ε : ℝ,0<ε → ε≤1 →
      ∀ a : Fin (n+1),
      (∫ θ in angularBox n,preferredAnchorProfile d ε a (Physical.constrainedAngles negative n θ))≤C^(n+1) := by
  obtain ⟨A,hA,hlarge⟩ := Selected.signed_profile_constrained_mass d
  obtain ⟨D,hD,hthree⟩ := LocalLimit.ThreeParticleSelected.signed_three_profile_constrained_mass d
  let K := max 1 (max A D)
  have hK : 1≤K := le_max_left _ _
  have hAK : A≤K := (le_max_left _ _).trans (le_max_right _ _)
  have hDK : D≤K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2*K,by positivity,?_⟩
  intro negative n hn ε hε hε1 a
  have hh := integral_mono (signed_anchor_profile_integrable d negative n hε a)
    ((signed_full_profile_integrable d negative n hε).const_mul 2)
    (fun θ => preferredAnchorProfile_le_full d hε hε1 a (Physical.constrainedAngles negative n θ))
  rw [integral_const_mul] at hh
  have hmass : (∫ θ in angularBox n,∏ i : Fin (n+1),preferredSelectedOneBodyProfile d ε
      (Physical.constrainedAngles negative n θ i))≤K^(n+1) := by
    by_cases hbig : 4≤n+1
    · exact (hlarge negative n hbig ε hε).trans (pow_le_pow_left₀ hA.le hAK _)
    · have he : n=2 := by omega
      subst n
      exact (hthree negative ε hε).trans (hDK.trans (le_self_pow₀ hK (by decide)))
  calc
    _ ≤ 2*K^(n+1) := hh.trans (mul_le_mul_of_nonneg_left hmass (by norm_num))
    _ ≤ 2^(n+1)*K^(n+1) := mul_le_mul_of_nonneg_right
      (le_self_pow₀ (by norm_num : (1:ℝ)≤2) (by omega)) (by positivity)
    _ = _ := by rw [mul_pow]
end
end IsingBulk.HT22.Anchor
