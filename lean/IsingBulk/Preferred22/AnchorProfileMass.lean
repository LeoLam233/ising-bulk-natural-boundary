import IsingBulk.Preferred22.AnchorJacobianProfile
import IsingBulk.Preferred22.SelectedProfileConvolution
import Mathlib.MeasureTheory.Integral.Pi

/-! Uniform complete constrained integration of the independent anchored
profile. The two-particle order is evaluated separately and retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem preferredAnchorProfile_mul {N : ℕ} (d : PreferredBranchData) (ε : ℝ)
    (a : Fin N) (θ : Fin N → ℝ) :
    preferredAnchorProfile d ε a θ*preferredSelectedOneBodyProfile d ε (θ a)=
      ∏ i,preferredSelectedOneBodyProfile d ε (θ i) := by
  classical
  calc
    _ = (∏ i : Fin N,if i=a then 1 else preferredSelectedOneBodyProfile d ε (θ i))*
        (∏ i : Fin N,if i=a then preferredSelectedOneBodyProfile d ε (θ i) else 1) := by
      simp only [Fintype.prod_ite_eq',preferredAnchorProfile]
    _ = ∏ i : Fin N,(if i=a then 1 else preferredSelectedOneBodyProfile d ε (θ i))*
        (if i=a then preferredSelectedOneBodyProfile d ε (θ i) else 1) := Finset.prod_mul_distrib.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i=a <;> simp only [hi,ite_true,ite_false,one_mul,mul_one]

theorem preferredAnchorProfile_le_full {N : ℕ} (d : PreferredBranchData) {ε : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (a : Fin N) (θ : Fin N → ℝ) :
    preferredAnchorProfile d ε a θ≤2*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
  have hh := mul_le_mul_of_nonneg_left (preferred_selected_profile_lower d hε hε1 (θ a))
    (preferredAnchorProfile_nonneg d hε a θ)
  rw [mul_one] at hh
  calc
    _ ≤ preferredAnchorProfile d ε a θ*(2*preferredSelectedOneBodyProfile d ε (θ a)) := hh
    _ = 2*(preferredAnchorProfile d ε a θ*preferredSelectedOneBodyProfile d ε (θ a)) := by ring
    _ = _ := by rw [preferredAnchorProfile_mul]

theorem preferredAnchorProfile_lift {N : ℕ} (d : PreferredBranchData) (ε δ : ℝ)
    (a : Fin N) (θ : Fin N → ℝ) :
    preferredAnchorProfile d ε a (preferredLiftedAngles δ θ)=preferredAnchorProfile d ε a θ := by
  unfold preferredAnchorProfile
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=a
  · simp only [ite_eq_left hi]
  · rw [ite_eq_right hi,ite_eq_right hi]
    exact preferred_periodic_lift _ (preferred_selected_oneBody_profile_periodic d ε) _ _

theorem preferredAnchorProfile_continuous {N : ℕ} (d : PreferredBranchData) {ε : ℝ}
    (hε : 0<ε) (a : Fin N) : Continuous (preferredAnchorProfile d ε a) := by
  unfold preferredAnchorProfile
  apply continuous_finsetProd
  intro i _
  by_cases hi : i=a
  · simp only [ite_eq_left hi]
    exact continuous_const
  · simp only [ite_eq_right hi]
    exact (preferred_selected_oneBody_profile_continuous d hε).comp (continuous_apply i)

theorem preferredAnchorProfile_integrable (d : PreferredBranchData) (n : ℕ)
    {ε : ℝ} (hε : 0<ε) (a : Fin (n+1)) :
    IntegrableOn (fun θ : Fin n → ℝ => preferredAnchorProfile d ε a (constrainedAngles θ)) (angularBox n) := by
  have hc := (preferredAnchorProfile_continuous d hε a).comp (constrainedAngles_continuous n)
  have hh : IntegrableOn (fun θ : Fin n → ℝ => preferredAnchorProfile d ε a (constrainedAngles θ))
      (Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi)) volume :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  apply hh.mono_set
  intro θ hθ
  have ht : ∀i,-Real.pi<θ i ∧ θ i≤Real.pi := by simpa [angularBox] using hθ
  exact ⟨fun i => (ht i).1.le,fun i => (ht i).2⟩

theorem preferredAnchorProfile_two (d : PreferredBranchData) (ε : ℝ)
    (a : Fin 2) (θ : Fin 1 → ℝ) :
    preferredAnchorProfile d ε a (constrainedAngles θ)=preferredSelectedOneBodyProfile d ε (θ 0) := by
  have hzero : constrainedAngles θ (0 : Fin 2)=θ 0 := by
    simp [constrainedAngles]
  have hone : constrainedAngles θ (1 : Fin 2)=-θ 0 := by
    change (Fin.snoc θ (-(∑ i : Fin 1,θ i)) : Fin 2 → ℝ) (Fin.last 1)=-θ 0
    rw [Fin.snoc_last]
    simp
  unfold preferredAnchorProfile
  rw [Fin.prod_univ_two,hzero,hone]
  fin_cases a <;> simp [preferredSelectedOneBodyProfile]

/-- At N=2 the remaining independent profile is exactly one original
angular factor; no endpoint is removed and no logarithmic loss is introduced. -/
theorem preferredAnchorProfile_two_integral (d : PreferredBranchData) (ε : ℝ) (a : Fin 2) :
    (∫ θ in angularBox 1,preferredAnchorProfile d ε a (constrainedAngles θ))=
      ∫ u in Ioc (-Real.pi) Real.pi,preferredSelectedOneBodyProfile d ε u := by
  simp_rw [preferredAnchorProfile_two]
  have he : (fun θ : Fin 1 → ℝ => preferredSelectedOneBodyProfile d ε (θ 0))=
      fun θ => ∏ i : Fin 1,preferredSelectedOneBodyProfile d ε (θ i) := by funext θ; simp
  rw [he,angularBox,volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_pow,Fintype.card_fin,pow_one]

/-- The literal anchored independent profile integrates uniformly for
all even N>=2, including the finite two-particle component. -/
theorem preferred_anchor_profile_mass (d : PreferredBranchData) :
    ∃ C>0,∀ n : ℕ,2≤n+1 → Even (n+1) → ∀ ε : ℝ,0<ε → ε≤1 → ∀ a : Fin (n+1),
      (∫ θ in angularBox n,preferredAnchorProfile d ε a (constrainedAngles θ))≤C^(n+1) := by
  obtain ⟨A,hA,hfull⟩ := preferred_selected_profile_constrained_mass d
  obtain ⟨D,hD,hDmass⟩ := preferred_selected_profile_uniform_mass d
  let C := max 1 (max A D)
  have hC : 1≤C := le_max_left _ _
  have hAC : A≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2*C,by positivity,?_⟩
  intro n hn he ε hε hε1 a
  by_cases hlarge : 4≤n+1
  · have hh := integral_mono (preferredAnchorProfile_integrable d n hε a)
      ((preferred_selected_profile_product_integrable d n hε).const_mul 2)
      (fun θ => preferredAnchorProfile_le_full d hε hε1 a (constrainedAngles θ))
    rw [integral_const_mul] at hh
    calc
      _ ≤ 2*(∫ θ in angularBox n,∏ i : Fin (n+1),preferredSelectedOneBodyProfile d ε (constrainedAngles θ i)) := hh
      _ ≤ 2*A^(n+1) := mul_le_mul_of_nonneg_left (hfull n hlarge ε hε) (by norm_num)
      _ ≤ 2^(n+1)*C^(n+1) := mul_le_mul (le_self_pow₀ (by norm_num : (1:ℝ)≤2) (by omega))
        (pow_le_pow_left₀ hA.le hAC _) (by positivity) (by positivity)
      _ = _ := by rw [mul_pow]
  · have hn1 : n=1 := by
      obtain ⟨k,hk⟩ := he
      omega
    subst n
    rw [preferredAnchorProfile_two_integral]
    calc
      _ ≤ D := (hDmass ε hε).2
      _ ≤ C := hDC
      _ ≤ C^2 := le_self_pow₀ hC (by decide)
      _ ≤ (2*C)^2 := by gcongr; linarith

end
end IsingBulk.Preferred22
