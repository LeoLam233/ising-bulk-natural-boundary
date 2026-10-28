import IsingBulk.HT22.Physical.FiniteAssembly.LocalizedPartition
import IsingBulk.HT22.Finite.ComponentBound
namespace IsingBulk.HT22.Finite
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Physical IsingBulk.HT22.Physical.FiniteAssembly Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem right_limit_of_critical_partition (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (χ : (Fin n → ℝ) → ℝ)
    (P : List ((Fin n → ℝ) → ℝ)) (rem : (Fin n → ℝ) → ℝ)
    (hχ : Continuous χ) (hP : ∀ ψ∈P,Continuous ψ) (hrem : Continuous rem)
    (hpartition : ∀ θ,χ θ+(P.map (fun ψ => ψ θ)).sum+rem θ=1) (j : ℕ) {L : ℂ}
    (hcrit : Tendsto (fun ε : ℝ => ε • iteratedDeriv j
      (localizedRightIntegral negative n τ B.p B.m r χ)
      (IsingBulk.Branch.radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 L))
    (hlocal : ∀ ψ∈P,∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r ψ)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C)
    (hR : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r rem)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|)) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv j
      (rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r)
      (IsingBulk.Branch.radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 L) := by
  let F : ℝ → ℂ := fun ε => iteratedDeriv j
      (rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r)
      (IsingBulk.Branch.radialParameter d.alpha ε)-iteratedDeriv j
      (localizedRightIntegral negative n τ B.p B.m r χ)
      (IsingBulk.Branch.radialParameter d.alpha ε)
  have hb : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e → ‖F ε‖≤C*(1+|Real.log ε|) := by
    obtain ⟨CR,eR,hCR,heR,hR⟩ := hR
    refine finite_plus_log_bound F _
      (P.map (fun ψ ε => iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r ψ)
        (IsingBulk.Branch.radialParameter d.alpha ε))) ?_ hCR heR hR ?_
    · intro f hf
      obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hf
      exact hlocal ψ hψ
    · intro ε hε _
      have hh := actual_right_local_derivative_partition negative n d B hτ r hr (χ::P) rem
        (by intro ψ hψ;rcases List.mem_cons.mp hψ with rfl|hψ;exact hχ;exact hP ψ hψ)
        hrem (by simpa only [List.map_cons,List.sum_cons] using hpartition)
        (preferredRadialTrace_im_pos d hε) j
      dsimp only [F]
      rw [hh]
      simp only [List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
      ring
  have ht := hcrit.add (complex_epsilon_zero_of_log_bound F hb)
  simpa only [add_zero,←smul_add,F,add_sub_cancel] using ht

theorem coefficient_limit_of_right_limit (negative : Bool) (k : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (j : ℕ) {L : ℂ}
    (hF : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (Selected.selectedIntegral negative (2*(k+1)) τ B.p B.m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C)
    (hA : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      Anchor.derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)≤C)
    (hR : Tendsto (fun ε : ℝ => ε • iteratedDeriv j
      (rightPopulationIntegral negative (2*(k+1)) τ preferredPopulationCutoff B.p B.m r)
      (IsingBulk.Branch.radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv j (signedCoefficient negative (2*(k+1)+1))
      (IsingBulk.Branch.radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 (2*L)) := by
  let F : ℝ → ℂ := fun ε => iteratedDeriv j
    (Selected.selectedIntegral negative (2*(k+1)) τ B.p B.m)
    (IsingBulk.Branch.radialParameter d.alpha ε)
  let A : ℝ → ℂ := fun ε => ∑ a : Fin (2*(k+1)+1),iteratedDeriv j
    (anchorPopulationIntegral negative (2*(k+1)) a τ preferredPopulationCutoff B.p B.m r)
    (IsingBulk.Branch.radialParameter d.alpha ε)
  have hf : Tendsto (fun ε : ℝ => ε • F ε) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    apply complex_epsilon_zero_of_log_bound
    obtain ⟨C,e,hC,he,hb⟩ := hF
    refine ⟨C,e,hC,he,?_⟩
    intro ε hε hεe
    exact (hb ε hε hεe).trans (by nlinarith [abs_nonneg (Real.log ε)])
  have ha : Tendsto (fun ε : ℝ => ε • A ε) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    apply complex_epsilon_zero_of_log_bound
    obtain ⟨C,e,hC,he,hb⟩ := hA
    refine ⟨C,e,hC,he,?_⟩
    intro ε hε hεe
    have hh : ‖A ε‖≤Anchor.derivativeMass negative k τ B.p B.m r j
        (IsingBulk.Branch.radialParameter d.alpha ε) := norm_sum_le _ _
    exact (hh.trans (hb ε hε hεe)).trans (by nlinarith [abs_nonneg (Real.log ε)])
  have ht := hf.add ((hR.add ha).const_mul (2:ℂ))
  simp only [add_zero,zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0<ε := hε
  rw [complete_derivative_partition negative (2*(k+1)) d B hτ r hr j
    (by rw [IsingBulk.First.radialParameter_norm hε.le];linarith)
    (preferredRadialTrace_im_pos d hε)]
  change ε • F ε + 2 * (ε • _ + ε • A ε) = ε • (F ε + 2 * (_ + A ε))
  simp only [Complex.real_smul]
  ring

end
end IsingBulk.HT22.Finite
