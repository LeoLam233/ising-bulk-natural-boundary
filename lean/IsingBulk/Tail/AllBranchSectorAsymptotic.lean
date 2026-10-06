import IsingBulk.Tail.AllBranchExteriorAsymptotic
import IsingBulk.Tail.AllBranchAngularDomination
import IsingBulk.Tail.AngleBoxMicrocoreAsymptotic
import IsingBulk.Tail.ParticleOffset

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.PrimeFamily Filter Asymptotics
open scoped Topology

def originalAllBranchWindowTerm (p : ℕ) (d : LocalBranchData) (η outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (D : ℝ) (j : ℕ) (ε : ℝ) (N : ℕ) : ℝ :=
  if 2*p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/ε)) then
    ‖iteratedDeriv j (originalSectorIntegral N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB outer inner ho hi none) (radialParameter d.theta ε)‖ else 0

theorem originalAllBranchWindowTerm_nonneg (p : ℕ) (d : LocalBranchData) (η outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (D : ℝ) (j : ℕ) (ε : ℝ) (N : ℕ) :
    0 ≤ originalAllBranchWindowTerm p d η outer inner ho hi D j ε N := by
  unfold originalAllBranchWindowTerm
  split_ifs <;> positivity

theorem selected_original_allBranch_window_littleO {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α)
    (hαsmall : α < Real.sin (branchAngle p a b)/4) :
    let d := selectedLocalBranchData ha hb τ α hτ hα
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η : ℝ, 0 < η → η ≤ Real.sin d.thetaB/4 →
      ∀ outer inner : ℝ, ∀ ho : 0 < outer, ∀ hi : 0 < inner, outer ≤ δ₀ →
      ∀ D : ℝ, 0 ≤ D → ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      (∀ᶠ ε : ℝ in 𝓝[>] 0, Summable (originalAllBranchWindowTerm p d η outer inner ho hi D j ε)) ∧
      (fun ε : ℝ => ∑' N, originalAllBranchWindowTerm p d η outer inner ho hi D j ε N)
        =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
  let d := selectedLocalBranchData ha hb τ α hτ hα
  obtain ⟨B⟩ := lemma_branch d
  have hc := selectedLocalBranchData_c0_small ha hb τ α hτ hα
  obtain ⟨δE,hδE,hE⟩ := allBranchExterior_window_littleO B hc hαsmall p hp.one_lt.le
  let δ₀ := min δE (min (1/2:ℝ) (min d.thetaB (Real.pi-d.thetaB)))
  have hδ₀ : 0 < δ₀ := lt_min hδE (lt_min (by norm_num)
    (lt_min d.thetaB_pos (sub_pos.mpr d.thetaB_lt)))
  refine ⟨δ₀,hδ₀,?_⟩
  intro η hη hηsmall outer inner ho hi houter D hD
  have hoE : outer ≤ δE := houter.trans (min_le_left _ _)
  have horest : outer ≤ min (1/2:ℝ) (min d.thetaB (Real.pi-d.thetaB)) :=
    houter.trans (min_le_right _ _)
  have hohalf : outer ≤ 1/2 := horest.trans (min_le_left _ _)
  have hoθ : outer ≤ d.thetaB := horest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hoπ : outer ≤ Real.pi-d.thetaB := horest.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨A,c,hA,hc',hc4,hco,hM⟩ := selected_angleBox_microcore_window_littleO hp ha hb τ α hτ hα
    η outer ho hohalf hoθ hoπ ((2*p)^2/2-1) D hD
  obtain ⟨β,hβ,hExt⟩ := hE η outer ho hoE A c hA.le hc' (by linarith)
  intro j hj
  obtain ⟨hMsum,hMsmall⟩ := hM j hj
  obtain ⟨hEsum,hEsmall⟩ := hExt β le_rfl D hD j hj
  let M := fun ε => particleOffset 2 (angleBoxMicrocoreWindowTerm d η outer ho A c D j ε)
  let E := allBranchExteriorWindowTerm p d η outer ho A c β D j
  let F := originalAllBranchWindowTerm p d η outer inner ho hi D j
  have hMn (ε : ℝ) (N : ℕ) : 0 ≤ M ε N := by
    apply particleOffset_nonneg
    intro n
    unfold angleBoxMicrocoreWindowTerm
    split_ifs <;> positivity
  have hEn := allBranchExteriorWindowTerm_nonneg p d η outer ho A c β D j
  have hFn := originalAllBranchWindowTerm_nonneg p d η outer inner ho hi D j
  have hMs : ∀ᶠ ε : ℝ in 𝓝[>] 0, Summable (M ε) :=
    hMsum.mono (fun ε hs => particleOffset_summable 2 hs)
  have hmajor : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ N, F ε N ≤ M ε N+E ε N := by
    filter_upwards [radial_source_eventually_damping d hc,self_mem_nhdsWithin] with ε hdom hε
    intro N
    dsimp only [F,originalAllBranchWindowTerm]
    split_ifs with hwindow
    · have hN2 : 2 ≤ N := by omega
      have hpred : N-2+2=N := Nat.sub_add_cancel hN2
      have hf := constructedSelector_regular d.thetaB η d.alpha d.a_pos hη hηsmall d.alpha_pos
      have hh := original_allBranch_micro_exterior_domination N (by omega) d η ε outer inner ho hi hf hε
        (allBranchMicroRadius A c N) (allBranchEqualityRadius β N) hdom.2.2 j
      have hMvalue : M ε N = ‖iteratedDeriv j (microPartitionAngularIntegral N
          (constructedSelector d.thetaB η d.alpha) (Real.exp (-d.c₀*ε)) d.tau d.thetaB outer ho
          (allBranchMicroRadius A c N) (allBranchEqualityRadius β N) none) (radialParameter d.theta ε)‖ := by
        dsimp [M,particleOffset]
        rw [ite_eq_left hN2]
        unfold angleBoxMicrocoreWindowTerm
        simp only [hpred,ite_eq_left hwindow.2]
        rw [← microPartitionAngularIntegral_none (N-2) d η outer ho ε
          (microcoreRadius A c N) (allBranchEqualityRadius β N)]
        rw [hpred]
        have hradius : microcoreRadius A c N=allBranchMicroRadius A c N := by
          unfold microcoreRadius allBranchMicroRadius
          ring
        rw [hradius]
      have hEvalue : E ε N = allBranchExteriorAngularNorm N d η outer ε
          (allBranchMicroRadius A c N) (allBranchEqualityRadius β N) ho j := by
        exact ite_eq_left hwindow
      rw [hMvalue,hEvalue]
      exact hh
    · exact add_nonneg (hMn ε N) (hEn ε N)
  have hsum : ∀ᶠ ε : ℝ in 𝓝[>] 0, Summable (F ε) := by
    filter_upwards [hmajor,hMs,hEsum] with ε he hm hs
    exact Summable.of_nonneg_of_le (hFn ε) he (hm.add hs)
  have hMsmall' : (fun ε => ∑' N, M ε N) =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
    apply hMsmall.congr'
    · filter_upwards [hMsum] with ε hm
      exact (particleOffset_tsum 2 hm).symm
    · exact Eventually.of_forall (fun _ => rfl)
  refine ⟨hsum,?_⟩
  have hO : (fun ε => ∑' N, F ε N) =O[𝓝[>] 0]
      (fun ε => (∑' N, M ε N)+(∑' N, E ε N)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hmajor,hMs,hEsum,hsum] with ε he hm hs hf
    have hh := Summable.tsum_le_tsum he hf (hm.add hs)
    rw [hm.tsum_add hs] at hh
    have h0F : 0 ≤ ∑' N, F ε N := tsum_nonneg (hFn ε)
    have h0ME : 0 ≤ (∑' N, M ε N)+(∑' N, E ε N) :=
      add_nonneg (tsum_nonneg (hMn ε)) (tsum_nonneg (hEn ε))
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0F,abs_of_nonneg h0ME,one_mul] using hh
  exact hO.trans_isLittleO (hMsmall'.add hEsmall)

end
end IsingBulk.Tail
