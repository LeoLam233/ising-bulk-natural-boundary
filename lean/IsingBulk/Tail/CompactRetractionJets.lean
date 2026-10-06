import IsingBulk.Tail.CoupledOccupancyJets
import IsingBulk.Tail.DeformedRadialTransfer
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-! Fixed real jets of the actual coupled retraction, uniformly in dimension.
The normalized occupancy is differentiated as its actual angular sum. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators ContDiff
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem coordinate_jet_norm_le {N j : ℕ} (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B)
    (i : Fin N) (θ : Fin N → ℝ) : ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ => p (x i)) θ‖≤B := by
  change ‖iteratedFDeriv ℝ j (p ∘ (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) θ‖≤B
  rw [(ContinuousLinearMap.proj i).iteratedFDeriv_comp_right hp θ (by simp)]
  have hproj : ‖(ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)‖≤1 := by
    apply (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).opNorm_le_bound (by norm_num)
    intro x
    simpa using norm_le_pi_norm x i
  apply ((iteratedFDeriv ℝ j p (θ i)).norm_compContinuousLinearMap_le _).trans
  have hprod : (∏ _k : Fin j, ‖(ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)‖)≤1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hproj)
  exact (mul_le_mul_of_nonneg_right (hb (θ i)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans
    (mul_le_of_le_one_right hB hprod)

theorem periodic_finite_jet_bound (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hper : Function.Periodic p (2*Real.pi)) (k : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀ j≤k, ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B := by
  have hjet (j : ℕ) : ∃ B : ℝ, 0<B ∧ ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B := by
    have hh := (periodic_iteratedFDeriv hper j).isBounded_of_continuous Real.two_pi_pos.ne'
      (hp.continuous_iteratedFDeriv (by simp))
    obtain ⟨B,hB,hbound⟩ := hh.exists_pos_norm_le
    exact ⟨B,hB,fun x => hbound _ ⟨x,rfl⟩⟩
  choose B hB hb using hjet
  let C := 1+∑ j ∈ Finset.range (k+1), B j
  have hsum : 0≤∑ j ∈ Finset.range (k+1), B j := Finset.sum_nonneg (fun j _ => (hB j).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro j hj x
  apply (hb j x).trans
  have hh := Finset.single_le_sum (fun l (_ : l∈Finset.range (k+1)) => (hB l).le)
    (show j∈Finset.range (k+1) from Finset.mem_range.mpr (by omega))
  dsimp [C]
  linarith

def normalizedRetractionShift (N : ℕ) (p m : ℝ → ℝ) (i : Fin N) (θ : Fin N → ℝ) : ℝ :=
  -2*p (θ i)+normalizedAngularOccupancy N p θ*m (θ i)/2

theorem normalizedAngularOccupancy_smooth (N : ℕ) (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (normalizedAngularOccupancy N p) := by
  unfold normalizedAngularOccupancy
  fun_prop

theorem normalizedRetractionShift_smooth (N : ℕ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (i : Fin N) :
    ContDiff ℝ ∞ (normalizedRetractionShift N p m i) := by
  have hocc := normalizedAngularOccupancy_smooth N p hp
  unfold normalizedRetractionShift
  fun_prop

theorem periodic_retraction_jet_bound (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpper : Function.Periodic p (2*Real.pi)) (hmper : Function.Periodic m (2*Real.pi)) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → ∀ i : Fin N, ∀ θ : Fin N → ℝ,
      ‖iteratedFDeriv ℝ j (normalizedRetractionShift N p m i) θ‖≤C := by
  obtain ⟨Bp,hBp,hpB⟩ := periodic_finite_jet_bound p hp hpper j
  obtain ⟨Bm,hBm,hmB⟩ := periodic_finite_jet_bound m hm hmper j
  let C := 2*Bp+2^j*Bp*Bm/2
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN i θ
  let P := normalizedAngularOccupancy N p
  let M := fun x : Fin N → ℝ => m (x i)
  let Q := fun x : Fin N → ℝ => p (x i)
  have hP : ContDiff ℝ ∞ P := normalizedAngularOccupancy_smooth N p hp
  have hM : ContDiff ℝ ∞ M := hm.comp (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).contDiff
  have hQ : ContDiff ℝ ∞ Q := hp.comp (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).contDiff
  have hpj (l : ℕ) (hl : l≤j) : ‖iteratedFDeriv ℝ l P θ‖≤Bp :=
    normalizedAngularOccupancy_jet_bound hN p hp hBp.le (hpB l hl) θ
  have hmj (l : ℕ) (hl : l≤j) : ‖iteratedFDeriv ℝ l M θ‖≤Bm :=
    coordinate_jet_norm_le m hm hBm.le (hmB l hl) i θ
  have hprod : ‖iteratedFDeriv ℝ j (fun x => P x*M x) θ‖≤2^j*Bp*Bm := by
    apply (norm_iteratedFDeriv_mul_le hP hM θ (by simp : (j:ℕ∞ω)≤∞)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (j+1), (j.choose l:ℝ)*Bp*Bm := by
        apply Finset.sum_le_sum
        intro l hl
        have hlj : l≤j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hpj l hlj) (Nat.cast_nonneg _))
          (hmj (j-l) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
      _ = 2^j*Bp*Bm := by
        rw [← Finset.sum_mul,← Finset.sum_mul]
        have hc : (∑ l ∈ Finset.range (j+1), (j.choose l:ℝ))=(2:ℝ)^j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hc]
  have he : normalizedRetractionShift N p m i=(fun x => (-2:ℝ) • Q x+(1/2:ℝ) • (P x*M x)) := by
    funext x
    unfold normalizedRetractionShift
    simp only [smul_eq_mul]
    dsimp [Q,P,M]
    ring
  rw [he]
  change ‖iteratedFDeriv ℝ j ((-2:ℝ) • Q+(1/2:ℝ) • (fun x => P x*M x)) θ‖≤C
  rw [iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) (x := θ)
      (f := (-2:ℝ) • Q) (g := (1/2:ℝ) • (fun x => P x*M x))
      ((hQ.const_smul (-2:ℝ)).of_le (by simp)).contDiffAt
      (((hP.mul hM).const_smul (1/2:ℝ)).of_le (by simp)).contDiffAt]
  rw [iteratedFDeriv_const_smul_apply (a := (-2:ℝ)) (i := j) (x := θ) (f := Q) ((hQ.of_le (by simp)).contDiffAt),
    iteratedFDeriv_const_smul_apply (a := (1/2:ℝ)) (i := j) (x := θ) (f := fun x => P x*M x) (((hP.mul hM).of_le (by simp)).contDiffAt)]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_neg,abs_div,abs_one]
  have hqj := coordinate_jet_norm_le p hp hBp.le (hpB j le_rfl) i θ
  dsimp [C]
  nlinarith

end
end IsingBulk.Tail
