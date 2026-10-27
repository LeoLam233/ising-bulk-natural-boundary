import IsingBulk.Preferred22.ContourMatrix
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-! Actual periodic bump and normalized occupancy jets for LT22.
The projection/occupancy arguments adapt the proper finite-jet infrastructure
in the pinned repository's CoupledOccupancyJets and CompactRetractionJets;
no old retraction or complete-tail estimate is imported or assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem bump_derivative_periodic {p : ℝ → ℝ} {T : ℝ}
    (hp : Function.Periodic p T) : Function.Periodic (deriv p) T := by
  intro x
  rw [← deriv_comp_add_const p T x, funext hp]

theorem bump_iteratedFDeriv_periodic {p : ℝ → ℝ} {T : ℝ}
    (hp : Function.Periodic p T) (j : ℕ) :
    Function.Periodic (iteratedFDeriv ℝ j p) T := by
  intro x
  rw [← iteratedFDeriv_comp_add_right j T x]
  exact congrArg (fun f : ℝ → ℝ => iteratedFDeriv ℝ j f x) (funext hp)

theorem bump_finite_jets (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hper : Function.Periodic p (2*Real.pi)) (J : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀ j≤J, ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B := by
  have hjet (j : ℕ) : ∃ B : ℝ, 0<B ∧ ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B := by
    have hh := (bump_iteratedFDeriv_periodic hper j).isBounded_of_continuous Real.two_pi_pos.ne'
      (hp.continuous_iteratedFDeriv (by simp))
    obtain ⟨B,hB,hbound⟩ := hh.exists_pos_norm_le
    exact ⟨B,hB,fun x => hbound _ ⟨x,rfl⟩⟩
  choose B hB hb using hjet
  let C := 1+∑ j ∈ Finset.range (J+1), B j
  have hsum : 0≤∑ j ∈ Finset.range (J+1), B j := Finset.sum_nonneg (fun j _ => (hB j).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro j hj x
  apply (hb j x).trans
  have hh := Finset.single_le_sum (fun l (_ : l∈Finset.range (J+1)) => (hB l).le)
    (show j∈Finset.range (J+1) from Finset.mem_range.mpr (by omega))
  dsimp [C]
  linarith

theorem coordinate_real_jet_le {N j : ℕ} (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B)
    (i : Fin N) (θ : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ => p (x i)) θ‖≤B := by
  change ‖iteratedFDeriv ℝ j (p ∘ (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) θ‖≤B
  rw [(ContinuousLinearMap.proj i).iteratedFDeriv_comp_right hp θ (by simp)]
  have hproj : ‖(ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)‖≤1 := by
    apply (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).opNorm_le_bound zero_le_one
    intro x
    simpa using norm_le_pi_norm x i
  apply ((iteratedFDeriv ℝ j p (θ i)).norm_compContinuousLinearMap_le _).trans
  have hprod : (∏ _k : Fin j, ‖(ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)‖)≤1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hproj)
  exact (mul_le_mul_of_nonneg_right (hb (θ i)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans
    (mul_le_of_le_one_right hB hprod)

def normalizedOccupancy {N : ℕ} (p : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  occupancy p θ / N

theorem normalizedOccupancy_contDiff {N : ℕ} (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (@normalizedOccupancy N p) := by
  unfold normalizedOccupancy occupancy
  fun_prop

theorem normalizedOccupancy_jet_le {N j : ℕ} (hN : 0<N) (p : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) {B : ℝ} (hB : 0≤B)
    (hb : ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B) (θ : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ j (@normalizedOccupancy N p) θ‖≤B := by
  let f : Fin N → (Fin N → ℝ) → ℝ := fun i θ => p (θ i)
  have hsmooth (i : Fin N) : ContDiff ℝ j (f i) :=
    (hp.of_le (by simp)).comp (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).contDiff
  have hcoord (i : Fin N) : ‖iteratedFDeriv ℝ j (f i) θ‖≤B :=
    coordinate_real_jet_le p hp hB hb i θ
  have hsum : ContDiff ℝ j (fun x => ∑ i, f i x) := ContDiff.sum (fun i _ => hsmooth i)
  have he : @normalizedOccupancy N p = (fun x => (N:ℝ)⁻¹ • (∑ i, f i x)) := by
    funext x
    simp [normalizedOccupancy, occupancy, f, div_eq_mul_inv, mul_comm]
  rw [he,iteratedFDeriv_const_smul_apply' hsum.contDiffAt,
    iteratedFDeriv_fun_sum_apply (fun i _ => (hsmooth i).contDiffAt),norm_smul]
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hh : ‖∑ i, iteratedFDeriv ℝ j (f i) θ‖≤(N:ℝ)*B :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hcoord i))
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans_eq (by field_simp)

theorem real_two_factor_uniform_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (J j : ℕ) (hj : j≤J) {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hb : ∀ r≤J, ‖iteratedFDeriv ℝ r f x‖≤B)
    (hd : ∀ r≤J, ‖iteratedFDeriv ℝ r g x‖≤D) :
    ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖≤2^J*B*D := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (by simp : (j:ℕ∞ω)≤∞)).trans
  calc
    _ ≤ ∑ r ∈ Finset.range (j+1), (j.choose r:ℝ)*B*D := by
      apply Finset.sum_le_sum
      intro r hr
      have hrj : r≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb r (hrj.trans hj)) (Nat.cast_nonneg _))
        (hd (j-r) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
    _ = 2^j*B*D := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := by gcongr; norm_num

theorem real_difference_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (j : ℕ) {B D : ℝ}
    (hb : ‖iteratedFDeriv ℝ j f x‖≤B) (hd : ‖iteratedFDeriv ℝ j g x‖≤D) :
    ‖iteratedFDeriv ℝ j (fun y => f y-g y) x‖≤B+D := by
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add hb hd)

theorem ofReal_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) (j : ℕ) {B : ℝ}
    (hb : ‖iteratedFDeriv ℝ j f x‖≤B) :
    ‖iteratedFDeriv ℝ j (fun y => (f y:ℂ)) x‖≤B := by
  have hh := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := x) hf.contDiffAt
    (by simp : (j:ℕ∞ω)≤∞)
  have hc : ‖Complex.ofRealCLM‖≤1 :=
    Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun y => by simp)
  exact (hh.trans (mul_le_of_le_one_left (norm_nonneg _) hc)).trans hb

end
end IsingBulk.Preferred22
