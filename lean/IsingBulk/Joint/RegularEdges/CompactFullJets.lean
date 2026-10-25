import IsingBulk.Joint.RegularEdges.MixedResolventJets
import IsingBulk.Anisotropic.RegularEdges.SingularJets

/-! # Complete mixed jets, including the full lattice resolvent
A common polydisk precedes every derivative order and particle number.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology BigOperators

def independentFullIntegrand {N : ℕ} (b : ℝ) (p : NumeratorParameter) (q : Fin N→ℝ) : ℂ :=
  2*independentNumerator b p (List.ofFn q)*(1-∏ i,independentRoot b p (q i))⁻¹-
    independentNumerator b p (List.ofFn q)

/-- Uniform mixed derivatives of the actual complete integrand, retaining the
integrable quadratic-gap power instead of discarding the lattice denominator. -/
theorem compact_full_integrand_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ r C M : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧
      ∀ j : ℕ, ∃ D : ℝ, 0<D ∧ ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N→ℝ) (sel : Fin m→Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → (fun i => q (sel i))≠0 →
      ‖iteratedFDeriv ℂ j (fun p => independentFullIntegrand b p q) x‖≤
        D*particleEdgeMajorant r C M N*(N:ℝ)^j*
          (1+‖fun i => q (sel i)‖^(-(2*(j+1):ℝ))) := by
  obtain ⟨δ₁,r,C,M,hδ₁,hr,hr1,hC,hM,hnum⟩ := compact_full_numerator_polydisks hb hK hB hS
  obtain ⟨δ₂,c,hδ₂,hc,hroots⟩ := compact_roots_geometric_mixed_jets hb hK hB hS
  refine ⟨min (δ₁/2) δ₂,r,C,M,lt_min (half_pos hδ₁) hδ₂,hr,hr1,hC,hM,?_⟩
  intro j
  obtain ⟨R,hR,hroot⟩ := hroots j
  let H := fun k : ℕ => (δ₁/(2*((k+1:ℕ):ℝ)))⁻¹^k
  let A := 1+∑ k∈Finset.range (j+1), H k
  let B := (j.factorial:ℝ)^2*(c⁻¹)^(j+1)*R^j
  let D := 2^(j+1)*A*B+A
  have hH (k : ℕ) : 0≤H k := by dsimp [H]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hB' : 0<B := by dsimp [B]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro v hv x hx hi N m _ q sel hq hq0
  have hx₁ : x∈ball ((0:ℂ),v) (δ₁/2) := ball_subset_ball (min_le_left _ _) hx
  have hx₁' : x∈ball ((0:ℂ),v) δ₁ := ball_subset_ball (by linarith : δ₁/2≤δ₁) hx₁
  have hx₂ : x∈ball ((0:ℂ),v) δ₂ := ball_subset_ball (min_le_right _ _) hx
  have hn := hnum v hv N q hq
  have hrq := (hroot v hv x hx₂ hi).2
  have hgap := root_product_retained_gap (fun i => independentRoot b x (q i)) q sel hc hi
    (fun i => (hrq (q i) (hq i)).2.2)
  let E := particleEdgeMajorant r C M N
  let P := ‖fun i => q (sel i)‖^(-(2*(j+1):ℝ))
  have hE : 0≤E := particleEdgeMajorant_nonneg hr.le hC.le hM.le N
  have hP : 0≤P := Real.rpow_nonneg (norm_nonneg _) _
  have hN : 1≤(N:ℝ) := by
    have hn := (sel (Classical.arbitrary (Fin m))).isLt
    exact_mod_cast (show 1≤N by omega)
  have hNj : 1≤(N:ℝ)^j := one_le_pow₀ hN
  have hnj : ∀ k≤j, ‖iteratedFDeriv ℂ k (fun p => independentNumerator b p (List.ofFn q)) x‖≤A*E := by
    intro k hk
    have hh := norm_iteratedFDeriv_le_on_half_ball k hδ₁ hE hn.1 hn.2 hx₁
    have hsum := Finset.single_le_sum (fun i (_ : i∈Finset.range (j+1)) => hH i)
      (show k∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
    have hle : H k≤A := by dsimp [A]; linarith
    apply hh.trans
    simpa only [H,div_eq_mul_inv,inv_pow,mul_comm] using mul_le_mul_of_nonneg_right hle hE
  have hga : AnalyticAt ℂ (fun p => (1-∏ i,independentRoot b p (q i))⁻¹) x := by
    apply (analyticAt_const.sub (Finset.analyticAt_fun_prod _ (fun i _ => (hrq (q i) (hq i)).1))).inv
    exact norm_pos_iff.mp (hgap.1.trans_le hgap.2.2)
  have hgj : ∀ k≤j, ‖iteratedFDeriv ℂ k (fun p => (1-∏ i,independentRoot b p (q i))⁻¹) x‖≤B*(N:ℝ)^j*P := by
    intro k hk
    have hh := reciprocal_product_gap_mixed_jets hR hgap.1 hgap.2.1
      (fun i => (hrq (q i) (hq i)).1)
      (fun i a ha => (hrq (q i) (hq i)).2.1 a (ha.trans hk)) hgap.2.2
    have hd1 : 1≤(c*(x.1.im+‖fun i => q (sel i)‖^2))⁻¹ := (one_le_inv₀ hgap.1).mpr hgap.2.1
    have hRN : 1≤R*(N:ℝ) := by nlinarith
    have hh' : ‖iteratedFDeriv ℂ k (fun p => (1-∏ i,independentRoot b p (q i))⁻¹) x‖≤
        (j.factorial:ℝ)^2*(c*(x.1.im+‖fun i => q (sel i)‖^2))⁻¹^(j+1)*(R*(N:ℝ))^j := by
      apply hh.trans
      gcongr
    have hnorm : 0<‖fun i => q (sel i)‖ := norm_pos_iff.mpr hq0
    have hinv : (c*(x.1.im+‖fun i => q (sel i)‖^2))⁻¹≤(c*‖fun i => q (sel i)‖^2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      nlinarith
    calc
      _ ≤ (j.factorial:ℝ)^2*(c*(x.1.im+‖fun i => q (sel i)‖^2))⁻¹^(j+1)*(R*(N:ℝ))^j := hh'
      _ ≤ (j.factorial:ℝ)^2*(c*‖fun i => q (sel i)‖^2)⁻¹^(j+1)*(R*(N:ℝ))^j := by gcongr
      _ = _ := by
        rw [mul_inv_rev,mul_pow,mul_pow,inverse_square_power_eq_rpow _ hnorm.le]
        dsimp [B,P]
        ring
  have hh := affine_product_mixed_jet_bound
    (fun p => independentNumerator b p (List.ofFn q))
    (fun p => (1-∏ i,independentRoot b p (q i))⁻¹) x j (hn.1 x hx₁') hga
    (mul_nonneg hA.le hE) (show 0≤B*(N:ℝ)^j*P by positivity) hnj hgj
  change ‖iteratedFDeriv ℂ j (fun p => independentFullIntegrand b p q) x‖≤_ at hh
  apply hh.trans
  change 2^(j+1)*(A*E)*(B*(N:ℝ)^j*P)+A*E ≤ D*E*(N:ℝ)^j*(1+P)
  have hAE : 0≤A*E := mul_nonneg hA.le hE
  have h₁ : A*E≤A*E*(N:ℝ)^j := le_mul_of_one_le_right hAE hNj
  have h₂ : 0≤2^(j+1)*A*B*E*(N:ℝ)^j := by positivity
  have h₃ : 0≤A*E*(N:ℝ)^j*P := by positivity
  dsimp [D]
  nlinarith

end
end IsingBulk.Joint.RegularEdges
