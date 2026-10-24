import IsingBulk.Anisotropic.RegularEdges.PositiveTailBound
import IsingBulk.Anisotropic.RegularEdges.UpperIntegratedJets
import IsingBulk.Anisotropic.RegularEdges.TailSummability

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

theorem unscaledAngularCoefficient_edge_tail_jets_upper {lam b : ℝ} {U : Set ℂ}
    {zeta B S : ℂ → ℂ} (hb : |b|<1) (hB0 : 0<(B 0).im)
    (hBa : AnalyticAt ℂ B 0) (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
    (hz : ∀u∈U, zeta u∉spectralSet lam) (hs : ∀u∈U, spectralS (zeta u)≠0)
    (hB : ∀u∈U, B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U, S u=spectralS (zeta u))
    (he : ∀u∈U, edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
    (huIm : ∀u∈U, 0<u.im) (hBi : ∀u∈U, 0<(B u).im) (j : ℕ) :
    ∃ δ r C M D : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<D ∧
      ∀ w : ℂ, 0<w.im → ‖w‖<δ → w∈U → ∀ k : ℕ,
      ‖iteratedDeriv j (fun v => unscaledAngularCoefficient (2*j+3+k) lam (zeta v))
        w‖ ≤
        D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,hbound⟩ :=
    edgeFullIntegrand_integrated_jets_upper hb hB0 hBa hSa hS0 j
  refine ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,?_⟩
  intro w hε hεδ hu k
  rw [unscaledAngularCoefficient_edge_iteratedDeriv _ j hU ha hz hs hB hS he huIm hBi hu,norm_mul]
  have hf : ‖(((2*j+3+k+1).factorial:ℂ)⁻¹)‖≤1 := by
    simp only [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (2*j+3+k+1))
  exact (mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans (by
    simpa only [one_mul] using hbound w hε hεδ k)

theorem unscaledAngularCoefficient_edge_tail_bounded_upper {lam b : ℝ} {U : Set ℂ}
    {zeta B S : ℂ → ℂ} (hb : |b|<1) (hB0 : 0<(B 0).im)
    (hBa : AnalyticAt ℂ B 0) (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
    (hz : ∀u∈U, zeta u∉spectralSet lam) (hs : ∀u∈U, spectralS (zeta u)≠0)
    (hB : ∀u∈U, B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U, S u=spectralS (zeta u))
    (he : ∀u∈U, edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
    (huIm : ∀u∈U, 0<u.im) (hBi : ∀u∈U, 0<(B u).im) (j : ℕ) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧
      ∀ w : ℂ, 0<w.im → ‖w‖<δ → w∈U →
      Summable (fun k : ℕ => iteratedDeriv j
        (fun v => unscaledAngularCoefficient (2*j+3+k) lam (zeta v)) w) ∧
      ‖∑' k : ℕ, iteratedDeriv j
        (fun v => unscaledAngularCoefficient (2*j+3+k) lam (zeta v)) w‖≤L := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,hbound⟩ :=
    unscaledAngularCoefficient_edge_tail_jets_upper hb hB0 hBa hSa hS0 hU ha hz hs hB hS he huIm hBi j
  let H : ℕ → ℝ := fun k => D*((2*j+3+k+1:ℕ):ℝ)^j*
    particleEdgeMajorant r C M (2*j+3+k+1)
  have hSum : Summable H := by
    have hh := (particleEdgeMajorant_polynomial_summable hr hr1 hC hM j).comp_injective
      (i:=fun k : ℕ => 2*j+3+k+1) (by intro a b h; dsimp at h; omega)
    simpa only [H,Function.comp_def,mul_assoc] using hh.mul_left D
  have hH : ∀k,0≤H k := fun k => mul_nonneg
    (mul_nonneg hD.le (pow_nonneg (Nat.cast_nonneg _) _))
    (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)
  have hT : 0≤∑' k,H k := tsum_nonneg hH
  refine ⟨δ,1+∑' k,H k,hδ,by linarith,?_⟩
  intro w hε hεδ hu
  have hnorm : ∀ k : ℕ, ‖iteratedDeriv j
      (fun v => unscaledAngularCoefficient (2*j+3+k) lam (zeta v)) w‖≤H k := by
    intro k
    convert hbound w hε hεδ hu k using 1
    dsimp [H]
    ring
  have hn := hSum.of_nonneg_of_le (fun k => norm_nonneg _) hnorm
  refine ⟨summable_norm_iff.mp hn,?_⟩
  exact (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hnorm hSum).trans (by linarith))

end IsingBulk.Anisotropic.RegularEdges
