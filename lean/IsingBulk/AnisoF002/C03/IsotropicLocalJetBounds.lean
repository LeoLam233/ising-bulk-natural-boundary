import IsingBulk.AnisoF002.C03.IsotropicBanachInverseJets
import IsingBulk.AnisoF002.C03.IsotropicScalarCurrent

/-!
# Local finite real-jet bounds for the smooth regular frame

These local forms of the checked multilinear product and composition
estimates do not assume global analyticity or global smooth extensions.
They apply to the actual inverse Jacobian and to real angular cutoffs.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_comp_at_le (f : E → F) (g : F → G) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x)) (C D : ℝ)
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨t, htv, ht, hxt⟩ := mem_nhds_iff.mp hv
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ n f y ∧ f y ∈ t :=
    (hf.eventually (by simp)).and (hf.continuousAt.eventually (ht.mem_nhds hxt))
  obtain ⟨s, hsnear, hs, hxs⟩ := mem_nhds_iff.mp hnear
  have hfs : ContDiffOn ℝ n f s := fun y hy => (hsnear hy).1.contDiffWithinAt
  have hgs : ContDiffOn ℝ n g t := hgv.mono htv
  have hmaps : MapsTo f s t := fun y hy => (hsnear hy).2
  have hh := norm_iteratedFDerivWithin_comp_le hgs hfs (n := n) le_rfl
    ht.uniqueDiffOn hs.uniqueDiffOn hmaps hxs
    (C := C) (D := D)
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen i ht hxt]; exact hC i hi)
    (fun i hi hin => by rw [iteratedFDerivWithin_of_isOpen i hs hxs]; exact hD i hi hin)
  rwa [iteratedFDerivWithin_of_isOpen n hs hxs] at hh

theorem norm_iteratedFDeriv_mul_at_le (f g : E → ℂ) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ n f y ∧ ContDiffAt ℝ n g y :=
    (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨s, hsnear, hs, hxs⟩ := mem_nhds_iff.mp hnear
  have hh := norm_iteratedFDerivWithin_mul_le
    (show ContDiffOn ℝ n f s from fun y hy => (hsnear hy).1.contDiffWithinAt)
    (show ContDiffOn ℝ n g s from fun y hy => (hsnear hy).2.contDiffWithinAt)
    hs.uniqueDiffOn hxs (n := n) le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ hs hxs] using hh

theorem norm_iteratedFDeriv_scalarPartial_le (f : E → ℂ) (v x : E) (n : ℕ)
    (hf : ContDiffAt ℝ (n + 1) f x) :
    ‖iteratedFDeriv ℝ n (scalarPartial f v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hd : ContDiffAt ℝ n (fderiv ℝ f) x := hf.fderiv_right (m := n) (by norm_cast)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := v) hd (n := n) le_rfl
  change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ ≤ _
  simpa only [norm_iteratedFDeriv_fderiv] using hh

theorem norm_iteratedFDeriv_finsetSum_le {ι : Type*} (u : Finset ι) (f : ι → E → F)
    (x : E) (n : ℕ) (hf : ∀ i ∈ u, ContDiffAt ℝ n (f i) x) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ i ∈ u, f i y) x‖ ≤
      ∑ i ∈ u, ‖iteratedFDeriv ℝ n (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply hf]
  exact norm_sum_le _ _

end IsingBulk.AnisoF002.Isotropic
