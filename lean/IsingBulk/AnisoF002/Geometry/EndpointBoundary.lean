import IsingBulk.AnisoF002.Geometry.EndpointConverse
import IsingBulk.AnisoF002.Geometry.EndpointFiber
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The complete unsquared endpoint boundary criterion

F002 Lemma 2.1 (`lem:endpoint-sandwich`, `eq:endpoint-sandwich`).
The spectral set below is the literal closed-square unsquared incidence.
Only the five previously permitted historical spectral definitions are used.
The proof includes singular real-linear fibers by an explicit square-fiber
construction, and excludes a rank-two open-square representation at a
frontier point by continuity of the Cramer coordinates.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set Filter
open scoped Topology

def spectralSetF002 (lam : ℝ) : Set ℂ :=
  {z | ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
    spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)}

def endpointLocusF002 (lam : ℝ) : Set ℂ :=
  {z | geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0}

def cramerU (lam : ℝ) (z : ℂ) : ℝ := spectralNumF002 lam z / spectralDetF002 lam z

def cramerV (lam : ℝ) (z : ℂ) : ℝ :=
  ((spectralS z).re * (spectralA lam z).im -
    (spectralS z).im * (spectralA lam z).re) / spectralDetF002 lam z

theorem continuous_spectralS_f002 : Continuous spectralS := by
  delta spectralS
  fun_prop

theorem continuous_spectralT_f002 (lam : ℝ) : Continuous (spectralT lam) := by
  delta spectralT
  fun_prop

theorem continuous_spectralA_f002 (lam : ℝ) : Continuous (spectralA lam) := by
  delta spectralA
  fun_prop

theorem isClosed_spectralSetF002 (lam : ℝ) : IsClosed (spectralSetF002 lam) := by
  let K := Set.Icc (-1 : ℝ) 1
  let G : Set (ℂ × (K × K)) := {p | spectralA lam p.1 =
    spectralS p.1 * (p.2.1.val : ℂ) + spectralT lam p.1 * (p.2.2.val : ℂ)}
  have hG : IsClosed G := by
    apply isClosed_eq
    · exact (continuous_spectralA_f002 lam).comp continuous_fst
    · exact ((continuous_spectralS_f002.comp continuous_fst).mul
        (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
          (continuous_fst.comp continuous_snd)))).add
        (((continuous_spectralT_f002 lam).comp continuous_fst).mul
          (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
            (continuous_snd.comp continuous_snd))))
  have hproj : IsClosed (Prod.fst '' G) := isClosedMap_fst_of_compactSpace _ hG
  have heq : Prod.fst '' G = spectralSetF002 lam := by
    ext z
    constructor
    · rintro ⟨⟨z', ⟨u, v⟩⟩, hg, rfl⟩
      exact ⟨u.val, u.property, v.val, v.property, hg⟩
    · rintro ⟨u, hu, v, hv, hinc⟩
      exact ⟨(z, (⟨u, hu⟩, ⟨v, hv⟩)), hinc, rfl⟩
  rwa [heq] at hproj

theorem cramer_incidence {lam : ℝ} {z : ℂ} (hdet : spectralDetF002 lam z ≠ 0) :
    spectralA lam z = spectralS z * (cramerU lam z : ℂ) +
      spectralT lam z * (cramerV lam z : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · unfold cramerU cramerV spectralNumF002
    field_simp [hdet]
    unfold spectralDetF002
    ring
  · unfold cramerU cramerV spectralNumF002
    field_simp [hdet]
    unfold spectralDetF002
    ring

theorem cramerU_of_incidence {lam : ℝ} {z : ℂ} {u v : ℝ}
    (hdet : spectralDetF002 lam z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    cramerU lam z = u := by
  unfold cramerU
  rw [cramer_numerator_of_unsquared_incidence hinc]
  field_simp

theorem cramerV_of_incidence {lam : ℝ} {z : ℂ} {u v : ℝ}
    (hdet : spectralDetF002 lam z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    cramerV lam z = v := by
  have hre := congrArg Complex.re hinc
  have him := congrArg Complex.im hinc
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre him
  unfold cramerV
  apply (div_eq_iff hdet).2
  unfold spectralDetF002
  linear_combination (spectralS z).re * him - (spectralS z).im * hre

theorem continuous_spectralDetF002 (lam : ℝ) : Continuous (spectralDetF002 lam) := by
  delta spectralDetF002 spectralS spectralT
  fun_prop

theorem continuousAt_cramerU {lam : ℝ} {z : ℂ} (hdet : spectralDetF002 lam z ≠ 0) :
    ContinuousAt (cramerU lam) z := by
  have hnum : Continuous (spectralNumF002 lam) := by
    delta spectralNumF002 spectralA spectralT
    fun_prop
  exact hnum.continuousAt.div (continuous_spectralDetF002 lam).continuousAt hdet

theorem continuousAt_cramerV {lam : ℝ} {z : ℂ} (hdet : spectralDetF002 lam z ≠ 0) :
    ContinuousAt (cramerV lam) z := by
  have hnum : Continuous (fun w => (spectralS w).re * (spectralA lam w).im -
      (spectralS w).im * (spectralA lam w).re) := by
    delta spectralS spectralA
    fun_prop
  exact hnum.continuousAt.div (continuous_spectralDetF002 lam).continuousAt hdet

theorem interior_of_strict_incidence {lam : ℝ} {z : ℂ} {u v : ℝ}
    (hdet : spectralDetF002 lam z ≠ 0)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) (hv : v ∈ Set.Ioo (-1 : ℝ) 1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    z ∈ interior (spectralSetF002 lam) := by
  have hu0 : cramerU lam z ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [cramerU_of_incidence hdet hinc]
    exact hu
  have hv0 : cramerV lam z ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [cramerV_of_incidence hdet hinc]
    exact hv
  have hU : ∀ᶠ w in 𝓝 z, cramerU lam w ∈ Set.Ioo (-1 : ℝ) 1 :=
    (continuousAt_cramerU hdet).eventually (Ioo_mem_nhds hu0.1 hu0.2)
  have hV : ∀ᶠ w in 𝓝 z, cramerV lam w ∈ Set.Ioo (-1 : ℝ) 1 :=
    (continuousAt_cramerV hdet).eventually (Ioo_mem_nhds hv0.1 hv0.2)
  have hD : ∀ᶠ w in 𝓝 z, spectralDetF002 lam w ≠ 0 :=
    (continuous_spectralDetF002 lam).continuousAt.eventually_ne hdet
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hU, hV, hD] with w hwU hwV hwD
  exact ⟨cramerU lam w, ⟨hwU.1.le, hwU.2.le⟩,
    cramerV lam w, ⟨hwV.1.le, hwV.2.le⟩, cramer_incidence hwD⟩

theorem frontier_subset_endpointLocusF002 {lam : ℝ} (hlam : 0 < lam) :
    frontier (spectralSetF002 lam) ⊆ endpointLocusF002 lam := by
  intro z hz
  obtain ⟨u, hu, v, hv, hinc⟩ := (isClosed_spectralSetF002 lam).frontier_subset hz
  by_cases hdet : spectralDetF002 lam z = 0
  · obtain ⟨a, b, ha, hb, hend, heq⟩ :=
      complex_singular_square_fiber_endpoint (spectralS z) (spectralT lam z) u v hu hv hdet
    exact endpoint_factor_of_square_boundary hlam ha hb hend (hinc.trans heq.symm)
  · by_cases hend : (u = 1 ∨ u = -1) ∨ (v = 1 ∨ v = -1)
    · exact endpoint_factor_of_square_boundary hlam hu hv hend hinc
    · have hu' : u ∈ Set.Ioo (-1 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hu.1 (fun h => hend (Or.inl (Or.inr h.symm))),
         lt_of_le_of_ne hu.2 (fun h => hend (Or.inl (Or.inl h)))⟩
      have hv' : v ∈ Set.Ioo (-1 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hv.1 (fun h => hend (Or.inr (Or.inr h.symm))),
         lt_of_le_of_ne hv.2 (fun h => hend (Or.inr (Or.inl h)))⟩
      exact (hz.2 (interior_of_strict_incidence hdet hu' hv' hinc)).elim

/-- Both inclusions of the frozen endpoint-boundary criterion, at every fixed
positive ratio.  This statement does not assert the remaining component or
regular-edge-density theorems. -/
theorem endpoint_boundary_criterion {lam : ℝ} (hlam : 0 < lam) :
    endpointLocusF002 lam ⊆ spectralSetF002 lam ∧
      frontier (spectralSetF002 lam) ⊆ endpointLocusF002 lam := by
  refine ⟨?_, frontier_subset_endpointLocusF002 hlam⟩
  intro z hz
  obtain ⟨u, v, hu, hv, hinc⟩ := endpoint_locus_realization hlam hz
  exact ⟨u, hu, v, hv, hinc⟩

end
end IsingBulk.AnisoF002.Geometry
