import IsingBulk.HT22.Geometry.SignedMean

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory Filter IsingBulk.Preferred22
open scoped BigOperators Topology ENNReal

/-- Full actual right region, before any extrema or diameters are chosen. -/
def signedRightRegion {n : ℕ} (η : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB : ℝ) : Set (Fin n → ℝ) :=
  {θ | θ∈angularBox n ∧ ∀ i,preferredLiftedAngles B.delta (constrainedAtTotal η θ) i∈Icc (-d.b-δB) B.delta}

def signedRightCollision {n : ℕ} (η : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB : ℝ) : Set (Fin n → ℝ) :=
  {θ | θ∈signedRightRegion η d B δB ∧ ∀ i j,
    preferredLiftedAngles B.delta (constrainedAtTotal η θ) i=preferredLiftedAngles B.delta (constrainedAtTotal η θ) j}

/-- The full equality locus consists of countably many actual points in
free angular coordinates; it is not removed by an assumed regularity rule. -/
theorem signedRightCollision_null {n : ℕ} (hn : 0<n)
    (η : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta) :
    volume (signedRightCollision (n := n) η d B δB)=0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : ℤ → (Fin n → ℝ) := fun l _ => (η+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)
  have hsub : signedRightCollision (n := n) η d B δB⊆Set.range f := by
    intro θ hθ
    obtain ⟨l,hl⟩ := signedLiftedAngles_integer_mean B.delta η θ
    let w := preferredLiftedAngles B.delta (constrainedAtTotal η θ)
    have he (i : Fin (n+1)) : w i=w 0 := hθ.2 i 0
    have hw0 : w 0=(η+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ) := by
      change (∑ i,w i)=(η+2*Real.pi*(l:ℝ)) at hl
      simp_rw [he] at hl
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hl
      apply (eq_div_iff (by positivity : ((n+1:ℕ):ℝ)≠0)).mpr
      simpa only [mul_comm] using hl
    refine ⟨l,?_⟩
    funext i
    have hfree := signed_lift_free_eq_of_right d B hδB η θ hθ.1.1 hθ.1.2 i
    dsimp [f]
    rw [← hw0]
    exact (he i.castSucc).symm.trans hfree
  exact measure_mono_null hsub ((Set.countable_range f).measure_zero volume)

/-- Every actual noncollision point lies in a real shell, with a bounded
integer mean and actual extreme particle indices. -/
theorem signedRightRegion_shell_cover {n : ℕ} (η : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta) (hη : |η|≤Real.pi) :
    signedRightRegion (n := n) η d B δB \ signedRightCollision η d B δB ⊆
      ⋃ m : ℕ, ⋃ l : {l : ℤ // l∈preferredMeanIndices (n+1)},
        ⋃ i : Fin (n+1), ⋃ a : Fin (n+1),
          signedRightShell η d B δB (preferredDyadicRadius m) l.1 i a := by
  intro θ hθ
  let w := preferredLiftedAngles B.delta (constrainedAtTotal η θ)
  have hnon : (Finset.univ : Finset (Fin (n+1))).Nonempty := ⟨0,Finset.mem_univ _⟩
  obtain ⟨i,_hi,hmin⟩ := Finset.exists_min_image Finset.univ w hnon
  obtain ⟨a,_ha,hmax⟩ := Finset.exists_max_image Finset.univ w hnon
  have hext (v : Fin (n+1)) : w i≤w v ∧ w v≤w a :=
    ⟨hmin v (Finset.mem_univ _),hmax v (Finset.mem_univ _)⟩
  have hgap : 0<w a-w i := by
    have hle := (hext a).1
    by_contra hh
    have he : w a=w i := by linarith
    apply hθ.2
    refine ⟨hθ.1,?_⟩
    intro v q
    have hv := hext v
    have hq := hext q
    change w v=w q
    linarith
  have hgapπ : w a-w i≤2*Real.pi := by
    have hlo := preferred_right_interval_original d B hδB (hθ.1.2 i)
    have hup := preferred_right_interval_original d B hδB (hθ.1.2 a)
    change -Real.pi<w i ∧ w i≤Real.pi at hlo
    change -Real.pi<w a ∧ w a≤Real.pi at hup
    linarith [hlo.1,hup.2]
  obtain ⟨m,hm1,hm2⟩ := preferred_dyadic_radius_cover hgap hgapπ
  obtain ⟨l,hl⟩ := signedLiftedAngles_integer_mean B.delta η θ
  have hshell : θ∈signedRightShell η d B δB (preferredDyadicRadius m) l i a :=
    ⟨hθ.1.1,⟨hθ.1.2,hext,hm1,hm2⟩,hl⟩
  have hlmem := signedRightShell_mean_mem η hη d B hδB hshell
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨⟨l,hlmem⟩,
    Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨a,hshell⟩⟩⟩⟩

/-- True full-region nonnegative integration is dominated by the actual
mean/extrema/dyadic shell sum. No integrand measurability is assumed. -/
theorem signedRightRegion_lintegral_le_shells {n : ℕ} (hn : 0<n)
    (η : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (hη : |η|≤Real.pi) (f : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ θ in signedRightRegion η d B δB,f θ) ≤
      ∑' m : ℕ,∑ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∑ i : Fin (n+1),∑ a : Fin (n+1),
        ∫⁻ θ in signedRightShell η d B δB (preferredDyadicRadius m) l.1 i a,f θ := by
  rw [← setLIntegral_congr (sdiff_null_ae_eq_self (signedRightCollision_null hn η d B hδB))]
  apply (lintegral_mono_set (signedRightRegion_shell_cover η d B hδB hη)).trans
  apply (lintegral_iUnion_le _ f).trans
  apply ENNReal.tsum_le_tsum
  intro m
  apply (lintegral_iUnion_le _ f).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro l _
  apply (lintegral_iUnion_le _ f).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro i _
  simpa only [tsum_fintype] using lintegral_iUnion_le
    (fun a : Fin (n+1) => signedRightShell η d B δB (preferredDyadicRadius m) l.1 i a) f

end
end IsingBulk.HT22.Geometry
