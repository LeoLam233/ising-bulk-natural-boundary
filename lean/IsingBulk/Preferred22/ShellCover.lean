import IsingBulk.Preferred22.ShellIntegration
import IsingBulk.Preferred22.ShellGeometry
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Algebra.Order.Archimedean.Basic

/-! A genuine countable shell cover of the full actual right region. The
one-sided lift supplies a literal integer mean; its full collision locus
is null in the actual constrained Haar variables. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

/-- Full actual right region, before any extrema or diameters are chosen. -/
def preferredRightRegion {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB : ℝ) : Set (Fin n → ℝ) :=
  {θ | θ∈angularBox n ∧ ∀ i,preferredLiftedAngles B.delta (constrainedAngles θ) i∈Icc (-d.b-δB) B.delta}

def preferredRightCollision {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB : ℝ) : Set (Fin n → ℝ) :=
  {θ | θ∈preferredRightRegion d B δB ∧ ∀ i j,
    preferredLiftedAngles B.delta (constrainedAngles θ) i=preferredLiftedAngles B.delta (constrainedAngles θ) j}

/-- Fixed dyadic radii cover every positive source diameter up to 2*pi. -/
def preferredDyadicRadius (m : ℕ) : ℝ := 2*Real.pi*(1/2:ℝ)^(m+1)

theorem preferredDyadicRadius_pos (m : ℕ) : 0<preferredDyadicRadius m := by
  unfold preferredDyadicRadius
  positivity

/-- The true lifted sum is an integer multiple of 2*pi for every input. -/
theorem preferredLiftedAngles_integer_mean {n : ℕ} (δ : ℝ) (θ : Fin n → ℝ) :
    ∃ l : ℤ,(∑ i,preferredLiftedAngles δ (constrainedAngles θ) i)=2*Real.pi*(l:ℝ) := by
  let k : Fin (n+1) → ℤ := fun i =>
    toIocDiv (by positivity : 0<2*Real.pi) (-Real.pi-δ) (constrainedAngles θ i)
  refine ⟨-∑ i,k i,?_⟩
  simp only [preferredLiftedAngles,toIocMod,Finset.sum_sub_distrib,zsmul_eq_mul]
  rw [constrainedAngles_sum]
  simp only [zero_sub,Int.cast_neg,Int.cast_sum]
  dsimp [k]
  rw [← Finset.sum_mul]
  ring

theorem preferred_dyadic_radius_cover {a : ℝ} (ha : 0<a) (haπ : a≤2*Real.pi) :
    ∃ m : ℕ,preferredDyadicRadius m≤a ∧ a≤2*preferredDyadicRadius m := by
  have hp : 0<2*Real.pi := by positivity
  obtain ⟨m,hl,hu⟩ := exists_nat_pow_near_of_lt_one (div_pos ha hp)
    ((div_le_one hp).mpr haπ) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  refine ⟨m,?_,?_⟩
  · unfold preferredDyadicRadius
    simpa only [mul_comm] using ((lt_div_iff₀ hp).mp hl).le
  · have hh := (div_le_iff₀ hp).mp hu
    simpa only [preferredDyadicRadius,pow_succ] using (show a≤2*(2*Real.pi*((1/2:ℝ)^m*(1/2))) by nlinarith)

/-- The full equality locus consists of countably many actual points in
free angular coordinates; it is not removed by an assumed regularity rule. -/
theorem preferredRightCollision_null {n : ℕ} (hn : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta) :
    volume (preferredRightCollision (n := n) d B δB)=0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : ℤ → (Fin n → ℝ) := fun l _ => 2*Real.pi*(l:ℝ)/((n+1:ℕ):ℝ)
  have hsub : preferredRightCollision (n := n) d B δB⊆Set.range f := by
    intro θ hθ
    obtain ⟨l,hl⟩ := preferredLiftedAngles_integer_mean B.delta θ
    let w := preferredLiftedAngles B.delta (constrainedAngles θ)
    have he (i : Fin (n+1)) : w i=w 0 := hθ.2 i 0
    have hw0 : w 0=2*Real.pi*(l:ℝ)/((n+1:ℕ):ℝ) := by
      change (∑ i,w i)=2*Real.pi*(l:ℝ) at hl
      simp_rw [he] at hl
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hl
      apply (eq_div_iff (by positivity : ((n+1:ℕ):ℝ)≠0)).mpr
      simpa only [mul_comm] using hl
    refine ⟨l,?_⟩
    funext i
    have hfree := preferred_lift_free_eq_of_right d B hδB θ hθ.1.1 hθ.1.2 i
    dsimp [f]
    rw [← hw0]
    exact (he i.castSucc).symm.trans hfree
  exact measure_mono_null hsub ((Set.countable_range f).measure_zero volume)

/-- Every actual noncollision point lies in a real shell, with a bounded
integer mean and actual extreme particle indices. -/
theorem preferredRightRegion_shell_cover {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta) :
    preferredRightRegion (n := n) d B δB \ preferredRightCollision d B δB ⊆
      ⋃ m : ℕ, ⋃ l : {l : ℤ // l∈preferredMeanIndices (n+1)},
        ⋃ i : Fin (n+1), ⋃ a : Fin (n+1),
          preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a := by
  intro θ hθ
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
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
  obtain ⟨l,hl⟩ := preferredLiftedAngles_integer_mean B.delta θ
  have hshell : θ∈preferredRightShell d B δB (preferredDyadicRadius m) l i a :=
    ⟨hθ.1.1,hθ.1.2,hl,hext,hm1,hm2⟩
  have hlmem := preferredRightShell_mean_mem d B hδB hshell
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨⟨l,hlmem⟩,
    Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨a,hshell⟩⟩⟩⟩

/-- True full-region nonnegative integration is dominated by the actual
mean/extrema/dyadic shell sum. No integrand measurability is assumed. -/
theorem preferredRightRegion_lintegral_le_shells {n : ℕ} (hn : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (f : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ θ in preferredRightRegion d B δB,f θ) ≤
      ∑' m : ℕ,∑ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∑ i : Fin (n+1),∑ a : Fin (n+1),
        ∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a,f θ := by
  rw [← setLIntegral_congr (sdiff_null_ae_eq_self (preferredRightCollision_null hn d B hδB))]
  apply (lintegral_mono_set (preferredRightRegion_shell_cover d B hδB)).trans
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
    (fun a : Fin (n+1) => preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a) f

end
end IsingBulk.Preferred22
