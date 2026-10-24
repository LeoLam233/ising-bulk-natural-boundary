import IsingBulk.Anisotropic.RegularEdges.SchurSupport
import IsingBulk.Tail.CompactPairUniform

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology

def edgeParamW (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (q : ℝ) : ℂ :=
  (b:ℂ)+u+B u*(1-(Real.cos q:ℂ))
def edgeParamRoot (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (q : ℝ) : ℂ :=
  continuedRoot (edgeParamW b B u q)
def edgeParamPair (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (p : ℝ × ℝ) : ℂ :=
  pairKernel (edgeParamRoot b B u p.1) (edgeParamRoot b B u p.2)
def edgeParamCanceledPair (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (p : ℝ × ℝ) : ℂ :=
  B u*canceledPair (Complex.exp (Complex.I*p.1)) (Complex.exp (Complex.I*p.2))
    (edgeParamRoot b B u p.1) (edgeParamRoot b B u p.2)

@[simp] theorem edgeParamW_zero (b : ℝ) (B : ℂ → ℂ) (q : ℝ) :
    edgeParamW b B 0 q=edgeW b (B 0) q := by simp [edgeParamW,edgeW]
@[simp] theorem edgeParamRoot_zero (b : ℝ) (B : ℂ → ℂ) (q : ℝ) :
    edgeParamRoot b B 0 q=edgeRoot b (B 0) q := by simp [edgeParamRoot,edgeRoot]

theorem edgeParamW_continuousAt (b : ℝ) {B : ℂ → ℂ} {u : ℂ}
    (hB : ContinuousAt B u) (q : ℝ) :
    ContinuousAt (fun p : ℂ × ℝ => edgeParamW b B p.1 p.2) (u,q) := by
  unfold edgeParamW
  exact (continuousAt_const.add continuousAt_fst).add
    ((hB.comp continuousAt_fst).mul (continuousAt_const.sub
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuous_cos.continuousAt.comp continuousAt_snd))))

theorem edgeParamRoot_continuousAt (b : ℝ) {B : ℂ → ℂ} {u : ℂ} {q : ℝ}
    (hB : ContinuousAt B u) (hW : edgeParamW b B u q ∈ continuedRootDomain) :
    ContinuousAt (fun p : ℂ × ℝ => edgeParamRoot b B p.1 p.2) (u,q) :=
  (continuedRoot_analyticAt hW).continuousAt.comp
    (f := fun p : ℂ × ℝ => edgeParamW b B p.1 p.2) (edgeParamW_continuousAt b hB q)

theorem edgeParamRoot_analyticAt (b : ℝ) {B : ℂ → ℂ} {u : ℂ} {q : ℝ}
    (hB : AnalyticAt ℂ B u) (hW : edgeParamW b B u q ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun v => edgeParamRoot b B v q) u := by
  exact (continuedRoot_analyticAt hW).comp (f := fun v => edgeParamW b B v q)
    ((analyticAt_const.add analyticAt_id).add (hB.mul analyticAt_const))

theorem edgeParamPair_continuousAt_zero {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (p : ℝ × ℝ) :
    ContinuousAt (fun x : ℂ × (ℝ × ℝ) => edgeParamPair b B x.1 x.2) (0,p) := by
  have hroot (q : ℝ) := edgeParamRoot_continuousAt b hc
    (show edgeParamW b B 0 q ∈ continuedRootDomain by simpa using edgeW_domain hb hB q)
  have h₁ : ContinuousAt (fun x : ℂ × (ℝ × ℝ) => edgeParamRoot b B x.1 x.2.1) (0,p) :=
    (hroot p.1).comp (x := (0,p)) (f := fun x : ℂ × (ℝ × ℝ) => (x.1,x.2.1))
    (continuousAt_fst.prodMk (continuousAt_fst.comp continuousAt_snd))
  have h₂ : ContinuousAt (fun x : ℂ × (ℝ × ℝ) => edgeParamRoot b B x.1 x.2.2) (0,p) :=
    (hroot p.2).comp (x := (0,p)) (f := fun x : ℂ × (ℝ × ℝ) => (x.1,x.2.2))
    (continuousAt_fst.prodMk (continuousAt_snd.comp continuousAt_snd))
  exact (h₁.sub h₂).div (continuousAt_const.sub (h₁.mul h₂))
    (by simpa using edgeRoot_pair_denominator_ne_zero hb hB p.1 p.2)

/-- The strict root Schur contraction persists in one complex parameter
neighborhood, uniformly on the whole angular square. -/
theorem edgeParamPair_uniform_neighborhood {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ r : ℝ, 0<r ∧ r<1 ∧ ∀ᶠ u in 𝓝 (0:ℂ),
      ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖edgeParamPair b B u (q,t)‖ ≤ r := by
  obtain ⟨r,hr,hr1,hm⟩ := edgeRoot_uniform_schur hb hB
  refine ⟨(r+1)/2,by positivity,by linarith,?_⟩
  have he : ∀ᶠ u in 𝓝 (0:ℂ), ∀ p ∈ Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi,
      ‖edgeParamPair b B u p‖ < (r+1)/2 := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro p hp
    apply (edgeParamPair_continuousAt_zero hb hB hc p).norm.eventually_lt continuousAt_const
    have hh := hm p.1 hp.1 p.2 hp.2
    simp only [edgeParamPair,edgeParamRoot_zero]
    linarith
  filter_upwards [he] with u hu q hq t ht
  exact (hu (q,t) ⟨hq,ht⟩).le

/-- All actual edge roots remain on the same analytic sheet in one uniform
complex neighborhood. No principal-power replacement is used. -/
theorem edgeParamW_uniform_domain {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∀ᶠ u in 𝓝 (0:ℂ), ∀ q ∈ Icc (-Real.pi) Real.pi,
      edgeParamW b B u q ∈ continuedRootDomain := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro q _
  exact (edgeParamW_continuousAt b hc q).eventually
    (continuedRootDomain_isOpen.mem_nhds (by simpa using edgeW_domain hb hB q))

theorem edgeParamCanceledPair_continuousAt_zero {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (p : ℝ × ℝ) :
    ContinuousAt (fun x : ℂ × (ℝ × ℝ) => edgeParamCanceledPair b B x.1 x.2) (0,p) := by
  have hroot (q : ℝ) := edgeParamRoot_continuousAt b hc
    (show edgeParamW b B 0 q ∈ continuedRootDomain by simpa using edgeW_domain hb hB q)
  have h₁ : ContinuousAt (fun x : ℂ × (ℝ × ℝ) => edgeParamRoot b B x.1 x.2.1) (0,p) :=
    (hroot p.1).comp (x := (0,p)) (f := fun x : ℂ × (ℝ × ℝ) => (x.1,x.2.1))
    (continuousAt_fst.prodMk (continuousAt_fst.comp continuousAt_snd))
  have h₂ : ContinuousAt (fun x : ℂ × (ℝ × ℝ) => edgeParamRoot b B x.1 x.2.2) (0,p) :=
    (hroot p.2).comp (x := (0,p)) (f := fun x : ℂ × (ℝ × ℝ) => (x.1,x.2.2))
    (continuousAt_fst.prodMk (continuousAt_snd.comp continuousAt_snd))
  unfold edgeParamCanceledPair
  apply (hc.comp (x := (0,p)) (f := fun x : ℂ × (ℝ × ℝ) => x.1) continuousAt_fst).mul
  apply continuousAt_canceledPair _ _ _ _ (0,p) (by fun_prop) (by fun_prop) h₁ h₂
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  simpa using edgeRoot_pair_denominator_ne_zero hb hB p.1 p.2

/-- Complete canceled pairs are only bounded by a finite constant, not
incorrectly asserted to contract. This bound persists in complex parameter. -/
theorem edgeParamCanceledPair_uniform_neighborhood {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ u in 𝓝 (0:ℂ),
      ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖edgeParamCanceledPair b B u (q,t)‖ ≤ C := by
  let K : Set (ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (edgeParamCanceledPair b B 0) K := by
    intro p _
    exact ((edgeParamCanceledPair_continuousAt_zero hb hB hc p).comp
      (f := fun p : ℝ × ℝ => ((0:ℂ),p)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hcont
  let C := max M 0+1
  refine ⟨C,by dsimp [C]; linarith [le_max_right M 0],?_⟩
  have he : ∀ᶠ u in 𝓝 (0:ℂ), ∀ p ∈ K, ‖edgeParamCanceledPair b B u p‖ < C := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    apply (edgeParamCanceledPair_continuousAt_zero hb hB hc p).norm.eventually_lt continuousAt_const
    exact (hM p hp).trans_lt (by dsimp [C]; linarith [le_max_left M 0])
  filter_upwards [he] with u hu q hq t ht
  exact (hu (q,t) ⟨hq,ht⟩).le
end
end IsingBulk.Anisotropic.RegularEdges
