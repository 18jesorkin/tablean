-- COMPLETENESS

import syntax
import tableau
import soundness
import modelgraphs

open has_sat

-- Each local rule preserves truth "upwards"
lemma localRuleTruth {W : Type} {M : kripkeModel W} {w : W} {X : finset formula} {B : finset (finset formula)} :
  localRule X B → (∃ Y ∈ B, (M,w) ⊨ Y) → (M,w) ⊨ X :=
begin
  intro r,
  cases r,
  case localRule.bot {
    simp,
  },
  case localRule.not {
    simp,
  },
  case localRule.neg : a f notnotf_in_a {
    intro hyp,
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩,
    intros phi phi_in_a,
    have b_is_af : b = insert f (a \ {~~f}), {
      simp at *, subst b_in_B,
    },
    have phi_in_b_or_is_f : phi ∈ b ∨ phi = ~~f, {
      rw b_is_af,
      simp,
      finish,
    },
    cases phi_in_b_or_is_f with phi_in_b phi_is_notnotf,
    {
      apply w_sat_b,
      exact phi_in_b,
    },
    {
      rw phi_is_notnotf,
      unfold evaluate at *,
      simp, -- this removes double negation
      apply w_sat_b,
      rw b_is_af ,
      simp at *,
    },
  },
  case localRule.con : a f g fandg_in_a {
    intro hyp,
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩,
    intros phi phi_in_a,
    simp at b_in_B,
    have b_is_fga : b = insert f (insert g (a \ {f⋏g})), {
      subst b_in_B, ext1, simp,
    },
    have phi_in_b_or_is_fandg : phi ∈ b ∨ phi = f⋏g, {
      rw b_is_fga,
      simp,
      finish,
    },
    cases phi_in_b_or_is_fandg with phi_in_b phi_is_fandg,
    {
      apply w_sat_b,
      exact phi_in_b,
    },
    { rw phi_is_fandg,
      unfold evaluate at *,
      split,
      { apply w_sat_b, rw b_is_fga, simp, },
      { apply w_sat_b, rw b_is_fga, simp, },
    },
  },
  case localRule.nCo : a f g not_fandg_in_a {
    intro hyp,
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩,
    intros phi phi_in_a,
    simp at *,
    have phi_in_b_or_is_notfandg : phi ∈ b ∨ phi = ~(f⋏g), {
      cases b_in_B ; { rw b_in_B, simp, finish, },
    },
    cases b_in_B,
    { -- b contains ~f
      cases phi_in_b_or_is_notfandg with phi_in_b phi_def,
      { exact w_sat_b phi phi_in_b, },
      {
        rw phi_def,
        unfold evaluate,
        rw b_in_B at w_sat_b,
        specialize w_sat_b (~f),
        rw not_and_distrib,
        left,
        unfold evaluate at w_sat_b,
        apply w_sat_b,
        finish,
      },
    },
    { -- b contains ~g
     cases phi_in_b_or_is_notfandg with phi_in_b phi_def,
      { exact w_sat_b phi phi_in_b, },
      {
        rw phi_def,
        unfold evaluate,
        rw b_in_B at w_sat_b,
        specialize w_sat_b (~g),
        rw not_and_distrib,
        right,
        unfold evaluate at w_sat_b,
        apply w_sat_b,
        finish,
      },
    },
  },
end

-- Each local rule is "complete", i.e. preserves satisfiability "upwards"
lemma localRuleCompleteness {X : finset formula} { B : finset (finset formula) } :
  localRule X B → (∃ Y ∈ B, satisfiable Y) → satisfiable X :=
begin
  intro lr,
  intro sat_B,
  rcases sat_B with ⟨Y, Y_in_B, sat_Y⟩,
  unfold satisfiable at *,
  rcases sat_Y with ⟨W,M,w,w_sat_Y⟩,
  use [W,M,w],
  apply localRuleTruth lr,
  tauto,
end

-- Lemma 11 (but rephrased to be about local tableau!?)
lemma inconsUpwards {X} {ltX : localTableau X} : (Π en ∈ endNodesOf ⟨X, ltX⟩, inconsistent en) → inconsistent X :=
begin
  intro lhs,
  unfold inconsistent at *,
  let leafTableaus : Π en ∈ endNodesOf ⟨X, ltX⟩, closedTableau en := λ Y YinEnds, (lhs Y YinEnds).some,
  split,
  exact closedTableau.loc ltX leafTableaus,
end

-- Converse of Lemma 11
lemma consToEndNodes {X} {ltX : localTableau X} : consistent X → (∃ en ∈ endNodesOf ⟨X, ltX⟩, consistent en) :=
begin
  intro consX,
  unfold consistent at *,
  have claim := not.imp consX (@inconsUpwards X ltX),
  simp at claim,
  tauto,
end

def projOfConsSimpIsCons : Π {X ϕ}, consistent X → simple X → ~□ϕ ∈ X → consistent (projection X ∪ {~ϕ}) :=
begin
  intros X ϕ consX simpX notBoxPhi_in_X,
  unfold consistent at *,
  unfold inconsistent at *,
  by_contradiction h,
  simp at *,
  cases h with ctProj,
  have ctX : closedTableau X, {
    apply closedTableau.atm notBoxPhi_in_X simpX,
    simp, exact ctProj,
  },
  cases consX, tauto,
end

lemma locTabEndSatThenSat {X Y} (ltX : localTableau X) (Y_endOf_X : Y ∈ endNodesOf ⟨X, ltX⟩) :
  satisfiable Y → satisfiable X :=
begin
  intro satY,
  induction ltX,
  case byLocalRule : X B lr next IH {
    apply localRuleCompleteness lr,
    cases lr,
    case localRule.bot : W bot_in_W {
      simp at *,
      exact Y_endOf_X,
    },
    case localRule.not : _ ϕ h {
      simp at *,
      exact Y_endOf_X,
    },
    case localRule.neg : Z ϕ notNotPhi_inX {
      simp at *,
      specialize IH (insert ϕ (Z.erase (~~ϕ))),
      simp at IH,
      apply IH,
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩,
      subst W_def,
      exact Y_endOf_W,
    },
    case localRule.con : Z ϕ ψ _ {
      simp at *,
      specialize IH (insert ϕ (insert ψ (Z.erase (ϕ⋏ψ)))),
      simp at IH,
      apply IH,
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩,
      subst W_def,
      exact Y_endOf_W,
    },
    case localRule.nCo : Z ϕ ψ _ {
      simp at *,
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩,
      cases W_def,
      all_goals { subst W_def, },
      { specialize IH (insert (~ϕ) (Z.erase (~(ϕ⋏ψ)))),
        simp at IH,
        use (insert (~ϕ) (Z.erase (~(ϕ⋏ψ)))),
        split,
        { left, refl, },
        { apply IH, exact Y_endOf_W, }
      },
      { specialize IH (insert (~ψ) (Z.erase (~(ϕ⋏ψ)))),
        simp at IH,
        use (insert (~ψ) (Z.erase (~(ϕ⋏ψ)))),
        split,
        { right, refl, },
        { apply IH, exact Y_endOf_W, }
      },
    },
  },
  case sim : X simpX {
    finish,
  },
end

lemma almostCompleteness : Π n X, lengthOfSet X = n → consistent X → satisfiable X :=
begin
  intro n,
  apply nat.strong_induction_on n,
  intros n IH,
  intros X lX_is_n consX,
  refine if simpX : simple X then _ else _,
  -- CASE 1: X is simple
  rw Lemma1_simple_sat_iff_all_projections_sat simpX,
  split,
  { -- show that X is not closed
    by_contradiction h,
    unfold consistent at consX,
    unfold inconsistent at consX,
    simp at consX,
    cases consX, apply consX,
    unfold closed at h,
    refine if botInX : ⊥ ∈ X then _ else _,
    { apply closedTableau.loc, rotate, apply localTableau.byLocalRule,
      exact localRule.bot botInX,
      intros Y YinEmpty, cases YinEmpty,
      rw botNoEndNodes, intros Y YinEmpty, cases YinEmpty,
    },
    { have f1 : ∃ (f : formula) (H : f ∈ X), ~f ∈ X := by tauto,
      have : nonempty (closedTableau X), {
      rcases f1 with ⟨f, f_in_X, notf_in_X⟩,
      fconstructor,
      apply closedTableau.loc, rotate, apply localTableau.byLocalRule,
      apply localRule.not ⟨f_in_X , notf_in_X⟩,
      intros Y YinEmpty, cases YinEmpty,
      rw notNoEndNodes, intros Y YinEmpty, cases YinEmpty,
      },
      exact classical.choice this,
    },
  },
  { -- show that all projections are sat
    intros R notBoxR_in_X,
    apply IH (lengthOfSet (projection X ∪ {~R})),
    { -- projection decreases lengthOfSet
      subst lX_is_n,
      exact atmRuleDecreasesLength notBoxR_in_X,
    },
    { refl, },
    { exact projOfConsSimpIsCons consX simpX notBoxR_in_X, },
  },
  -- CASE 2: X is not simple
  rename simpX notSimpX,
  rcases notSimpleThenLocalRule notSimpX with ⟨B,lrExists⟩,
  have lr := classical.choice lrExists,
  have rest : Π (Y : finset formula), Y ∈ B → localTableau Y, {
    intros Y Y_in_B,
    set N := hasLength.lengthOf Y,
    exact classical.choice (existsLocalTableauFor N Y (by refl))
  },
  rcases @consToEndNodes X (localTableau.byLocalRule lr rest) consX with ⟨E, E_endOf_X, consE⟩,
  have satE : satisfiable E, {
    apply IH (lengthOfSet E),
    { -- end Node of local rule is LT
      subst lX_is_n,
      apply endNodesOfLocalRuleLT E_endOf_X,
    },
    { refl, },
    { exact consE, },
  },
  exact locTabEndSatThenSat (localTableau.byLocalRule lr rest) E_endOf_X satE,
end

-- Theorem 3
theorem modelExistence : ∀ Z0, consistent Z0 → ∃ Worlds (mG : modelGraph Worlds), Z0 ∈ Worlds :=
begin
  intro Z0,
  intro Z0_is_consistent,
  let T0 := existsLocalTableauFor (hasLength.lengthOf Z0) Z0,
  sorry,
end

-- Theorem 4, page 37
theorem completeness : ∀ X, consistent X ↔ satisfiable X :=
begin
  intro X,
  split,
  { intro X_is_consistent,
    let n := lengthOfSet X,
    apply almostCompleteness n X (by refl) X_is_consistent,
  },
  -- use Theorem 2:
  exact correctness X,
end

lemma singletonCompleteness : ∀ φ, consistent {φ} ↔ satisfiable φ :=
begin
  intro f,
  have := completeness {f},
  simp only [singletonSat_iff_sat] at *,
  tauto,
end
