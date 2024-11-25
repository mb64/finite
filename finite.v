(* Several things: *)
(* 1. Finitary PCF type system + operational semantics *)
(* 2. Finite domain theory *)
(* 3. Soundness and adequacy for PCF *)
(* 4. Extract a decision procedure *)

Require Import List.
Require Import String. Open Scope string_scope.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.EqdepFacts.
Require Import RelationClasses.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.
Require Import FunInd.
Require Import Recdef.
Import EqNotations.
Import ListNotations.
(* Require Import Coq.Logic.PropExtensionality. *)


From stdpp Require Import gmap finite vector.

Section Util.
  Lemma unit_unique (x y : unit) : x = y.
    destruct x, y.
    reflexivity.
  Qed.

  Global Instance prop_irrel (P : Prop) : ProofIrrel P.
  Proof.
    intros x y.
    apply proof_irrelevance.
  Qed.

  Global Instance eq_dec_fun `{Finite A} `{EqDecision B} :
    EqDecision (A -> B).
  Proof.
    intros f g.
    destruct (decide (∀ x, f x = g x)).
    - left.
      extensionality x.
      auto.
    - right.
      intro. apply n. intro.
      congruence.
  Defined.

  Definition vec_to_fun `{Finite A} {B} (v : vec B (card A)) : A -> B :=
    fun x => v !!! encode_fin x.

  Instance vec_to_fun_surj `{Finite A} {B} : Surj (=) (vec_to_fun (A:=A) (B:=B)).
  Proof.
    intro f.
    exists (fun_to_vec (fun x => f (decode_fin x))).
    extensionality x.
    unfold vec_to_fun.
    rewrite lookup_fun_to_vec.
    rewrite decode_encode_fin.
    reflexivity.
  Qed.

  Program Global Instance finite_fun `{Finite A} `{Finite B} : Finite (A -> B) :=
    surjective_finite (fun (v : vec B (card A)) (x : A) => v !!! encode_fin x).

  Lemma sig_eq {A} {P} (x y : {x:A | P x}) : proj1_sig x = proj1_sig y -> x = y.
  Proof.
    destruct x as [x], y as [y].
    simpl.
    intro.
    apply eq_dep_eq_sig.
    apply eq_sigT_eq_dep.
    apply eq_sigT_sig_eq.
    apply (exist _ H).
    apply proof_irrelevance.
  Qed.

  Global Instance eq_dec_sig `{EqDecision A} {P : A -> Prop} :
    EqDecision {x:A | P x}.
  Proof.
    intros [x] [y].
    destruct (decide (x = y)) as [H|H].
    - left; auto using sig_eq.
    - right; congruence.
  Defined.

  Global Instance decide_and `{Decision P} `{Decision Q} : Decision (P ∧ Q).
  Proof.
    unfold Decision.
    destruct (decide P), (decide Q); eauto; right; intros []; eauto.
  Defined.

  Lemma list_filter_sig_lengths_le {A:Type} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (xs : list A) :
    (∀ x, P x -> Q x) ->
    length (list_filter_sig P xs) ≤ length (list_filter_sig Q xs).
  Proof.
    intros.
    induction xs; simpl; eauto.
    case_decide; case_decide; simpl; try lia.
    contradiction H3; eauto.
  Qed.

  Lemma list_filter_sig_lengths_lt {A:Type} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (xs : list A) :
    (∀ x, P x -> Q x) -> (∃ x, x ∈ xs /\ Q x /\ ~ P x) ->
    length (list_filter_sig P xs) < length (list_filter_sig Q xs).
  Proof.
    intros.
    revert H2.
    induction xs; intros [x [?[]]]; simpl in *; set_unfold; destruct H2.
    - subst.
      case_decide; case_decide; try contradiction.
      simpl.
      pose proof (list_filter_sig_lengths_le xs H1).
      lia.
    - unshelve (epose proof (IHxs _)); eauto.
      case_decide; case_decide; simpl; try lia.
      contradiction H7; eauto.
  Qed.

  Global Instance decide_sigT {A:Type} {P:A -> Type} :
    EqDecision A -> (forall x, EqDecision (P x)) -> EqDecision {x:A & P x}.
  Proof.
    intros.
    intros [x p] [x' p'].
    destruct (decide (x = x')); last (right; congruence).
    simplify_eq.
    destruct (decide (p = p')); [left|right]; try congruence.
    eauto using eq_sigT_eq_dep, eq_dep_eq.
  Defined.

End Util.

Section Lang.
  (* 1. Finitary PCF, type system + operational semantics *)

  Inductive ty : Set := Bool | Fun (a b : ty).

  Inductive exp : Set :=
  | Var (x : string)
  | Const (b : bool)
  | If (e1 e2 e3 : exp)
  | App (e1 e2 : exp)
  | Lam (x : string) (a : ty) (body : exp)
  | Fix (f x : string) (a b : ty) (body : exp).

  Coercion Var : string >-> exp.
  Coercion Const : bool >-> exp.

  Global Instance dec_eq_ty : EqDecision ty.
  Proof.
    unfold EqDecision, Decision.
    decide equality.
  Defined.

  (* Type system *)
  Definition Ctx := list (string * ty).
  Hint Unfold Ctx : core.

  Fixpoint lookup {A} (Γ : list (string * A)) (x : string) : option A :=
    match Γ with
    | [] => None
    | (x',t) :: xs => if decide (x = x') then Some t else lookup xs x
    end.

  Ltac simp_lookup :=
    simpl lookup in *; simplify_eq; repeat (case_decide; simplify_eq; eauto).

  Inductive typed : Ctx -> exp -> ty -> Prop :=
  | t_var Γ x ty : lookup Γ x = Some ty -> typed Γ (Var x) ty
  | t_const Γ b : typed Γ (Const b) Bool
  | t_if Γ e1 e2 e3 ty :
      typed Γ e1 Bool ->
      typed Γ e2 ty ->
      typed Γ e3 ty ->
      typed Γ (If e1 e2 e3) ty
  | t_app Γ e1 e2 t1 t2 :
      typed Γ e1 (Fun t1 t2) ->
      typed Γ e2 t1 ->
      typed Γ (App e1 e2) t2
  | t_lam Γ x body t1 t2 :
      typed ((x, t1) :: Γ) body t2 ->
      typed Γ (Lam x t1 body) (Fun t1 t2)
  | t_fix Γ f x body t1 t2 :
      typed ((x, t1) :: (f, Fun t1 t2) :: Γ) body t2 ->
      typed Γ (Fix f x t1 t2 body) (Fun t1 t2).

  Lemma weaken_typed Γ Γ' e t :
    typed Γ e t -> typed (Γ ++ Γ') e t.
  Proof.
    intros.
    revert Γ'.
    induction H; eauto using typed; intros; constructor.
    - revert H; induction Γ as [|[]]; intro; simp_lookup.
    - apply IHtyped.
  Qed.

  Lemma weaken_typed' Γ e t :
    typed [] e t -> typed Γ e t.
  Proof.
    apply (weaken_typed []).
  Qed.

  (* Operational semantics *)
  Definition is_value (x : exp) :=
    match x with
    | Const _ | Lam _ _ _ | Fix _ _ _ _ _ => True
    | _ => False
    end.

  Fixpoint subst x v e :=
    match e with
    | Var x' => if decide (x' = x) then v else Var x'
    | Const b => Const b
    | If e1 e2 e3 => If (subst x v e1) (subst x v e2) (subst x v e3)
    | App e1 e2 => App (subst x v e1) (subst x v e2)
    | Lam x' a body =>
        if decide (x' = x) then Lam x' a body else Lam x' a (subst x v body)
    | Fix f x' a b body =>
        if decide (x' = x \/ f = x) then Fix f x' a b body else Fix f x' a b (subst x v body)
    end.

  Inductive step : exp -> exp -> Prop :=
  | step_app_1 e1 e1' e2 :
    step e1 e1' -> step (App e1 e2) (App e1' e2)
  | step_app_2 v1 e2 e2' :
    is_value v1 ->
    step e2 e2' -> step (App v1 e2) (App v1 e2')
  | step_beta_lam x a body arg :
    is_value arg ->
    step (App (Lam x a body) arg) (subst x arg body)
  | step_beta_fix f x a b body arg :
    is_value arg ->
    step (App (Fix f x a b body) arg) (subst f (Fix f x a b body) (subst x arg body))
  | step_if_1 e1 e1' e2 e3 :
    step e1 e1' -> step (If e1 e2 e3) (If e1' e2 e3)
  | step_if_true e2 e3 :
    step (If true e2 e3) e2
  | step_if_false e2 e3 :
    step (If false e2 e3) e3.

  Lemma step_app_1' e1 e1' e2 :
    rtc step e1 e1' -> rtc step (App e1 e2) (App e1' e2).
  Proof. induction 1; eauto using rtc_refl, rtc_l, step. Qed.

  Lemma step_app_2' v1 e2 e2' : is_value v1 ->
    rtc step e2 e2' -> rtc step (App v1 e2) (App v1 e2').
  Proof. induction 2; eauto using rtc_refl, rtc_l, step. Qed.

  Lemma step_if_1' e1 e1' e2 e3 :
    rtc step e1 e1' -> rtc step (If e1 e2 e3) (If e1' e2 e3).
  Proof. induction 1; eauto using rtc_refl, rtc_l, step. Qed.

  (* Syntactic type soundness *)
  Definition ctx_equiv (A B : Ctx) : Prop := ∀ x, lookup A x = lookup B x.
  Hint Unfold ctx_equiv : core.
  Global Instance ctx_equiv_equiv : Equivalence ctx_equiv.
  Proof.
    constructor; eauto.
    intros A B C. unfold ctx_equiv. intros. congruence.
  Qed.

  Lemma typed_in_equiv_contexts A B e t :
    ctx_equiv A B -> typed A e t -> typed B e t.
  Proof.
    intros.
    revert B H.
    induction H0; intros; simplify_eq; simpl in *; eauto using typed;
      constructor; first (specialize (H0 x); congruence);
      apply IHtyped; intro; simp_lookup.
  Qed.

  Lemma subst_typed Γ Γ' e t x v t_x :
    typed Γ' e t ->
    ctx_equiv Γ' ((x,t_x)::Γ) -> typed [] v t_x -> typed Γ (subst x v e) t.
  Proof.
    intro. revert Γ.
    induction H; intros; subst; simpl in *; try solve [eauto using typed].
    - specialize (H0 x0); simpl in *.
      simp_lookup; eauto using weaken_typed'.
      constructor; congruence.
    - case_decide; simplify_eq.
      + constructor.
        eapply typed_in_equiv_contexts; last eassumption.
        intro x'; specialize (H0 x'); simp_lookup.
      + constructor.
        eapply IHtyped; eauto.
        intro x'; specialize (H0 x'); simp_lookup.
    - case_decide; simplify_eq; constructor.
      + destruct H2; simplify_eq;
          eapply typed_in_equiv_contexts; try eassumption;
          intro x'; specialize (H0 x'); simp_lookup.
      + assert (x0 <> x) by eauto.
        assert (f <> x) by eauto.
        apply IHtyped; eauto; intro x'; specialize (H0 x'); simp_lookup.
  Qed.

  Lemma preservation e e' ty :
    step e e' -> typed [] e ty -> typed [] e' ty.
  Proof.
    intro.
    revert ty.
    induction H; intros ty Htyped; inv Htyped; eauto using typed.
    - inv H3.
      eapply subst_typed; eauto.
    - inv H3.
      destruct (decide (x = f)).
      + subst.
        eapply subst_typed; eauto using typed.
        eapply weaken_typed'; eapply subst_typed; eauto.
        intro x'; simp_lookup.
      + eapply subst_typed; eauto using typed.
        eapply subst_typed; eauto.
  Qed.

  Lemma preservation_steps e e' ty :
    rtc step e e' -> typed [] e ty -> typed [] e' ty.
  Proof.
    induction 1; eauto using preservation.
  Qed.

  Lemma progress e ty :
    typed [] e ty -> is_value e \/ ∃ e', step e e'.
  Proof.
    intro H.
    remember [] as Γ.
    revert HeqΓ.
    induction H; intro; simplify_eq; simpl; eauto; right.
    - inv H; first (destruct b; eauto using step);
        destruct IHtyped1 as [|[]]; eauto; try contradiction;
        eauto using step.
    - inv H.
      1, 2: destruct IHtyped1 as [|[]]; eauto; try contradiction; eauto using step.
      all: destruct IHtyped2 as [|[]]; eauto using step;
        eexists; apply step_app_2; first constructor; eauto.
  Qed.

  Theorem syntactic_type_soundness e e' ty :
    typed [] e ty -> rtc step e e' -> is_value e' \/ ∃ e'', step e' e''.
  Proof.
    induction 2; eauto using progress, preservation.
  Qed.

  (* Type system in Set *)
  (* Why must I do this :( *)
  Fixpoint type_of Γ e : option ty :=
    match e with
    | Var x => lookup Γ x
    | Const b => Some Bool
    | If e1 e2 e3 =>
        match type_of Γ e1, type_of Γ e2, type_of Γ e3 with
        | Some Bool, Some t, Some t' => if decide (t = t') then Some t else None
        | _, _, _ => None
        end
    | App e1 e2 =>
        match type_of Γ e1, type_of Γ e2 with
        | Some (Fun a b), Some a' => if decide (a = a') then Some b else None
        | _, _ => None
        end
    | Lam x a body =>
        match type_of ((x,a)::Γ) body with
        | Some b => Some (Fun a b)
        | _ => None
        end
    | Fix f x a b body =>
        match type_of ((x,a)::(f,Fun a b)::Γ) body with
        | Some b' => if decide (b = b') then Some (Fun a b) else None
        | _ => None
        end
    end.

  Lemma typed_to_type_of Γ e t :
    typed Γ e t <-> type_of Γ e = Some t.
  Proof.
    split.
    - induction 1; simplify_eq; simpl; eauto.
      + rewrite IHtyped1, IHtyped2, IHtyped3. case_decide; congruence.
      + rewrite IHtyped1, IHtyped2. case_decide; congruence.
      + rewrite IHtyped. congruence.
      + rewrite IHtyped. case_decide; congruence.
    - revert Γ t; induction e; simpl; intros; simplify_eq; eauto using typed.
      + edestruct (type_of Γ e1) as [[]|] eqn:?, (type_of Γ e2) eqn:?, (type_of Γ e3) eqn:?;
          simpl in *; try congruence.
        case_decide; simplify_eq; eauto using typed.
      + edestruct (type_of Γ e1) as [[]|] eqn:?, (type_of Γ e2) eqn:?;
          simpl in *; try congruence.
        case_decide; simplify_eq; eauto using typed.
      + edestruct type_of eqn:?; simplify_eq; eauto using typed.
      + edestruct type_of eqn:?; simplify_eq; case_decide; simplify_eq; eauto using typed.
  Qed.

  Corollary types_are_unique {Γ e t t'} : typed Γ e t -> typed Γ e t' -> t = t'.
  Proof.
    intros.
    rewrite typed_to_type_of in *.
    congruence.
  Qed.

  Inductive typed' : Ctx -> exp -> ty -> Set :=
  | t_var' {Γ} x {ty} : lookup Γ x = Some ty -> typed' Γ (Var x) ty
  | t_const' {Γ} b : typed' Γ (Const b) Bool
  | t_if' {Γ e1 e2 e3 ty} :
      typed' Γ e1 Bool ->
      typed' Γ e2 ty ->
      typed' Γ e3 ty ->
      typed' Γ (If e1 e2 e3) ty
  | t_app' {Γ e1 e2 t1 t2} :
      typed' Γ e1 (Fun t1 t2) ->
      typed' Γ e2 t1 ->
      typed' Γ (App e1 e2) t2
  | t_lam' {Γ} x {body t1 t2} :
      typed' ((x, t1) :: Γ) body t2 ->
      typed' Γ (Lam x t1 body) (Fun t1 t2)
  | t_fix' {Γ} f x {body t1 t2} :
      typed' ((x, t1) :: (f, Fun t1 t2) :: Γ) body t2 ->
      typed' Γ (Fix f x t1 t2 body) (Fun t1 t2).

  Definition typed_to_typed' {Γ e t} : typed Γ e t -> typed' Γ e t.
  Proof.
    revert Γ t. induction e; intros.
    - constructor. inv H; eauto.
    - assert (t = Bool) by (inv H; eauto).
      subst.
      constructor.
    - constructor.
      + apply IHe1. inv H; eauto.
      + apply IHe2. inv H; eauto.
      + apply IHe3. inv H; eauto.
    - apply typed_to_type_of in H.
      simpl in H.
      destruct (type_of Γ e1) as [[]|] eqn:?, (type_of Γ e2) eqn:?; simpl in *; try congruence.
      case_decide; simplify_eq.
      apply typed_to_type_of in Heqo, Heqo0.
      eauto using typed'.
    - apply typed_to_type_of in H.
      simpl in H.
      destruct type_of eqn:?; simplify_eq.
      apply typed_to_type_of in Heqo.
      eauto using typed'.
    - assert (t = Fun a b) by (inv H; congruence).
      subst.
      constructor.
      apply IHe.
      inv H; eauto.
  Defined.

  Theorem typed'_to_typed {Γ e t} : typed' Γ e t -> typed Γ e t.
  Proof.
    revert Γ t. induction 1; intros; eauto using typed.
  Qed.

  Hint Resolve typed_to_typed' : core.
  Hint Resolve typed'_to_typed : core.

  Corollary types_are_unique' {Γ e t t'} :
    typed' Γ e t -> typed' Γ e t' -> t = t'.
  Proof.
    eauto using types_are_unique.
  Qed.

  Theorem typed'_unique {Γ e t} (pf pf' : typed' Γ e t) : pf = pf'.
  Proof.
    revert pf'.
    induction pf; intros; simplify_eq; dependent destruction pf'; f_equal; eauto.
    - apply UIP.
    - assert (t0 = t1) by eauto using types_are_unique'.
      subst.
      congruence.
  Qed.

End Lang.

Module Domains.
  (* Finite domain theory: domains, maps, combinators, oh my *)

  (* Finite partial orders with decidable order *)
  Record poset : Type := {
      carrier :> Set;
      poset_deceq :: EqDecision carrier;
      poset_finite :: Finite carrier;

      le : carrier -> carrier -> Prop;
      dec_le :: ∀ x y, Decision (le x y);

      le_refl : ∀ x, le x x;
      le_trans : ∀ x y z, le x y -> le y z -> le x z;
      le_antisym : ∀ x y, le x y -> le y x -> x = y;
    }.
  Notation "x ≤ y" := (le _ x y).

  Class pointed (A : poset) := {
      bot : A;
      bot_le : ∀ x, bot ≤ x;
    }.
  Notation "⊥" := bot.

  Global Instance poset_preorder (A : poset) : PreOrder (le A).
  Proof.
    constructor.
    - intro. apply le_refl.
    - intros ???. apply le_trans.
  Qed.
  Hint Resolve le_refl bot_le : core.

  Lemma le_bot_eq_bot `{pointed A} (x : A) : x ≤ ⊥ -> x = ⊥.
  Proof.
    eauto using le_antisym.
  Qed.
  Hint Resolve le_bot_eq_bot : core.

  Obligation Tactic := (simpl; eauto).

  (* Maps *)
  Definition monotone {A B : poset} (f : A -> B) : Prop :=
    forall x y, x ≤ y -> f x ≤ f y.
  Hint Unfold monotone : core.

  Definition map_le {A B : poset} (f g : A → B) : Prop :=
    ∀ x, f x ≤ g x.
  Hint Unfold map_le : core.
  Program Definition Map (A B : poset) : poset :=
    {|
      carrier := { f : (A -> B) | monotone f };
      le := fun x y => map_le x y;
    |}.
  Next Obligation.
    eauto using le_trans.
  Qed.
  Next Obligation.
    intros P Q f g ??.
    apply sig_eq.
    extensionality x.
    auto using le_antisym.
  Qed.

  Definition proj_map {A B} : Map A B -> (A -> B) := proj1_sig.
  Coercion proj_map : carrier >-> Funclass.
  Hint Unfold proj_map : core.

  Global Program Instance map_pointed {A B} (_ : pointed B) : pointed (Map A B) := {
      bot := fun _ => ⊥
    }.

  Class ppomap `{pointed A} `{pointed B} (f : Map A B) : Prop :=
    { strict : f ⊥ = ⊥ }.
  Global Instance decide_ppomap `{pointed A} `{pointed B} (f : Map A B) :
    Decision (ppomap f).
  Proof.
    destruct (decide (f ⊥ = ⊥)).
    - left. constructor. eauto.
    - right. intros []. contradiction.
  Qed.

  Program Definition id_map {A} : Map A A :=
    fun x => x.
  Global Instance pointed_id `{pointed A} : ppomap id_map.
  Proof.
    constructor.
    eauto.
  Qed.

  Program Definition compose_map {A B C} : Map (Map B C) (Map (Map A B) (Map A C)) :=
    fun f g x => f (g x).
  Next Obligation.
    intros ???[f][g].
    eauto.
  Qed.
  Next Obligation.
    intros ???[f][g][g'].
    simpl.
    eauto.
  Qed.
  Next Obligation.
    intros ???[f][f']?[g].
    simpl.
    eauto.
  Qed.
  Global Instance pointed_compose `{pointed A} `{pointed B} `{pointed C} (f : Map B C) (g : Map A B) :
    ppomap f -> ppomap g -> ppomap (compose_map f g).
  Proof.
    constructor.
    simpl.
    rewrite strict.
    rewrite strict.
    reflexivity.
  Qed.

  Lemma app_monotone {A B} (f g : Map A B) (x y : A) :
    f ≤ g -> x ≤ y -> f x ≤ g y.
  Proof.
    intros.
    destruct f as [f], g as [g]. simpl.
    transitivity (f y); eauto.
  Qed.
  Hint Resolve app_monotone : core.

  (* that's right it's K *)
  Program Definition const_map {A B} : Map A (Map B A) :=
    fun x y => x.
  Next Obligation.
    unfold monotone.
    simpl.
    eauto.
  Qed.

  (* that's right it's S *)
  Program Definition apply_map {A B C} : Map (Map A (Map B C)) (Map (Map A B) (Map A C)) :=
    fun f g x => f x (g x).
  Next Obligation.
    intros ??? [f] [g] [g'] ??.
    unfold monotone in *. simpl.
    eauto.
  Qed.
  Next Obligation.
    intros ???[f][f']?[g]?.
    unfold monotone in *. simpl.
    eauto.
  Qed.

  (* Flat order *)
  Program Definition Flat (A : Set) `{Finite A} : poset :=
    {|
      carrier := A;
      le := fun x y => x = y;
    |}.
  Next Obligation.
    intros.
    congruence.
  Qed.

  Program Definition map_from_flat {A:Set} `{Finite A} {B : poset} (f : A -> B) : Map (Flat A) B :=
    fun x => f x.
  Next Obligation.
    unfold monotone; simpl; intros; subst; eauto.
  Qed.

  (* Sub-posets *)
  Program Definition subset (A : poset) (P : A -> Prop) `{∀ x, Decision (P x)} : poset :=
    {|
      carrier := {x:A | P x};
      le := fun x y => `x ≤ `y;
    |}.
  Next Obligation.
    eauto using le_trans.
  Qed.
  Next Obligation.
    intros.
    apply sig_eq.
    auto using le_antisym.
  Qed.
  Global Program Instance subset_pointed {A P} `{pointed A} `{∀ x, Decision (P x)} (pf : P ⊥) : pointed (subset A P) :=
    { bot := (⊥ : A) }.

  Program Definition subset_inj {A:poset} `{∀ x, Decision (P x)} : Map (subset A P) A :=
    proj1_sig.

  (* Strict map space between ppos *)
  Definition SMap A B `{pointed A} `{pointed B} :=
    subset (Map A B) ppomap.

  Global Instance ppomap_bot `{pointed A} `{pointed B} : ppomap (⊥ : Map A B).
  Proof.
    constructor.
    eauto.
  Qed.

  (* Empty poset *)
  Program Definition Empty_poset : poset :=
    {|
      carrier := Empty_set;
      le := fun _ _ => True;
    |}.
  Next Obligation.
    intros [].
  Qed.

  Unset Program Cases.
  Program Definition absurd_map {A} : Map Empty_poset A :=
    fun x => match x with end.
  Next Obligation.
    intros ?[].
  Qed.

  Lemma absurd_unique {A} (f g : Map Empty_poset A) : f = g.
  Proof.
    apply sig_eq.
    extensionality x.
    destruct x.
  Qed.

  (* Unit poset *)
  Program Definition Unit_poset : poset :=
    {|
      carrier := unit;
      le := fun _ _ => True;
    |}.
  Next Obligation.
    intros. apply unit_unique.
  Qed.

  Program Definition unit_map {A} : Map A Unit_poset :=
    fun _ => ().

  Lemma unit_map_unique {A} (f g : Map A Unit_poset) : f = g.
  Proof.
    apply sig_eq.
    extensionality x.
    apply unit_unique.
  Qed.

  (* prod P Q is the (categorical) product of A and B *)
  Program Definition prod (A B : poset) : poset :=
    {|
      carrier := (A * B)%type;
      le := fun p1 p2 => fst p1 ≤ fst p2 /\ snd p1 ≤ snd p2;
    |}.
  Next Obligation.
    intros ?????[][].
    eauto using le_trans.
  Qed.
  Next Obligation.
    intros ?? [] [] [] [].
    simpl in *.
    f_equal; auto using le_antisym.
  Qed.
  Global Program Instance prod_pointed `{pointed A} `{pointed B} : pointed (prod A B) :=
    { bot := (⊥, ⊥) }.

  Program Definition fst_prod {A B} : Map (prod A B) A :=
    fun p => fst p.
  Next Obligation.
    unfold monotone.
    intros ??[][][]; eauto.
  Qed.
  Global Instance fst_prod_strict `{pointed A} `{pointed B} : ppomap (@fst_prod A B).
  Proof.
    constructor.
    eauto.
  Qed.

  Program Definition snd_prod {A B} : Map (prod A B) B :=
    fun p => snd p.
  Next Obligation.
    unfold monotone.
    intros ??[][][]; eauto.
  Qed.
  Global Instance snd_prod_strict `{pointed A} `{pointed B} : ppomap (@snd_prod A B).
  Proof.
    constructor.
    eauto.
  Qed.

  Lemma prod_maps {X A B : poset} (f : X -> A) (g : X -> B) :
    monotone f /\ monotone g <-> monotone (B := prod A B) (fun x => (f x, g x)).
  Proof.
    unfold monotone.
    simpl.
    split.
    - intros []. eauto.
    - intro H. split; intros; edestruct H; eauto.
  Qed.

  Program Definition pair {X A B : poset} (f : Map X A) (g : Map X B) : Map X (prod A B) :=
    fun x => (f x, g x).
  Next Obligation.
    intros ???[][].
    apply prod_maps.
    eauto.
  Qed.
  Global Instance pair_strict `{pointed X} `{pointed A} `{pointed B} (f : Map X A) (g : Map X B) :
    ppomap f -> ppomap g -> ppomap (pair f g).
  Proof.
    intros [][].
    constructor.
    simpl.
    congruence.
  Qed.

  Program Definition pair' {A B} : Map A (Map B (prod A B)) :=
    fun x y => (x, y).
  Next Obligation.
    unfold monotone. simpl. eauto.
  Qed.
  Next Obligation.
    unfold monotone. simpl.
    unfold map_le. simpl.
    eauto.
  Qed.

  (* Cartesian closure *)
  Program Definition curry {A B C : poset} : Map (Map (prod A B) C) (Map A (Map B C)) :=
    fun f =>
      compose_map (compose_map f) pair'.
  Next Obligation.
    intros ???[f][f']???.
    simpl.
    eauto.
  Qed.

  Program Definition uncurry {A B C : poset} : Map (Map A (Map B C)) (Map (prod A B) C) :=
    fun f =>
      apply_map (compose_map f fst_prod) snd_prod.
  Next Obligation.
    intros ???[f][f']??.
    simpl.
    eauto.
  Qed.

  Lemma curry_uncurry {A B C} : compose_map (@curry A B C) uncurry = id_map.
  Proof.
    apply sig_eq.
    extensionality f.
    destruct f as [f].
    apply sig_eq.
    extensionality x.
    apply sig_eq.
    extensionality y.
    reflexivity.
  Qed.

  Lemma uncurry_curry {A B C} : compose_map (@uncurry A B C) curry = id_map.
  Proof.
    apply sig_eq.
    extensionality f.
    destruct f as [f].
    apply sig_eq.
    extensionality p.
    destruct p as [x y].
    reflexivity.
  Qed.

  (* Freely adjoint a basepoint *)
  Definition lift_le {A : poset} (x y : option A) : Prop :=
    match x, y with
    | None, _ => True
    | Some _, None => False
    | Some x, Some y => x ≤ y
    end.
  Global Instance lift_le_dec {A : poset} `{EqDecision A} (x y : option A) :
    Decision (lift_le x y).
  Proof.
    unfold lift_le.
    destruct x, y; exact _.
  Defined.

  Program Definition Lift (A : poset) : poset :=
    {|
      carrier := option A;
      le := lift_le;
    |}.
  Next Obligation.
    intros; destruct x; simpl; auto.
  Qed.
  Next Obligation.
    intros; destruct x, y, z; simpl in *; auto; try contradiction.
    eauto using le_trans.
  Qed.
  Next Obligation.
    intros ? [] [] ? ?; simpl in *; try contradiction; f_equal.
    eauto using le_antisym.
  Qed.
  Global Program Instance pointed_Lift {A} : pointed (Lift A) :=
    { bot := None }.

  Program Definition lift_inj {A} : Map A (Lift A) :=
    fun x => Some x.

  Definition lift_bind {A} `{pointed B} :
    Map (Map A B) (Map (Lift A) B).
  Proof.
    unshelve refine (exist _ (fun f : Map A B => exist _ (fun x => match x with None => ⊥ | Some x' => f x' end) _) _).
    - unfold monotone.
      intros [] []; eauto.
      simpl. intros [].
    - unfold monotone.
      intros [f][g] ? []; simpl; eauto.
  Defined.

  Definition lift_bind' {X A : poset} `{pointed B} (f : Map (prod X A) B) : Map X (Map (Lift A) B) :=
    compose_map lift_bind (curry f).

  Definition lift_bind'' {X A : poset} `{pointed B} (x : Map X (Lift A)) (f : Map (prod X A) B) : Map X B :=
    apply_map (lift_bind' f) x.

  (* Fixed points *)
  Function lfp_at_least {A} (f : Map A A) (min : A) (pf : min ≤ f min)
    { measure (fun min => card {x : A | min ≤ x }) min } :=
    if decide (f min = min) then min else lfp_at_least f (f min) ltac:(eauto).
  Proof.
    intros.
    unfold card.
    destruct f as [f H].
    simpl in *.
    apply list_filter_sig_lengths_lt.
    - eauto using le_trans.
    - exists min. split; eauto using elem_of_enum, le_antisym.
  Qed.
  Arguments lfp_at_least {A} f min pf : rename.

  Lemma lfp_at_least_is_fixpoint {A} (f : Map A A) min pf :
    f (lfp_at_least f min pf) = lfp_at_least f min pf.
  Proof.
    functional induction (lfp_at_least f min pf); eauto.
  Qed.

  (* in fact, it's the least x such that f x ≤ x *)
  Lemma lfp_at_least_is_least {A} (f : Map A A) min pf :
    ∀ x, min ≤ x -> f x ≤ x -> lfp_at_least f min pf ≤ x.
  Proof.
    functional induction (lfp_at_least f min pf); eauto.
    intros.
    apply IHc; eauto.
    eauto using le_trans.
  Qed.

  Definition lfp `{pointed A} : Map A A -> A :=
    fun f => lfp_at_least f ⊥ (bot_le _).

  Lemma lfp_is_fixpoint `{pointed A} (f : Map A A) :
    f (lfp f) = lfp f.
  Proof.
    apply lfp_at_least_is_fixpoint.
  Qed.

  Lemma lfp_is_least `{pointed A} (f : Map A A) :
    ∀ x, f x ≤ x -> lfp f ≤ x.
  Proof.
    intros.
    apply lfp_at_least_is_least; eauto.
  Qed.

  Lemma fixpoint_induction `{pointed A} (P : A -> Prop) (f : Map A A) :
    P ⊥ -> (∀ x, P x -> P (f x)) -> P (lfp f).
  Proof.
    unfold lfp.
    generalize ⊥ (bot_le (f ⊥)).
    intros ??.
    functional induction (lfp_at_least f c l); eauto.
  Qed.

  Program Definition lfp_map `{pointed A} : Map (Map A A) A := lfp.
  Next Obligation.
    unfold lfp.
    intros ?? f f' ?.
    simpl in H0; unfold map_le in H0.
    apply lfp_at_least_is_least; eauto.
    rewrite <-(lfp_at_least_is_fixpoint f') at 2.
    eauto.
  Qed.

End Domains.

Module Semantics.
  (* Denotational semantics for finitary PCF *)

  Import Domains.

  Fixpoint denot (t : ty) : poset :=
    match t with
    | Bool => Flat bool
    | Fun a b => Map (denot a) (Lift (denot b))
    end.

  Fixpoint denot_ctx (Γ : Ctx) : poset :=
    match Γ with
    | [] => Unit_poset
    | (x,t)::Γ' => prod (denot_ctx Γ') (denot t)
    end.

  Definition lookup_var {Γ t} (x : string) (pf : lookup Γ x = Some t) :
    Map (denot_ctx Γ) (denot t).
  Proof.
    induction Γ as [|[x' t']]; simpl in *; try discriminate.
    case_decide.
    - assert (t' = t) as -> by congruence.
      exact snd_prod.
    - exact (compose_map (IHΓ pf) fst_prod).
  Defined.

  Ltac simp_lookup :=
    simpl lookup in *; simplify_eq; repeat (case_decide; simplify_eq; eauto).

  Lemma lookup_var_here {Γ t} (x : string) (pf : lookup ((x,t)::Γ) x = Some t) env v :
    lookup_var x pf (env, v) = v.
  Proof.
    simpl.
    simp_lookup.
    assert (pf = eq_refl) by apply UIP.
    subst.
    reflexivity.
  Qed.

  Lemma lookup_var_there {Γ t t'} (x x' : string) (pf : lookup ((x',t')::Γ) x = Some t) (pf' : lookup Γ x = Some t) env v :
    x <> x' -> lookup_var x pf (env,v) = lookup_var x pf' env.
  Proof.
    intros.
    simpl.
    simp_lookup.
    simpl.
    assert (pf = pf') by apply UIP.
    subst.
    reflexivity.
  Qed.

  Strategy opaque [lookup_var].

  Definition lift_curry {A B C} (f : Map (prod A B) C) : Map A (Lift (Map B C)) :=
    compose_map lift_inj (curry f).

  Unset Program Cases.
  Program Definition if_map {X A} (f g : Map X A) : Map (prod X (Flat bool)) A :=
    fun '(x, b) => if b then f x else g x.
  Next Obligation.
    intros ??[f][g][][][].
    simpl in *.
    subst.
    destruct c2; eauto.
  Qed.

  Definition weaken {A B C} (f : Map A C) : Map (prod A B) C :=
    compose_map f fst_prod.
  Definition var {A B} : Map (prod A B) B := snd_prod.

  Definition curry2 {Γ A B C} (f : Map (prod (prod Γ A) B) C) : Map Γ (Map A (Map B C)) :=
    curry (curry f).

  Lemma curry2_apply {Γ A B C} (f : Map (prod (prod Γ A) B) C) env x y :
    curry2 f env x y = f (env, x, y).
  Proof.
    reflexivity.
  Qed.

  Strategy opaque [curry2].

  Lemma lfp_curry2_unfold {Γ A} `{pointed B} (f : Map (prod (prod Γ (Map A B)) A) B) env arg :
    lfp (curry2 f env) arg = f (env, lfp (curry2 f env), arg).
  Proof.
    rewrite <-lfp_is_fixpoint at 1.
    rewrite curry2_apply.
    reflexivity.
  Qed.

  (* The denotational semantics *)
  Fixpoint eval {Γ e t} (pf : typed' Γ e t) : Map (denot_ctx Γ) (Lift (denot t)) :=
    match pf in typed' Γ e t return Map (denot_ctx Γ) (Lift (denot t)) with
    | t_var' x pf => compose_map lift_inj (lookup_var x pf)
    | t_const' b => compose_map lift_inj (const_map (b : Flat bool))
    | t_if' e1 e2 e3 => lift_bind'' (eval e1) (if_map (eval e2) (eval e3))
    | t_app' e1 e2 =>
        lift_bind'' (eval e1)
          (lift_bind'' (weaken (eval e2))
             (apply_map (weaken var) var))
    | t_lam' x body => lift_curry (eval body)
    | t_fix' f x body =>
        compose_map lift_inj
          (compose_map lfp_map (curry2 (eval body)))
    end.

  (* Soundness! *)
  (* Parallel substitution *)
  Fixpoint subst' (sub : string -> exp) e :=
    match e with
    | Var x => sub x
    | Const b => Const b
    | If e1 e2 e3 => If (subst' sub e1) (subst' sub e2) (subst' sub e3)
    | App e1 e2 => App (subst' sub e1) (subst' sub e2)
    | Lam x a body => Lam x a (subst' (fun x' => if decide (x = x') then x' else sub x') body)
    | Fix f x a b body =>
        Fix f x a b (subst' (fun x' => if decide (f = x') then x' else if decide (x = x') then x' else sub x') body)
    end.

  Hint Resolve typed_to_typed' : core.
  Hint Resolve typed'_to_typed : core.

  Lemma subst'_id e sub :
    (∀ x, sub x = Var x) -> subst' sub e = e.
  Proof.
    revert sub; induction e; simpl; intros; f_equal; eauto; apply IHe;
      intro; repeat case_decide; eauto.
  Qed.

  Fixpoint only_has_vars xs e :=
    match e with
    | Var x => x ∈ xs
    | Const _ => True
    | If e1 e2 e3 => only_has_vars xs e1 /\ only_has_vars xs e2 /\ only_has_vars xs e3
    | App e1 e2 => only_has_vars xs e1 /\ only_has_vars xs e2
    | Lam x _ e1 => only_has_vars (x::xs) e1
    | Fix f x _ _ e1 => only_has_vars (x::f::xs) e1
    end.
  Definition closed e := only_has_vars [] e.

  Lemma only_has_vars_weaken A B x e : only_has_vars (B++A) e -> only_has_vars (B++[x]++A) e.
  Proof.
    revert B; induction e; simpl; intros; try set_solver.
    - apply (IHe (_::B)); eauto.
    - apply (IHe (_::_::B)); eauto.
  Qed.
  Lemma only_has_vars_contract A B x e : only_has_vars (B++[x;x]++A) e -> only_has_vars (B++[x]++A) e.
  Proof.
    revert B; induction e; simpl; intros; try set_solver.
    - apply (IHe (_::B)); eauto.
    - apply (IHe (_::_::B)); eauto.
  Qed.
  Lemma only_has_vars_exchange A B x y e : only_has_vars (B++[x;y]++A) e -> only_has_vars (B++[y;x]++A) e.
  Proof.
    revert B; induction e; simpl; intros; try set_solver.
    - apply (IHe (_::B)); eauto.
    - apply (IHe (_::_::B)); eauto.
  Qed.

  Lemma typed_to_only_has_vars Γ e t : typed Γ e t -> only_has_vars (map fst Γ) e.
  Proof.
    induction 1; simpl; eauto.
    induction Γ as [|[]]; simpl in *; set_unfold; simp_lookup.
  Qed.

  Lemma typed_to_closed e t : typed [] e t -> closed e.
  Proof.
    apply (typed_to_only_has_vars []).
  Qed.

  Lemma subst'_only_has_vars xs e sub sub' :
    only_has_vars xs e -> (forall x, x ∈ xs -> sub x = sub' x) -> subst' sub e = subst' sub' e.
  Proof.
    intro.
    revert xs sub sub' H.
    induction e; simpl; intros; repeat split_and; f_equal; eauto; try set_solver.
    - eapply IHe; eauto.
      intros.
      set_unfold.
      destruct H1; case_decide; simplify_eq; eauto.
    - eapply IHe; eauto.
      intros.
      set_unfold.
      destruct H1 as [|[]]; repeat case_decide; simplify_eq; eauto.
  Qed.

  Lemma subst'_closed sub e : closed e -> subst' sub e = e.
  Proof.
    intros.
    rewrite (subst'_only_has_vars [] e sub Var); eauto; try set_solver.
    apply subst'_id; eauto.
  Qed.

  Lemma subst'_subst x v e :
    subst x v e = subst' (fun x' => if decide (x = x') then v else x') e.
  Proof.
    induction e; simpl; simp_lookup; f_equal; eauto.
    - rewrite subst'_id; eauto; intros; simp_lookup.
    - rewrite IHe. f_equal.
      extensionality x'.
      simp_lookup.
    - rewrite subst'_id; eauto; intros; simp_lookup.
      destruct H; congruence.
    - assert (x0 <> x) by eauto.
      assert (f <> x) by eauto.
      rewrite IHe. f_equal.
      extensionality x'.
      simp_lookup.
  Qed.

  Lemma subst_closed x v e : closed e -> subst x v e = e.
  Proof.
    rewrite subst'_subst.
    apply subst'_closed.
  Qed.

  Lemma subst_equiv xs sub sub' e :
    only_has_vars xs e -> (∀ x, x ∈ xs -> sub x = sub' x) -> subst' sub e = subst' sub' e.
  Proof.
    revert xs sub sub'. induction e; simpl; intros; f_equal;
      repeat match goal with H : _ /\ _ |- _ => destruct H end; eauto.
    - apply (IHe (x::xs)); eauto.
      intro. set_unfold. intros []; simp_lookup.
    - apply (IHe (x::f::xs)); eauto.
      intro. set_unfold. intros [?|[]]; simp_lookup.
  Qed.

  Lemma subst_compose' A B x v sub e :
    sub x = Var x ->
    only_has_vars (B ++ x :: A) e ->
    (∀ x', x' ∈ B -> sub x' = x') ->
    (∀ x', x' ∈ A -> ~ (x' ∈ B) -> x' <> x -> closed (sub x')) ->
    subst x v (subst' sub e) = subst' (fun x' => subst x v (sub x')) e.
  Proof.
    revert sub B.
    induction e; simpl; intros; eauto.
    - destruct H0 as [?[]]. f_equal; eauto.
    - destruct H0. f_equal; eauto.
    - case_decide; f_equal.
      + subst.
        eapply subst_equiv; eauto.
        intro. destruct (decide (x0 ∈ (x :: B))); set_unfold.
        * destruct e0; intros [|[|[]]]; subst; simp_lookup;
            rewrite H1; eauto; simpl; simp_lookup.
        * assert (x0 <> x) by eauto.
          assert (~ (x0 ∈ B)) by eauto.
          intros [|[|[]]]; simplify_eq; simp_lookup.
          symmetry; apply subst_closed; eauto.
      + rewrite (IHe _ (x0::B)).
        * eapply subst_equiv; eauto.
          intros. simp_lookup. simpl. simp_lookup.
        * simp_lookup.
        * eauto.
        * intros. simp_lookup. set_solver.
        * intros. case_decide; set_solver.
    - case_decide; f_equal.
      + eapply subst_equiv; eauto.
        intros. simp_lookup.
        assert (x1 ∈ B \/ (x1 ∈ A /\ ~ (x1 ∈ B) /\ x1 <> x)).
        { destruct (decide (x1 ∈ B)); eauto; right; set_solver. }
        destruct H7 as [|[?[]]].
        * rewrite H1; eauto; simpl; destruct H3; simp_lookup.
        * symmetry; apply subst_closed; apply H2; eauto.
      + assert (x0 <> x) by eauto.
        assert (f <> x) by eauto.
        rewrite (IHe _ (x0::f::B)).
        * eapply subst_equiv; eauto.
          intros. simp_lookup; simpl; simp_lookup.
        * simp_lookup.
        * eauto.
        * intros. simp_lookup. set_solver.
        * intros. simp_lookup; set_solver.
  Qed.

  Lemma subst_compose A x v sub e :
    sub x = Var x ->
    only_has_vars (x :: A) e ->
    (∀ x', x' ∈ A -> x' <> x -> closed (sub x')) ->
    subst x v (subst' sub e) = subst' (fun x' => subst x v (sub x')) e.
  Proof.
    intros.
    apply (subst_compose' A []); eauto; set_solver.
  Qed.

  (* typed_sub sub A B means that B |- sub : B;A is a weakening of |- sub : A *)
  Definition typed_sub (sub : string -> exp) (A B : Ctx) :=
    (forall x t, lookup B x = Some t -> sub x = Var x) /\
      (forall x t, lookup B x = None -> lookup A x = Some t -> typed [] (sub x) t).

  Lemma lookup_append {A} x t (xs ys : list (string * A)) :
    lookup (xs ++ ys) x = Some t ->
      lookup xs x = Some t \/ (lookup xs x = None /\ lookup ys x = Some t).
  Proof.
    induction xs as [|[]]; intros; eauto; simp_lookup.
  Qed.

  Lemma in_vars_to_lookup (Γ : Ctx) x : x ∈ map fst Γ -> exists t, lookup Γ x = Some t.
  Proof.
    induction Γ as [|[]]; simpl; set_unfold; intros []; simp_lookup.
  Qed.

  Lemma subst'_typed A B sub e t :
    typed_sub sub A B ->
    typed (B++A) e t -> typed B (subst' sub e) t.
  Proof.
    intros [] ?.
    remember (B ++ A) as ctx'.
    revert sub A B Heqctx' H H0.
    induction H1; intros; simplify_eq; simpl in *; eauto using typed.
    - edestruct (lookup_append x ty0 B A) as [|[]]; eauto using weaken_typed'.
      erewrite H0 by eassumption.
      eauto using typed.
    - constructor; eapply IHtyped; eauto; intros; simp_lookup.
    - constructor; eapply IHtyped; eauto; intros; simp_lookup.
  Qed.

  Fixpoint cat_env {A B} (e1 : denot_ctx A) : denot_ctx B -> denot_ctx (B ++ A) :=
    match B return denot_ctx B -> denot_ctx (B ++ A) with
    | [] => fun _ => e1
    | (x,t)::B' => fun '(e2, v) => (cat_env e1 e2, v)
    end.

  Lemma cat_env_lookup {A B} x t (pf : lookup B x = Some t) (pf' : lookup (B++A) x = Some t) env env' :
    lookup_var x pf env = lookup_var x pf' (cat_env env' env).
  Proof.
    revert pf pf' env env'.
    induction B as [|[]]; simpl; intros; simplify_eq.
    destruct env as [env v].
    destruct (decide (s = x)); subst.
    - assert (t0 = t) by simp_lookup; subst.
      rewrite (lookup_var_here x pf).
      rewrite (lookup_var_here x pf').
      reflexivity.
    - unshelve erewrite (lookup_var_there x s pf); simp_lookup.
      unshelve erewrite (lookup_var_there x s pf'); simp_lookup.
  Qed.

  Lemma cat_env_lookup' {A B} x t (pf : lookup A x = Some t) (pf' : lookup (B++A) x = Some t) env env' :
    lookup B x = None -> lookup_var x pf env' = lookup_var x pf' (cat_env env' env).
  Proof.
    revert pf pf' env env'.
    induction B as [|[]]; simpl; intros; simplify_eq.
    { assert (pf = pf') by apply UIP.
      subst. reflexivity. }
    destruct env as [ env v ].
    destruct (decide (s = x)); first exfalso; simp_lookup.
    unshelve erewrite (lookup_var_there x s pf'); simp_lookup.
  Qed.

  Lemma eval_extend A B e t :
    forall Γ (Heq : Γ = B ++ A) (pf : typed' Γ e t) (pf' : typed' B e t) env env',
      eval (rew[ fun C => typed' C e t ] Heq in pf) (cat_env env' env) = eval pf' env.
  Proof.
    intros ???; revert A B Heq.
    induction pf; intros; simplify_eq; dependent destruction pf'.
    - simpl. f_equal.
      symmetry. apply cat_env_lookup.
    - simpl. f_equal.
    - simpl.
      specialize (IHpf1 _ _ eq_refl).
      specialize (IHpf2 _ _ eq_refl).
      specialize (IHpf3 _ _ eq_refl).
      simpl in IHpf1, IHpf2, IHpf3.
      erewrite IHpf1, IHpf2, IHpf3.
      reflexivity.
    - simpl.
      specialize (IHpf1 _ _ eq_refl).
      specialize (IHpf2 _ _ eq_refl).
      simpl in IHpf1, IHpf2.
      assert (typed' (Γ++A) e2 t0) by eauto using weaken_typed.
      assert (t0 = t1) by eauto using types_are_unique'.
      subst. clear H.
      erewrite IHpf1, IHpf2.
      reflexivity.
    - simpl. f_equal. apply sig_eq.
      simpl.
      extensionality arg.
      apply (IHpf A ((x,t1)::B) eq_refl pf' (env,arg) env').
    - unfold eq_rect.
      simpl. f_equal. f_equal.
      apply sig_eq.
      extensionality rec.
      apply sig_eq.
      extensionality arg.
      change (curry2 (eval pf) (cat_env env' env) rec arg = curry2 (eval pf') env rec arg).
      do 2 rewrite curry2_apply.
      apply (IHpf A ((x,t1)::(f,Fun t1 t2)::B) eq_refl pf' (env,rec,arg) env').
  Qed.

  Lemma eval_extend' A B e t :
    forall (pf : typed' (B++A) e t) (pf' : typed' B e t) env env',
      eval pf (cat_env env env') = eval pf' env'.
  Proof.
    intros.
    About eval_extend.
    apply (eval_extend A B e t (B++A) eq_refl).
  Qed.

  Lemma eval_extend'' Γ e t :
    forall (pf : typed' Γ e t) (pf' : typed' [] e t) env,
      eval pf env = eval pf' ().
  Proof.
    intros.
    apply (eval_extend' _ []).
  Qed.

  (* Implicitly, typed_sub A B, i.e. B |- sub : B;A is a weakening of |- sub : A *)
  (* and they're all values *)
  Definition env_is_eval_subst Γ A B sub (env : denot_ctx A) (Heq : Γ = B ++ A) :=
    forall x t (pf : lookup Γ x = Some t),
      lookup B x = None ->
        exists pf' : typed' [] (sub x) t,
          forall (env' : denot_ctx B),
          Some (lookup_var x (rew[fun ctx => _ = _] Heq in pf) (cat_env env env')) = eval pf' ().

  Lemma subst_eval A B Γ e t (pf : typed' Γ e t) :
    forall (Heq : Γ = B++A) env env' sub,
      typed_sub sub A B -> env_is_eval_subst Γ A B sub env Heq ->
      forall (pf' : typed' B (subst' sub e) t),
        eval (rew[fun ctx => typed' ctx e t] Heq in pf) (cat_env env env') = eval pf' env'.
  Proof.
    unfold env_is_eval_subst, typed_sub.
    revert B.
    induction pf; intros; simplify_eq.
    - destruct H.
      destruct (lookup_append _ _ _ _ e) as [|[]].
      + simpl in pf'. revert pf'.
        assert (sub x = x) by eauto.
        simpl.
        rewrite H3.
        intro.
        dependent destruction pf'.
        simpl.
        f_equal.
        symmetry.
        apply cat_env_lookup.
      + simpl in *.
        unshelve edestruct H0; eauto.
        rewrite H4.
        symmetry.
        apply eval_extend''.
    - dependent destruction pf'.
      reflexivity.
    - dependent destruction pf'.
      simpl in *.
      unshelve erewrite (IHpf1 _ eq_refl); eauto.
      simpl.
      repeat case_match; eauto.
      + apply (IHpf2 _ eq_refl); eauto.
      + apply (IHpf3 _ eq_refl); eauto.
    - dependent destruction pf'.
      simpl.
      assert (typed' Γ (subst' sub e2) t1) by eauto using subst'_typed.
      assert (t0 = t1) by eauto using types_are_unique'.
      subst. clear H1.
      unshelve erewrite (IHpf1 _ eq_refl); eauto.
      unshelve erewrite (IHpf2 _ eq_refl); eauto.
    - dependent destruction pf'.
      simpl.
      f_equal.
      apply sig_eq.
      simpl.
      extensionality arg.
      simpl in *.
      destruct H.
      apply (IHpf ((x,t1)::B) eq_refl env (env', arg)).
      + split; intros; simp_lookup.
      + simpl. intros.
        simp_lookup; first exfalso; simp_lookup.
        assert (lookup (B++A) x0 = Some t) by simp_lookup.
        assert (lookup B x0 = None) by simp_lookup.
        unshelve edestruct H0; eauto.
        exists x1.
        intros [].
        erewrite (lookup_var_there x0 x pf0).
        apply H6.
        congruence.
    - dependent destruction pf'.
      simpl.
      f_equal.
      f_equal.
      apply sig_eq.
      extensionality rec.
      apply sig_eq.
      extensionality arg.
      change (curry2 (eval pf) (cat_env env env') rec arg = curry2 (eval pf') env' rec arg).
      do 2 rewrite curry2_apply.
      destruct H.
      apply (IHpf ((x,t1)::(f,_)::B) eq_refl env (env', rec, arg)).
      + split; intros; simp_lookup.
      + simpl eq_rect.
        intros.
        assert (lookup (B ++ A) x0 = Some t) by simp_lookup.
        assert (lookup B x0 = None) by simp_lookup.
        unshelve edestruct (H0 x0 t); eauto.
        assert (typed' [] (if decide (f = x0) then x0 else
                             if decide (x = x0) then x0 else sub x0) t)
          by simp_lookup.
        exists H6.
        intros [[env'0 fv] xv].
        destruct (lookup_append x0 t ((x,t1)::(f,Fun t1 t2)::B) A) as [|[]]; eauto; try congruence.
        unshelve erewrite <-cat_env_lookup'; eauto.
        simp_lookup.
        assert (H6 = x1) by eauto using typed'_unique.
        subst.
        simpl eq_rect in *.
        specialize (H5 env'0).
        rewrite <-H5.
        f_equal.
        erewrite <-cat_env_lookup'; eauto.
  Qed.

  (* Like above but without the extra generalization over Γ = B++A, *)
  (* which was only needed for the induction hypothesis *)
  Definition env_is_eval_subst' A B sub (env : denot_ctx A) :=
    forall x t (pf : lookup (B++A) x = Some t),
      lookup B x = None ->
        exists pf' : typed' [] (sub x) t,
          forall (env' : denot_ctx B),
          Some (lookup_var x pf (cat_env env env')) = eval pf' ().

  Lemma subst_eval' A B {e t} (pf : typed' (B++A) e t) :
    forall env env' sub e',
      e' = subst' sub e ->
      typed_sub sub A B -> env_is_eval_subst' A B sub env ->
      forall (pf' : typed' B e' t),
        eval pf (cat_env env env') = eval pf' env'.
  Proof.
    intros ?????.
    subst.
    intros.
    apply (subst_eval A B (B++A) e t pf eq_refl); eauto.
  Qed.

  Lemma subst_eval_one {x t_x v d e t}
    (pf_v : typed' [] v t_x)
    (pf : typed' [(x,t_x)] e t)
    (pf' : typed' [] (subst x v e) t) :
      eval pf_v () = Some d ->
      eval pf ((), d) = eval pf' ().
  Proof.
    intro.
    eapply (subst_eval' [(x,t_x)] [] pf ((), d) ()
           (fun x' => if decide (x = x') then v else x')).
    - apply subst'_subst.
    - unfold typed_sub. split; intros; simpl in *; simplify_eq.
      simp_lookup.
    - unfold env_is_eval_subst'. intros.
      simpl. simp_lookup; last exfalso; simp_lookup.
      assert (t_x = t0) by simp_lookup. subst.
      exists pf_v.
      unshelve erewrite (lookup_var_here (Γ:=[]) x0 pf0); simp_lookup.
  Qed.

  Lemma subst_eval_two {x t_x v_x y t_y v_y d_x d_y e t}
    (pf_x : typed' [] v_x t_x)
    (pf_y : typed' [] v_y t_y)
    (pf : typed' [(x,t_x);(y,t_y)] e t)
    (pf' : typed' [] (subst y v_y (subst x v_x e)) t) :
      eval pf_x () = Some d_x ->
      eval pf_y () = Some d_y ->
      eval pf ((), d_y, d_x) = eval pf' ().
  Proof.
    intros.
    eapply (subst_eval' [(x,t_x);(y,t_y)] [] pf ((),d_y,d_x) ()
              (fun x' => if decide (x = x') then v_x else if decide (y = x') then v_y else x')).
    - destruct (decide (y = x)); subst.
      + do 2 rewrite subst'_subst.
        rewrite subst'_closed; first (f_equal; extensionality x'; simp_lookup).
        eapply typed_to_closed.
        apply (subst'_typed [(x,t_x)] []). { split; intros; simp_lookup. }
        eapply typed_in_equiv_contexts; eauto.
        intro; simp_lookup.
      + rewrite <-(subst'_id e Var) at 1; eauto.
        assert (only_has_vars [x;y] e).
        { eapply (typed_to_only_has_vars [(x,t_x);(y,t_y)]); eauto. }
        assert (only_has_vars [y;x] e).
        { apply (only_has_vars_exchange [] []); simpl; eauto. }
        rewrite (subst_compose' [] [y]); eauto; try set_solver.
        rewrite (subst_compose [x] y); set_unfold; simpl; eauto; simp_lookup.
        * f_equal; extensionality x'; simp_lookup; simpl; simp_lookup.
          apply subst_closed.
          eauto using typed_to_closed.
        * intros ? [|[]]. simp_lookup.
          eauto using typed_to_closed.
    - unfold typed_sub. split; intros; simpl in *; simplify_eq.
      simp_lookup.
    - unfold env_is_eval_subst'. intros.
      simpl. simp_lookup; last exfalso; simp_lookup.
      + assert (t0 = t_x) by simp_lookup.
        subst; unshelve eexists; eauto; intros.
        erewrite (lookup_var_here (Γ:=[(_,_)]) x0 pf0).
        symmetry; assumption.
      + assert (t0 = t_y) by simp_lookup.
        subst; unshelve eexists; eauto; intros.
        assert (lookup [(x0,t_y)] x0 = Some t_y) by simp_lookup.
        unshelve erewrite (lookup_var_there (Γ:=[(_,_)]) x0 x pf0); eauto.
        erewrite (lookup_var_here (Γ:=[]) x0 H2).
        symmetry; assumption.
  Qed.

  Lemma eval_of_value_is_some Γ e t (pf : typed' Γ e t) (env : denot_ctx Γ) :
    is_value e -> exists d, eval pf env = Some d.
  Proof.
    destruct e; simpl; intro; try contradiction; dependent destruction pf; eauto.
  Qed.

  Theorem soundness_step e e' t (pf : typed' [] e t) (pf' : typed' [] e' t) :
    step e e' -> eval pf = eval pf'.
  Proof.
    intro H.
    revert t pf pf'.
    induction H; intros.
    - dependent destruction pf.
      dependent destruction pf'.
      assert (t0 = t1) by eauto using types_are_unique'. subst.
      assert (pf'2 = pf2) by eauto using typed'_unique. subst.
      assert (eval pf1 = eval pf'1) by apply IHstep.
      apply sig_eq.
      simpl. rewrite H0. reflexivity.
    - dependent destruction pf.
      dependent destruction pf'.
      assert (Fun t0 t2 = Fun t1 t2) by eauto using types_are_unique'. simplify_eq.
      assert (pf'1 = pf1) by eauto using typed'_unique. subst.
      assert (eval pf2 = eval pf'2) by apply IHstep.
      apply sig_eq.
      simpl. rewrite H1. reflexivity.
    - dependent destruction pf.
      dependent destruction pf1.
      apply sig_eq.
      extensionality env.
      destruct env.
      simpl.
      edestruct (eval_of_value_is_some [] arg t1 pf2 ()); eauto.
      simpl in *.
      rewrite H0.
      eapply subst_eval_one; eauto.
    - dependent destruction pf.
      dependent destruction pf1.
      apply sig_eq.
      extensionality env.
      destruct env.
      edestruct (eval_of_value_is_some [] arg t1 pf2 ()) as [d_arg]; eauto.
      simpl in *.
      rewrite H0.
      rewrite lfp_curry2_unfold.
      change (eval pf1 ((), lfp (curry2 (eval pf1) ()), d_arg) = eval pf' ()).
      unshelve eapply subst_eval_two; eauto using typed'.
    - dependent destruction pf.
      dependent destruction pf'.
      assert (pf'2 = pf2) by eauto using typed'_unique. subst.
      assert (pf'3 = pf3) by eauto using typed'_unique. subst.
      simpl. f_equal. apply (IHstep _ pf1 pf'1).
    - dependent destruction pf.
      dependent destruction pf1.
      assert (pf2 = pf') by eauto using typed'_unique. subst.
      apply sig_eq.
      reflexivity.
    - dependent destruction pf.
      dependent destruction pf1.
      assert (pf3 = pf') by eauto using typed'_unique. subst.
      apply sig_eq.
      reflexivity.
  Qed.

  Corollary soundness e e' t (pf : typed' [] e t) (pf' : typed' [] e' t) :
    rtc step e e' -> eval pf = eval pf'.
  Proof.
    intro. revert pf pf'.
    induction H; intros.
    - assert (pf = pf') by eauto using typed'_unique.
      subst.
      reflexivity.
    - unshelve erewrite (soundness_step x y); eauto using preservation.
  Qed.

  (* I need a logical relation. There's (more or less) two ways to do this: *)
  (*  1. Build it (deeply) into the semantic domain. *)
  (*  2. Write it as a top-level predicate. *)
  (* The first seems quite hard in this setting, so I will do the second. *)

  Definition lift_rel {t} (R : exp -> denot t -> Prop) (e : exp) (x : Lift (denot t)) : Prop :=
    forall x', x = Some x' -> exists v, is_value v /\ closed v /\ rtc step e v /\ R v x'.

  Fixpoint R_V {t} v : denot t -> Prop :=
    match t return denot t -> Prop with
    | Bool => fun x => v = Const x
    | Fun a b => fun f =>
        forall v' x, is_value v' -> closed v' -> R_V (t:=a) v' x -> lift_rel (R_V (t:=b)) (App v v') (`f x)
    end.
  Definition R_E {t} := lift_rel (t:=t) R_V.

  Definition R_env {Γ} sub (env : denot_ctx Γ) :=
    ∀ x t (pf : lookup Γ x = Some t),
      is_value (sub x) /\ closed (sub x) /\ R_V (sub x) (lookup_var x pf env).

  Theorem FTLR {Γ e t} (pf : typed' Γ e t) :
    forall sub env, R_env sub env -> R_E (subst' sub e) (eval pf env).
  Proof.
    unfold R_env, R_E, lift_rel.
    induction pf; simpl; intros; simplify_eq.
    - (* var *)
      exists (sub x).
      destruct (H x ty0 e) as [?[]].
      eauto using rtc_refl.
    - (* const *)
      exists x'. unfold closed; simpl; eauto using rtc_refl.
    - (* if *)
      case_match; simplify_eq.
      edestruct IHpf1 as [vb [?[?[]]]]; eauto.
      simpl in H5.
      case_match; simplify_eq.
      + edestruct IHpf2 as [v [?[?[]]]]; eauto.
        exists v.
        repeat split; eauto.
        transitivity (If true (subst' sub e2) (subst' sub e3));
          eauto using step_if_1', rtc_l, step.
      + edestruct IHpf3 as [v [?[?[]]]]; eauto.
        exists v.
        repeat split; eauto.
        transitivity (If false (subst' sub e2) (subst' sub e3));
          eauto using step_if_1', rtc_l, step.
    - (* app *)
      case_match; simplify_eq.
      case_match; simplify_eq.
      rename c into d_f.
      rename c0 into d_arg.
      edestruct IHpf1 as [v_f [?[?[]]]]; eauto.
      edestruct IHpf2 as [v_arg [?[?[]]]]; eauto.
      clear IHpf1 IHpf2.
      unshelve edestruct H6 as [v [?[?[]]]]; eauto.
      exists v.
      repeat split; eauto.
      transitivity (App v_f (subst' sub e2)); eauto using step_app_1'.
      transitivity (App v_f v_arg); eauto using step_app_2'.
    - (* lam *)
      eexists (Lam x t1 (subst' _ body)).
      split; first constructor.
      split; first last; first (split; first constructor).
      2: admit.
      unfold lift_rel.
      simpl.
      intros.
      edestruct (IHpf (fun x' => if decide (x = x') then v' else sub x')) as [v[?[?[]]]]; eauto.
      { intros.
        simp_lookup.
        + split; eauto.
          assert (t1 = t) by simp_lookup; subst.
          rewrite (lookup_var_here x1 pf0); eauto.
        + assert (lookup Γ x1 = Some t) by simp_lookup.
          unshelve erewrite (lookup_var_there x1 x pf0); eauto. }
      exists v.
      repeat split; eauto.
      eapply rtc_l; first apply step_beta_lam; eauto.
      replace (subst x v' (subst' (fun x' => if decide (x = x') then x' else sub x') body))
                with (subst' (fun x' => if decide (x = x') then v' else sub x') body).
      { eauto. }
      rewrite (subst_compose (map fst Γ)); simp_lookup.
      + apply (subst_equiv (x::map fst Γ)).
        { eapply (typed_to_only_has_vars ((x,_)::Γ)); eauto. }
        intros; simp_lookup; simpl; simp_lookup.
        set_unfold; destruct H8 as [|[?[]]]; simplify_eq.
        symmetry; apply subst_closed.
        assert (∃ t, lookup Γ x2.1 = Some t).
        { apply in_vars_to_lookup. set_solver. }
        destruct H8.
        unshelve edestruct (H x2.1) as [?[]]; first shelve; eauto.
      + eapply (typed_to_only_has_vars ((x,_)::Γ)); eauto.
      + intros.
        edestruct in_vars_to_lookup; eauto.
        case_decide; first congruence.
        unshelve edestruct H as [?[]]; eauto.
    - (* fix *)
      eexists (Fix f x t1 t2 (subst' _ body)).
      split; first constructor.
      split; first last; first (split; first constructor).
      2: admit. (* need a lemma about subst with closed terms *)
      apply fixpoint_induction.
      { simpl. intros. discriminate. }
      intros df IHfix.
      unfold lift_rel.
      intros. rename x0 into darg.
      assert (eval pf (env, df, darg) = Some x') by (rewrite <-(curry2_apply (eval pf)); apply H3).
      edestruct (IHpf (fun x' =>
        if decide (x = x') then v' else
        if decide (f = x') then Fix f x t1 t2 (subst' (λ x',
                              if decide (f = x')
                              then x'
                              else if decide (x = x') then x' else sub x') body)
        else sub x')); eauto.
      { intros.
        simp_lookup.
        + split; eauto.
          assert (t = t1) by simp_lookup; subst.
          rewrite (lookup_var_here (Γ:=(_,_)::_) x0 pf0).
          eauto.
        + split; first constructor.
          split; first admit.
          assert (t = Fun t1 t2) by simp_lookup.
          subst. simpl.
          assert (lookup ((x0,Fun t1 t2)::Γ) x0 = Some (Fun t1 t2)) by simp_lookup.
          unshelve erewrite (lookup_var_there (Γ:=(_,_)::_) x0 x pf0); eauto.
          rewrite (lookup_var_here x0 H5).
          eauto.
        + assert (lookup ((f,Fun t1 t2)::Γ) x0 = Some t) by simp_lookup.
          assert (lookup Γ x0 = Some t) by simp_lookup.
          unshelve edestruct (H x0 t) as [?[]]; eauto.
          split; eauto. split; eauto.
          unshelve erewrite (lookup_var_there (Γ:=(_,_)::_) x0 x pf0); eauto.
          unshelve erewrite (lookup_var_there x0 f H6); eauto.
      }
      exists x0.
      destruct H5 as [?[?[]]].
      repeat split; eauto.
      eapply rtc_l; first eapply step_beta_fix; eauto.
      match goal with |- ?G => let t := type of H7 in replace G with t end; eauto.
      f_equal.
      symmetry.
      admit.
  Admitted.

  (* Up next: adequacy *)
  Corollary adequacy {e t} (pf : typed' [] e t) :
    (exists v, is_value v /\ rtc step e v) <-> (exists v, eval pf tt = Some v).
  Proof.
    split.
    - intros [v[]].
      assert (typed' [] v t) by eauto using preservation_steps.
      unshelve edestruct eval_of_value_is_some; eauto. { constructor. }
      erewrite soundness; eauto.
    - intros [d].
      edestruct (FTLR pf (fun x => x) ()) as [v[?[?[]]]]; eauto.
      { intros ???. simp_lookup. }
      rewrite subst'_id in H2; eauto.
  Qed.

  (* And as a further corollary, ≤ soundly underapproximates contextual refinement *)
