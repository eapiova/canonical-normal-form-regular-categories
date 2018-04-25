Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawStructuralRule.
Require Import Typed.TypedClosure.
Require Import Raw.FlatTypeTheoryMap.
Require Import Raw.FlatRule.

(** We show that all the structural rules are well-typed.

   For the ones stated as flat rules, this means showing they’re well-typed as such: i.e.
   showing that whenever their premises hold, then all the presuppositions of both their
   premises and conclusion hold.
 *)


(** The following section provides infrastructure to deal with a problem
arising with instantiations of flat rules: their conclusion is typically
over a context whose shape is [ shape_sum Γ (shape_empty σ) ], not just [ Γ ]
as one would expect. 

  So we give here derivations going between a general judgement [ Γ |- J ] and
its reindexing to [ shape_sum Γ (shape_empty σ) ]. 

  It would be good to have some infrastructure (tactics or lemmas?) making
applications of this less intrusive: i.e. to allow one to use instantiations
of flat rules as the closure conditions one expects them to be, with just [Γ]
instead of [ shape_sum Γ (shape_empty σ) ]. *)
(* TODO: upstream the entire section; but to where? *)

(* TODO: in fact, with current structural rules, this probably won’t be possible, since our context formation rules only give us contexts obtainable as an iterated extension.  How to fix this??? *)
Section Sum_Shape_Empty.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (* TODO: upstream *)
  Definition shape_sum_empty (γ : σ) : σ
  := shape_sum γ (shape_empty σ).

  (* TODO: upstream *)
  Definition shape_sum_empty_inl_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj1 shape_is_sum : γ -> shape_sum_empty γ).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (coproduct_rect shape_is_sum).
      + intros i; exact i.
      + apply (empty_rect _ shape_is_empty).
    - unfold Sect. apply (coproduct_rect shape_is_sum).
      + intros i. apply ap.
        refine (coproduct_comp_inj1 _).
      + apply (empty_rect _ shape_is_empty).
    - intros i. refine (coproduct_comp_inj1 _).
  Defined.

  (* TODO: upstream *)
  Definition shape_sum_empty_inl (γ : σ)
    : γ <~> shape_sum_empty γ
  := BuildEquiv _ _ _ (shape_sum_empty_inl_is_equiv γ).

  (* TODO: upstream *)
  Definition raw_context_sum_empty (Γ : raw_context Σ)
    : raw_context Σ
  := rename_raw_context _ Γ (equiv_inverse (shape_sum_empty_inl _)).

  (* TODO: upstream *)
  Definition reindexing_to_empty_sum
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical hjf).
    exists (raw_context_sum_empty Γ).
    intros i. exact (rename (shape_sum_empty_inl _) (J i)).
  Defined.

  (** From any judgement [ Γ |- J ],
      one can derive [ Γ+0 |- r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derive_reindexing_to_empty_sum
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : Closure.derivation (structural_rule Σ)
        [< (form_hypothetical hjf ; (Γ ; J)) >] 
        (reindexing_to_empty_sum J).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply rename_hypothetical.
      exists Γ.
      refine (_ ; (equiv_inverse (shape_sum_empty_inl _) ; _)).
      exists hjf. exact J.
    - apply idpath.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  (* TODO: upstream *)
  Lemma rename_idmap {γ} {cl} (e : raw_expression Σ cl γ)
    : rename idmap e = e.
  Proof.
  Admitted.

  (* TODO: upstream *)
  (** To derive a judgement [ Γ |- J ],
      it’s sufficient to derive [ Γ+0 |- r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derive_from_reindexing_to_empty_sum
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : Closure.derivation (structural_rule Σ)
        [< reindexing_to_empty_sum J >]
        (form_hypothetical hjf ; (Γ ; J)).
  Proof.
    (* Outline: renaming rule, along [shape_sum_empty_inl], plus
    functoriality lemma for renaming to show that the conclusion
    of that is the original judgement. *)
    simple refine (Closure.deduce' _ _ _).
    - apply rename_hypothetical.
      exists (raw_context_sum_empty Γ),
        Γ, (shape_sum_empty_inl _), hjf.
      exact (fun i => rename (shape_sum_empty_inl _) (J i)).
    - apply (ap (fun x => (_;x))).
      refine (@ap _ _
            (fun ΓJ : (_ * hypothetical_judgement _ _ Γ)
              => (Build_raw_context Γ (fst ΓJ) ; snd ΓJ))
            (_,_) (_,_) _).
      apply path_prod; apply path_forall; intros i.
      + eapply concat. { apply inverse, RawSubstitution.comp_Raw_Weaken. }
        eapply concat.
        { eapply (ap (fun f => rename f _)).
          apply path_forall; intros j; apply eissect. }
        eapply concat. { apply rename_idmap. }
        apply ap, eissect.
      + eapply concat. { apply inverse, RawSubstitution.comp_Raw_Weaken. }
        eapply concat.
        { eapply (ap (fun f => rename f _)).
          apply path_forall; intros j; apply eissect. }
        apply rename_idmap.
 (* lemma on functoriality of substitution *)
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.
  (* TODO: rename everything involving [Raw_Weaken], [Raw_Subst]! *)

End Sum_Shape_Empty.

Section TypedStructuralRule.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** In this section we show that all structural rules are well-typed, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)

  (** Is a given closure rule arising from a total judgement well-typed in the sense
      that its presuppositions are derivable using structural rules? *)
  Local Definition is_well_typed : Closure.rule (judgement_total Σ) -> Type
  := TypedClosure.weakly_well_typed_rule presupposition (structural_rule Σ).

  (** Context rules are well typed. *)
  Local Definition context_is_well_typed (r : RawStructuralRule.context_instance Σ)
    : is_well_typed (RawStructuralRule.context_instance _ r).
  Proof.
    apply TypedClosure.weakly_from_strongly_well_typed_rule.
    destruct r as [  [Γ A] | ].
    - split. (* context extension *)
      + intros [ [] | ]. (* two premises *)
        * intros []. (* context hypothesis: no presups *)
        * intros [ [] | ]. (* type hypothesis: one presup *)
          simple refine (Closure.hypothesis' _ _).
          -- cbn. apply (Some tt).
          -- apply idpath.
      + intros []. (* conclusion: no presups *)
    - split. (* empty context rule *)
      + intros []. (* no premises *)
      + intros []. (* no presups for conclusion *)
  Defined.

  (** Rules for variable-renaming in contexts are well typed *)
  Local Definition rename_context_is_well_typed
      (r : RawStructuralRule.rename_context_instance Σ)
    : is_well_typed (RawStructuralRule.rename_context_instance _ r).
  Proof.
    intros []. (* no presups for conclusion *)
  Defined.

  (** Rules for variable-renaming in hypothetical judgements are well typed *)
  Local Definition rename_hypothetical_is_well_typed
      (r : RawStructuralRule.rename_hypothetical_instance Σ)
    : is_well_typed (RawStructuralRule.rename_hypothetical_instance _ r).
  Proof.
    destruct r as [Γ [γ' [f [hjf J]]]]; cbn.
    intros p.
    set (p_orig := p : presupposition (form_hypothetical hjf; Γ; J)).
    (* In all cases, we just rename along [f] in the corresponding original
    presupposition.  However, this will require a different rule — either
    [rename_context] or [rename_hypotherical] — depending on whether [p] is
    the context presup or a hypothetical presup. *)
    destruct p as [ p | ].
    - (* hypothetical presupposition *)
      set (JJ_p_orig := presupposition _ p_orig).
      set (hjf_p := match JJ_p_orig.1 with form_context => hjf
                                     | form_hypothetical hjf_p => hjf_p end).
      cbn in hjf_p.
      set (J_p_orig := (JJ_p_orig.2).2).
      simple refine (Closure.deduce' _ _ _).
      + apply rename_hypothetical. exists Γ, γ', f, hjf_p. exact J_p_orig.
      + apply (ap (fun x => (_;x))).
        apply (ap (fun x => (_;x))).
        apply path_forall; intros i.
        recursive_destruct hjf; recursive_destruct p; recursive_destruct i;
          apply idpath.
      + intros []. 
        simple refine (Closure.hypothesis' _ _).
        * apply inr. (* go for a presup *)
          exact (tt; p_orig). (* select corresponding original presup *)
        * apply idpath.
    - (* context presupposition *)
      simple refine (Closure.deduce' _ _ _). 
      + apply rename_context. exists Γ, γ'; exact f.
      + apply idpath.
      + intros []. 
        simple refine (Closure.hypothesis' _ _).
        * apply inr. (* go for a presup *)
          exact (tt; p_orig). (* select corresponding original presup *)
        * apply idpath.
  Defined.

  (** All variable-renaming rules are well typed *)
  Local Definition rename_is_well_typed
      (r : RawStructuralRule.rename_instance Σ)
    : is_well_typed (RawStructuralRule.rename_instance _ r).
  Proof.
    destruct r as [ ? | ? ].
    - apply rename_context_is_well_typed.
    - apply rename_hypothetical_is_well_typed.
  Defined.

  (** Substitution-application rules are well typed *)
  Local Definition subst_apply_is_well_typed
        (r : RawStructuralRule.subst_apply_instance Σ)
    : is_well_typed (RawStructuralRule.subst_apply_instance _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ hjf J]]]].
    intros p.
    transparent assert (j : (judgement_total Σ)).
      { exists (form_hypothetical hjf). refine (Γ;J). }
    transparent assert (p' : (presupposition j)).
      { exact p. }
    destruct p as [ p | ].
    - (* [p] a hypothetical presupposition *)
      simple refine (Closure.deduce' _ _ _).
      (* Aim here: apply the same substitution rule, with the same substition,
         but with target the presupposition [p] of the original target. *)
      + apply subst_apply.
        (* TODO: give access functions for locating the structural rules! *)
        exists Γ, Γ', f.
        exists (form_object (Judgement.boundary_slot _ p)).
        exact (pr2 (pr2 (presupposition _ p'))).
      + recursive_destruct hjf; recursive_destruct p;
          apply Judgement.eq_by_eta; apply idpath.
      + intros [ q | ].
        * (* premises: show the substitution OK. *)
          simple refine (Closure.hypothesis' _ _).
          -- exact (inl (Some q)).
          -- apply idpath.
        * (* premises: new presupposition *)
          simple refine (Closure.hypothesis' _ _).
          -- exact (inr (None; p')).
          -- apply idpath.
    - (* [p] the context presupposition [Γ'] *)
      simple refine (Closure.hypothesis' _ _).
      + exact (inl (Some None)).
      + apply idpath.
  Defined.


  (** Substitution-equality rules are well typed *)
  Local Definition subst_equal_is_well_typed
        (r : RawStructuralRule.subst_equal_instance Σ)
    : is_well_typed (RawStructuralRule.subst_equal_instance _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ g [cl J]]]]].
    intros p.
    transparent assert (j : (judgement_total Σ)).
      { exists (form_hypothetical (form_object cl)). refine (Γ;J). }
    destruct p as [ p | ].
    - (* [p] a hypothetical presupposition *)
      (* What we do here genuinely depends on [cl]. *)
      destruct cl as [ | ].
      (* Case 1: substitutions are into a type judgement.
         Then the presups of [ Γ |- f^*A = g^*A ] are just
         [ Γ |- f^*A type ] and [ Γ |- g^*A type ].
         In each case, we get them by the [substitution_apply] rule. *)
      + simple refine (Closure.deduce' _ _ _).
        * apply subst_apply.
          exists Γ, Γ'. refine (_;(form_object class_type; J)).
          destruct p as [ [] | | ].
          -- exact f.
          -- exact g.
        * recursive_destruct p;
            apply Judgement.eq_by_eta; apply idpath.
        * intros h; cbn in h.
          destruct h as [ [ x | ] | ].
          -- (* premise: [f] / [g] is a context map *)
            destruct p as [ [] | | ].
            ++ simple refine (Closure.hypothesis' _ _).
              ** apply inl, Some, Some, inl, inl, x.
              ** apply idpath.
            ++ simple refine (Closure.hypothesis' _ _).
              ** apply inl, Some, Some, inl, inr, x.
              ** apply idpath.
          -- (* premise: [Γ'] is a context *)
            simple refine (Closure.hypothesis' _ _).
            ++ exact (inl (Some None)).
            ++ apply idpath.
          -- (* premise: [Γ |- J]  *)
            simple refine (Closure.hypothesis' _ _).
            ++ exact (inl None).
            ++ apply idpath.
        
      (* Case 2: substitutions are into a term judgement [ Γ |- a : A].
         Then the presups of [ Γ |- f^*a = g^*a : f^* A] are
         [ Γ |- f^*A type ], [ Γ |- f^*a : f^*A ], and [ Γ |- g^*A : f^*A ].
         The first two, we get by the [substitution_apply] rule; the third 
         additionally requires the [term_convert] and [substitution_equal]
         rules. *)
      + recursive_destruct p.
        * (* presup [ Γ |- f^*A type ] *)
          simple refine (Closure.deduce' _ _ _).
          -- apply subst_apply.
             exists Γ, Γ', f. refine (form_object class_type; _).
             intros [[] | ].
             exact (J (the_boundary class_term the_term_type)).
          -- apply Judgement.eq_by_eta; apply idpath.
          -- intros [ [ x | ] | ].
             ++ (* premise: [f] is a context map *)
               simple refine (Closure.hypothesis' _ _).
               ** apply inl, Some, Some, inl, inl, x.
               ** apply idpath.
             ++ (* premise: [Γ'] is a context *)
               simple refine (Closure.hypothesis' _ _).
               ** exact (inl (Some None)).
               ** apply idpath.
             ++ (* premise: [Γ |- A type ]  *)
               simple refine (Closure.hypothesis' _ _).
               ** apply inr. exists None. exact (Some the_term_type).
               ** apply Judgement.eq_by_eta; apply idpath.
        * (* presup [ Γ' |- f^*a : f^*A ] *)
          simple refine (Closure.deduce' _ _ _).
          -- apply subst_apply. (* subst-apply rule:
                                   substitute f into Γ |- a : A *)
             exists Γ, Γ', f. refine (form_object class_term; _).
             exact J.
          -- apply Judgement.eq_by_eta; apply idpath.
          -- intros [ [ x | ] | ].
             ++ (* premise: [f] is a context map *)
               simple refine (Closure.hypothesis' _ _).
               ** apply inl, Some, Some, inl, inl, x.
               ** apply idpath.
             ++ (* premise: [Γ'] is a context *)
               simple refine (Closure.hypothesis' _ _).
               ** exact (inl (Some None)).
               ** apply idpath.
             ++ (* premise: [Γ |- a : A type ]  *)
               simple refine (Closure.hypothesis' _ _).
               ** exact (inl None).
               ** apply idpath.
        * (* presup [ Γ' |- g^*a : f^*A ] *)
          apply Judgement.canonicalise. unfold Judgement.eta_expand; cbn.
          refine (Closure.graft' _ _ _).
          -- simple refine (derive_from_reindexing_to_empty_sum _).
            exact Γ'. exact (form_object class_term).
            intros i; recursive_destruct i.
            ++ exact (substitute f (J (the_boundary class_term the_term_type))).
            ++ exact (substitute g (J (the_head class_term))).
          -- apply idpath.
          -- intros [].
            simple refine (Closure.deduce' _ _ _).
            ++ apply term_convert. (* term_convert rule *)
              exists Γ'. cbn.
              intros i; recursive_destruct i; cbn.
               ** refine (rename _ (substitute f
                          (J (the_boundary class_term the_term_type)))). (* [f^*A] *)
                 apply shape_sum_empty_inl.
               ** refine (rename _ (substitute g
                          (J (the_boundary class_term the_term_type)))). (* [g^*A] *)
                 apply shape_sum_empty_inl.
               ** refine (rename _ (substitute g
                          (J (the_head _)))). (* [g^*a] *)
                 apply shape_sum_empty_inl.
            ++ apply Judgement.eq_by_eta.
              apply ap.
              admit. (*functoriality of substitution *)
   (* TODO: all the above three are the same problem: renaming between a proto-context and its sum with the empty shape.  Think about how to make a utility lemma to deal with this situation!
   E.g. given an “algebraic” flat rule, can get a derivable equivallent that doesn’t add this damn thing to the context? *)
            ++ admit. (* from hypotheses, via an inverse to
                         [derive_from_reindexing_to_empty_sum]. *)
    - (* [p] the context presupposition [Γ'] *)
      simple refine (Closure.hypothesis' _ _).
      + exact (inl (Some None)).
      + apply idpath.
  Admitted.

  (** All substitution rules are well typed *)
  Local Definition subst_is_well_typed (r : RawStructuralRule.substitution_instance Σ)
    : is_well_typed (RawStructuralRule.substitution_instance _ r).
  Proof.
    destruct r as [ ? | ? ].
    - apply subst_apply_is_well_typed.
    - apply subst_equal_is_well_typed.
  Defined.

  (** Variable rules are well typed *)
  Local Definition variable_is_well_typed (r : RawStructuralRule.variable_instance Σ)
    : is_well_typed (RawStructuralRule.variable_instance _ r).
  Proof.
    destruct r as [Γ x].
    intros i; recursive_destruct i.
    (* type presupposition *)
    - simple refine (Closure.hypothesis' _ _).
      + cbn. apply inl, None.
      + apply Judgement.eq_by_eta; apply idpath.
    (* context presupposition *)
    - simple refine (Closure.hypothesis' _ _).
      + cbn. apply inl, Some, tt.
      + cbn. apply idpath.
  Defined.

  (** Equality rules are well typed *)
  Local Definition equality_is_well_typed (r : RawStructuralRule.equality_instance Σ)
    : is_well_typed (RawStructuralRule.equality_instance _ r).
  Proof.
    (* deduce from showing these are well-typed as flat rules *)
  Admitted.

  (** Putting the above components together, we obtain the main result:
      all structural rules are well-typed. *)
  Local Definition well_typed
    : TypedClosure.weakly_well_typed_system presupposition (structural_rule Σ).
  Proof.
    intros [ [ [ [ ? | ? ] | ? ] | ? ] | ? ].
    - apply context_is_well_typed.
    - apply rename_is_well_typed.
    - apply subst_is_well_typed.
    - apply variable_is_well_typed.
    - apply equality_is_well_typed.
  Admitted.

End TypedStructuralRule.
