Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.

(** This module defines the “standard rules” — the rules which are not explicitly specified in a type theory, but are always assumed to be present.  These fall into several groups.   

- context formation
- substitution rules
- variable rule
- equality rules

Since “raw rule” in our terminology always mean _hypothetical_ rules, the structural rules that don’t fit this form (context formation and substitution) have to be given directly as families of closure conditions.

All of the above are then collected as a single family [Structural_CCs].
*)

Section Structural_Rules.

Context {σ : Shape_System}.
Context (Σ : @Signature σ).

Section Context_Formation.

Definition empty_context_cc : Closure.rule (Judgt_Instance Σ).
Proof.
  split.
  (* No premises: *)
  - exact [< >].
  (* Conclusion: *)
  - exact [Cxt! |- [::] !].
Defined.

Definition context_extension_cc : Closure.system (Judgt_Instance Σ).
Proof.
  exists { Γ : Raw_Context Σ & Raw_Syntax Σ Ty Γ }.
  intros [ Γ A ]; split.
  (* Premises: |- Γ cxt; Γ |- A type *)
  - refine [< _ ; _ >].
    + exact [Cxt! |- Γ !].
    + exact [Ty! Γ |- A !].
  (* Conclusion: *)
  - exact [Cxt! |- (snoc_Raw_Context Γ A) !].
Defined.

Definition context_ccs : Closure.system (Judgt_Instance Σ)
  := Family.adjoin context_extension_cc empty_context_cc.

(* NOTE: an issue arising from the present approach to shapes/proto-contexts: if the context extension rule is formulated just with [shape_extend] as above, then it will give no way to ever prove well-typedness of contexts with other shapes; in particular, of contexts using [shape_coproduct], which will arise in the premises of logical rules.

  Possible solutions (without entirely changing the proto-context approach):

  - for now, we just aim to work over the de Bruijn shape-system, in which case the standard rules as currently given are enough;
  - to give the standard rules in named-variable case, formulate the context-extension rule in more general way: for *any* (γ+1) coproduct, … (again, should be enough in finitary shape systems)
  - add a closure condition for the context judgements under “renaming variables” along isomorphisms of proto-contexts?  (should again suffice in enough in “finitary” shape systems, i.e. where all shapes finite, and is a nice derived rule to have anyway)
  - for eventual generalisation to infinitary settings, is there some more uniform way of setting this up that would give the standard rules as derived rules?  e.g. (a) put well-orderings on (proto-)contexts, and say: a context is well-typed if each type is well-typed under earlier parts? (b) similar, but without well-orderings (and then allow derivations to take place over not-yet-well-typed contexts)?
*)

End Context_Formation.

Section Substitution.

(* General substitution along context maps. *)

Definition subst_cc : Closure.system (Judgt_Instance Σ).
Proof.
  exists {   Γ : Raw_Context Σ
    & { Γ' : Raw_Context Σ
    & { f : Raw_Context_Map Σ Γ' Γ
    & { hjf : Hyp_Judgt_Form
    & Hyp_Judgt_Form_Instance Σ hjf Γ}}}}.
  intros [Γ [Γ' [f [hjf hjfi]]]].
  split.
  (* premises: *)
  - apply Family.adjoin.
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (Raw_Subst f (Γ i)).
    (* the judgement holds over Γ *)
    + exists (HJF hjf).
      exists Γ.
      exact hjfi.
  (* conclusion: *)
  - exists (HJF hjf).
    exists Γ'.
    intros i. exact (Raw_Subst f (hjfi i)).
Defined.

(* Substitution respects *equality* of context morphisms *)
Definition subst_eq_cc : Closure.system (Judgt_Instance Σ).
Proof.
  exists {   Γ : Raw_Context Σ
    & { Γ' : Raw_Context Σ
    & { f : Raw_Context_Map Σ Γ' Γ
    & { f' : Raw_Context_Map Σ Γ' Γ
    & { cl : Syn_Class
    & Hyp_Judgt_Form_Instance Σ (obj_HJF cl) Γ}}}}}.
  intros [Γ [Γ' [f [f' [cl hjfi]]]]].
  split.
  (* premises: *)
  - refine (Family.adjoin (_ + _ + _) _).
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (Raw_Subst f (Γ i)).
    (* f' is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f' i).
      * exact (Raw_Subst f' (Γ i)).
    (* f ≡ f' *)
    + exists Γ.
      intros i. refine [TmEq! Γ' |- _ ≡ _ ; _ !].
    (* TODO: note inconsistent ordering of arguments in [give_Tm_ji] compared to other [give_Foo_ji].  Consider, consistentise? *)
      * exact (Raw_Subst f (Γ i)).
      * exact (f i).
      * exact (f' i).
    (* the judgement holds over Γ *)
    + exists (HJF (obj_HJF cl)).
      exists Γ.
      exact hjfi.
 (* conclusion: *) 
  - exists (HJF (eq_HJF cl)).
    exists Γ'.
    cbn. intros [i | ]. 
    + (* boundry and LHS *)
      exact (Raw_Subst f (hjfi i)).
    + (* RHS *)
      exact (Raw_Subst f' (hjfi None)).
Defined.

Definition subst_ccs : Closure.system (Judgt_Instance Σ)
  := subst_cc + subst_eq_cc.

End Substitution.

Section Hyp_Structural_Rules.

(* Hypothetical structural rules:

  - var rule
  - equality rules

*)

(* The var rule:

  |– A type
-----------
x:A |– x:A

*)

Definition var_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ )    (* [ A ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (A := None : Metas).
  exists Metas.
  (* single premise:  |— A type *)
  - simple refine [< [Ty! _ |- _ !] >].
    + exact [: :].
    + exact [M/ A /].
  (* conclusion:  x:A |- x:A *)
  - simple refine [Tm! _ |- _ ; _ !].
    + exact [: [M/ A /] :].
    + refine (var_raw _).
      apply (plusone_one _ _ (shape_is_extend _ _)).
    + exact [M/ A /].
Defined.

Section Equality_Rules.

(* rule REFL_TyEq
    ⊢ A type
-----------------
    ⊢ A ≡ A
*)

Definition refl_ty_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ )    (* [ A ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (A := None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ A type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ A /].
  (* Conclusion : ⊢ A ≡ A *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ A /].
Defined.

(* rule SYMM_TyEq
   ⊢ A ≡ B
--------------
   ⊢ B ≡ A
*)

Definition symm_ty_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ )    (* [ A ] *)
    ; (Ty , shape_empty σ )    (* [ B ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (B := None : Metas).
  pose (A := Some None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
  (* Conclusion : ⊢ B ≡ A *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ B /].
    + exact [M/ A /].
Defined.

(* rule TRANS_TyEq
  ⊢ A ≡ B     ⊢ B ≡ C
-----------------------
       ⊢ A ≡ C
*)

Definition trans_ty_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ )    (* [ A ] *)
    ; (Ty , shape_empty σ )    (* [ B ] *)
    ; (Ty , shape_empty σ )    (* [ C ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (C := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ B ≡ C *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ B /].
      * exact [M/ C /].
  (* Conclusion : ⊢ A ≡ C *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ C /].
Defined.

(* rule REFL_TmEq
  ⊢ u : A
-----------
⊢ u ≡ u : A
*)

Definition refl_tm_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (A := Some None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ u : A type *)
      simple refine [Tm! _ |- _ ; _ !].
      * exact [::].
      * exact [M/ u /].
      * exact [M/ A /].
  (* Conclusion : ⊢ u ≡ u : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ u /].
    + exact [M/ u /].
Defined.

(* rule SYMM_TmEq
   ⊢ u ≡ v : A
----------------
   ⊢ v ≡ u : A
*)

Definition symm_tm_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    ; (Tm , shape_empty σ)    (* [ v ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (v := None : Metas).
  pose (u := Some None : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ u ≡ v : A type *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
  (* Conclusion : ⊢ v ≡ u : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ v /].
    + exact [M/ u /].
Defined.

(* rule TRANS_TmEq
  ⊢ u ≡ v : A     ⊢ v ≡ w : A
-------------------------------
         ⊢ u ≡ w : A
*)

Definition trans_tm_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    ; (Tm , shape_empty σ)    (* [ v ] *)
    ; (Tm , shape_empty σ)    (* [ w ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (w := None : Metas).
  pose (v := Some None : Metas).
  pose (u := Some (Some None) : Metas).
  pose (A := Some (Some (Some None)) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ u ≡ v : A type *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
    + (* Premise ⊢ v ≡ w : A type *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ v /].
      * exact [M/ w /].
  (* Conclusion : ⊢ u ≡ w : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ u /].
    + exact [M/ w /].
Defined.

(* rule COERCE_Tm

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u : A
-------------
 ⊢ u : B
*)

Definition coerce_tm_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Ty , shape_empty σ)    (* [ B ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ ; _ ; _ >].
    + (* Premise ⊢ A type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ A /].
    + (* Premise ⊢ B type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ B /].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ u : A *)
      simple refine [Tm! _ |- _ ; _ !].
      * exact [::].
      * exact [M/ u /].
      * exact [M/ A /].
  (* Conclusion: ⊢ u : B *)
  - simple refine [Tm! _ |- _ ; _ !].
    + exact [::].
    + exact [M/ u /].
    + exact [M/ B /].
Defined.

(* rule COERCE_TmEq

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u, u' : A 
 ⊢ u = u' : A
-------------
 ⊢ u = u' : B
*)

Definition coerce_tmeq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Ty , shape_empty σ)    (* [ B ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    ; (Tm , shape_empty σ)    (* [ u' ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (A := Some (Some (Some None)) : Metas).
  pose (B := Some (Some None) : Metas).
  pose (u := Some None : Metas).
  pose (u' := None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ ; _ ; _ ; _ ; _ >].
    + (* Premise ⊢ A type *)
      exact [Ty! [::] |- [M/ A /] !].
    + (* Premise ⊢ B type *)
      exact [Ty! [::] |- [M/ B /] !].
    + (* Premise ⊢ A ≡ B *)
      exact [TyEq! [::] |- [M/ A /] ≡ [M/ B /] !].
    + (* Premise ⊢ u : A *)
      exact [Tm! [::] |- [M/ u /] ; [M/ A /] !].
    + (* Premise ⊢ u' : A *)
      exact [Tm! [::] |- [M/ u' /] ; [M/ A /] !].
    + (* Premise ⊢ u ≡ u' : A *)
      exact [TmEq! [::] |- [M/ u /] ≡ [M/ u' /] ; [M/ A /] !].
  (* Conclusion: ⊢ u ≡ u' : B *)
  - exact [TmEq! [::] |- [M/ u /] ≡ [M/ u' /] ; [M/ B /] !].
Defined.

Definition Equality_Raw_Rules : family (Raw_Rule Σ)
:= [< refl_ty_eq_raw_rule 
    ; symm_ty_eq_raw_rule
    ; trans_ty_eq_raw_rule
    ; refl_tm_eq_raw_rule 
    ; symm_tm_eq_raw_rule
    ; trans_tm_eq_raw_rule
    ; coerce_tm_raw_rule
    ; coerce_tmeq_raw_rule
  >]. 

End Equality_Rules.

End Hyp_Structural_Rules.

Definition Structural_CCs : Closure.system (Judgt_Instance Σ)
:= context_ccs
  + subst_ccs
  + CCs_of_RR var_raw_rule
  + Family.bind Equality_Raw_Rules CCs_of_RR.
(* TODO: add Haskell-style >= notation for bind? *)
(* TODO: capitalise naming in [Context_CCs], etc. *)

End Structural_Rules.

