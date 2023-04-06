From HoTT Require Import HoTT.
From GeneralTT Require Import Auxiliary.Family.
From GeneralTT Require Import Auxiliary.Coproduct.
From GeneralTT Require Import Syntax.ScopeSystem.
From GeneralTT Require Import Syntax.All.
From GeneralTT Require Import Typing.Context.
From GeneralTT Require Import Typing.Judgement.
From GeneralTT Require Import Typing.RawRule.
From GeneralTT Require Import Typing.StructuralRule.
From GeneralTT Require Import Typing.RawTypeTheory.
From GeneralTT Require Import Auxiliary.WellFounded.
From GeneralTT Require Import Presented.AlgebraicExtension.
From GeneralTT Require Import Presented.PresentedRawRule.
From GeneralTT Require Import Presented.PresentedRawTypeTheory.
From GeneralTT Require Import Presented.TypedRule.
From GeneralTT Require Import Presented.TypeTheory.
From GeneralTT Require Import Metatheorem.UniqueTyping.
From GeneralTT Require Import Metatheorem.Elimination.
From GeneralTT Require Import Metatheorem.Presuppositions.
From GeneralTT Require Import Metatheorem.Acceptability.
From GeneralTT Require Import Example.ScopeSystemExamples.
Require Setoid.










Inductive TReg_symbols : Type :=
  | Terminal_symbol | star_symbol | Sigma_symbol | pairs_symbol | el_Sigma_symbol | Eq_symbol | eq_symbol. (* | Qtr_symbol | class_symbol | el_Qtr_symbol. *)

Definition Sig : signature DeBruijn.
Proof.
  exists TReg_symbols.
  intros.
  induction H.
  - exact (class_type, [< >]). (* Top *)
  - exact (class_term, [< >]). (* Star *)
  - exact (class_type, [< (class_type, 0%nat); (class_type, 1%nat) >]). (* Sigma *)
  - refine (class_term, [< (class_term, 0%nat); (class_term, 0%nat) >]). (* pair *)
  - refine (class_term, [< (class_term, 0%nat); (class_term, 2%nat) >]). (* el_Sigma *)
  - refine (class_type, [< (class_type, 0%nat); (class_term, 0%nat); (class_term, 0%nat) >]). (* Eq *)
  - refine (class_term, [< (class_type, 0%nat); (class_term, 0%nat) >]). (* eq *)
  (*
  - refine (class_type, [< (class_type, 0%nat) >]). (* Qtr *)
  - refine (class_term, [< (class_term, 0%nat) >]). (* class *)
  - refine (class_term, [< (class_term, 1%nat); (class_term, 0%nat) >]). (* el_Qtr *)
  *)
Defined.



Definition Terminal : family_index Sig.
Proof.
  refine Terminal_symbol.
Defined.

Definition star : family_index Sig.
Proof.
  refine star_symbol.
Defined.

Definition Sigma : family_index Sig.
Proof.
  refine Sigma_symbol.
Defined.

Definition pairs : family_index Sig.
Proof.
  refine pairs_symbol.
Defined.

Definition el_Sigma : family_index Sig.
Proof.
  refine el_Sigma_symbol.
Defined.

Definition Eq : family_index Sig.
Proof.
  refine Eq_symbol.
Defined.

Definition eq : family_index Sig.
Proof.
  refine eq_symbol.
Defined.








Section Terminal_type.

Definition F_Tr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := [< >]; raw_rule_premise := [< >]; raw_rule_conclusion := _ |}.
  refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
  refine {| form_of_judgement := form_object class_type; judgement_expression := _|}.
  unfold hypothetical_judgement_expressions.
  intros. 
  recursive_destruct i. refine (raw_symbol (include_symbol Terminal) _).
    intros.
    destruct i.
Defined.

Definition I_Tr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := [< >]; raw_rule_premise := [< >]; raw_rule_conclusion := _ |}.
  refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
  refine {| form_of_judgement := form_object class_term; judgement_expression := _|}.
  unfold hypothetical_judgement_expressions.
  intros. recursive_destruct i.
  + refine (raw_symbol (include_symbol Terminal) _).
    intros.
    destruct i.
  + refine (raw_symbol (include_symbol star) _).
    intros.
    destruct i.
Defined.

Inductive metas_C_Tr_symbols : Type := t_C_Tr_symbol.

Let metas : arity DeBruijn.
Proof.
  exists metas_C_Tr_symbols.
  intros.
  induction X.
  refine (class_term, 0%nat).
Defined.

Let t : family_index metas.
Proof.
  refine t_C_Tr_symbol.
Defined.

Definition C_Tr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
    + refine [< _ >].
      refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _|}.
      unfold hypothetical_judgement_expressions. intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol Terminal) _). intros. destruct i.
      * refine (raw_symbol (include_metavariable t) (empty_rect _ scope_is_empty _)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_term; judgement_expression := _|}.
      unfold hypothetical_judgement_expressions. intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol Terminal) _). intros. destruct i.
      * refine (raw_symbol (include_metavariable t) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_symbol star) _). intros. destruct i.
Defined.

End Terminal_type.



Inductive metas_F_Sigma_symbols : Type := B_F_Sigma_symbol | C_F_Sigma_symbol.

Definition metas_F_Sigma : arity DeBruijn.
Proof.
  exists metas_F_Sigma_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
Defined.

Definition B_F_Sigma : family_index metas_F_Sigma.
Proof.
  refine B_F_Sigma_symbol.
Defined.

Definition C_F_Sigma : family_index metas_F_Sigma.
Proof.
  refine C_F_Sigma_symbol.
Defined.


Definition F_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_F_Sigma; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable B_F_Sigma) (Metavariable.empty_args scope_is_empty)).
    + refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        refine (raw_symbol (include_metavariable C_F_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    refine (raw_symbol (include_symbol Sigma) _).
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable B_F_Sigma) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable C_F_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
Defined.






Inductive metas_I_Sigma_symbols : Type := B_I_Sigma_symbol | C_I_Sigma_symbol | b_I_Sigma_symbol | c_I_Sigma_symbol.

Definition metas_I_Sigma : arity DeBruijn.
Proof.
  exists metas_I_Sigma_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Definition B_I_Sigma : family_index metas_I_Sigma.
Proof.
  refine B_I_Sigma_symbol.
Defined.

Definition C_I_Sigma : family_index metas_I_Sigma.
Proof.
  refine C_I_Sigma_symbol.
Defined.

Definition b_I_Sigma : family_index metas_I_Sigma.
Proof.
  refine b_I_Sigma_symbol.
Defined.

Definition c_I_Sigma : family_index metas_I_Sigma.
Proof.
  refine c_I_Sigma_symbol.
Defined.


Definition I_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_I_Sigma; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B_I_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable b_I_Sigma) (Metavariable.empty_args scope_is_empty)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_I_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_metavariable b_I_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_I_Sigma) (Metavariable.empty_args scope_is_empty)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B_I_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C_I_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B_I_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C_I_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
    + refine (raw_symbol (include_symbol pairs) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable b_I_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_I_Sigma) (Metavariable.empty_args scope_is_empty)).
Defined.

Print I_Sigma.


Inductive metas_E_Sigma_symbols : Type := B_E_Sigma_symbol | C_E_Sigma_symbol | M_E_Sigma_symbol | d_E_Sigma_symbol | m_E_Sigma_symbol .

Definition metas_E_Sigma : arity DeBruijn.
Proof.
  exists metas_E_Sigma_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_type, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 2%nat).
Defined.

Definition B_E_Sigma : family_index metas_E_Sigma.
Proof.
  refine B_E_Sigma_symbol.
Defined.

Definition C_E_Sigma : family_index metas_E_Sigma.
Proof.
  refine C_E_Sigma_symbol.
Defined.

Definition M_E_Sigma : family_index metas_E_Sigma.
Proof.
  refine M_E_Sigma_symbol.
Defined.

Definition d_E_Sigma : family_index metas_E_Sigma.
Proof.
  refine d_E_Sigma_symbol.
Defined.

Definition m_E_Sigma : family_index metas_E_Sigma.
Proof.
  refine m_E_Sigma_symbol.
Defined.

(* VAR *)

Definition E_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_E_Sigma; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_symbol Sigma) _).
        intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable B_E_Sigma) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable C_E_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
           apply (zero_db).
      * refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        refine (raw_symbol (include_metavariable M_E_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        (* var *)
        apply (zero_db).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable B_E_Sigma) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable C_E_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
          apply zero_db.
      * refine (raw_symbol (include_metavariable d_E_Sigma) (Metavariable.empty_args scope_is_empty)).
    + simple refine {| context_of_judgement := [: _; _:]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_metavariable B_E_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C_E_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
      * refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable M_E_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
           refine (raw_symbol (include_symbol pairs) _).
           intros. recursive_destruct i.
           ++ refine (raw_variable _).
              apply zero_db.
           ++ refine (raw_variable _).
              apply (succ_db zero_db).
        -- refine (raw_symbol (include_metavariable m_E_Sigma) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
          ++ apply zero_db.
          ++ apply (succ_db zero_db).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable M_E_Sigma) _).
      intros.
      refine (raw_symbol (include_metavariable d_E_Sigma) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_symbol el_Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable d_E_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable m_E_Sigma) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
      ++ apply zero_db.
      ++ apply (succ_db zero_db).
Defined.


Inductive metas_C_Sigma_symbols : Type := B_C_Sigma_symbol | C_C_Sigma_symbol | M_C_Sigma_symbol | b_C_Sigma_symbol | c_C_Sigma_symbol | m_C_Sigma_symbol .

Definition metas_C_Sigma : arity DeBruijn.
Proof.
  exists metas_C_Sigma_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_type, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 2%nat).
Defined.

Definition B_C_Sigma : family_index metas_C_Sigma.
Proof.
  refine B_C_Sigma_symbol.
Defined.

Definition C_C_Sigma : family_index metas_C_Sigma.
Proof.
  refine C_C_Sigma_symbol.
Defined.

Definition M_C_Sigma : family_index metas_C_Sigma.
Proof.
  refine M_C_Sigma_symbol.
Defined.

Definition b_C_Sigma : family_index metas_C_Sigma.
Proof.
  refine b_C_Sigma_symbol.
Defined.

Definition c_C_Sigma : family_index metas_C_Sigma.
Proof.
  refine c_C_Sigma_symbol.
Defined.

Definition m_C_Sigma : family_index metas_C_Sigma.
Proof.
  refine m_C_Sigma_symbol.
Defined.

(* SISTCMARC VAR *)

Definition C_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_C_Sigma; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _; _ >].
    + simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_symbol Sigma) _).
        intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable B_C_Sigma) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable C_C_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
           apply (zero_db).
      * refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        refine (raw_symbol (include_metavariable M_C_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        (* var *)
        apply (zero_db).
        + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
        refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        * refine (raw_symbol (include_metavariable B_C_Sigma) (Metavariable.empty_args scope_is_empty)).
        * refine (raw_symbol (include_metavariable b_C_Sigma) (Metavariable.empty_args scope_is_empty)).
      + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
        refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        * refine (raw_symbol (include_metavariable C_C_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
          refine (raw_symbol (include_metavariable b_C_Sigma) (Metavariable.empty_args scope_is_empty)).
        * refine (raw_symbol (include_metavariable c_C_Sigma) (Metavariable.empty_args scope_is_empty)).
    + simple refine {| context_of_judgement := [: _; _:]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_metavariable B_C_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C_C_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
      * refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable M_C_Sigma) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
           refine (raw_symbol (include_symbol pairs) _).
           intros. recursive_destruct i.
           ++ refine (raw_variable _).
              apply zero_db.
           ++ refine (raw_variable _).
              apply (succ_db zero_db).
        -- refine (raw_symbol (include_metavariable m_C_Sigma) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
          ++ apply zero_db.
          ++ apply (succ_db zero_db).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable M_C_Sigma) _).
      intros.
      refine (raw_symbol (include_symbol pairs) _).
      intros. recursive_destruct i0.
      * refine (raw_symbol (include_metavariable b_C_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_C_Sigma) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_symbol el_Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol pairs) _).
        intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable b_C_Sigma) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable c_C_Sigma) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable m_C_Sigma) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
        ++ apply zero_db.
        ++ apply (succ_db zero_db).
    + refine (raw_symbol (include_metavariable m_C_Sigma) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _) _)).
      ++ refine (raw_symbol (include_metavariable b_C_Sigma) (Metavariable.empty_args scope_is_empty)).
      ++ refine (raw_symbol (include_metavariable c_C_Sigma) (Metavariable.empty_args scope_is_empty)).
Defined.




Inductive metas_F_Eq_symbols : Type := C_F_Eq_symbol | c_F_Eq_symbol | d_F_Eq_symbol.

Definition metas_F_Eq : arity DeBruijn.
Proof.
  exists metas_F_Eq_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Definition C_F_Eq : family_index metas_F_Eq.
Proof.
  refine C_F_Eq_symbol.
Defined.

Definition c_F_Eq : family_index metas_F_Eq.
Proof.
  refine c_F_Eq_symbol.
Defined.

Definition d_F_Eq : family_index metas_F_Eq.
Proof.
  refine d_F_Eq_symbol.
Defined.


Definition F_Eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_F_Eq; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable C_F_Eq) (empty_rect _ scope_is_empty _)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_F_Eq) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c_F_Eq) (empty_rect _ scope_is_empty _)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_F_Eq) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable d_F_Eq) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    refine (raw_symbol (include_symbol Eq) _).
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable C_F_Eq) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable c_F_Eq) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable d_F_Eq) (empty_rect _ scope_is_empty _)).
Defined.



Inductive metas_I_Eq_symbols : Type := C_I_Eq_symbol | c_I_Eq_symbol.

Definition metas_I_Eq : arity DeBruijn.
Proof.
  exists metas_I_Eq_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Local Definition C_I_Eq : family_index metas_I_Eq.
Proof.
  refine C_I_Eq_symbol.
Defined.

Local Definition c_I_Eq : family_index metas_I_Eq.
Proof.
  refine c_I_Eq_symbol.
Defined.



Definition I_Eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_I_Eq; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable C_I_Eq) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable c_I_Eq) (Metavariable.empty_args scope_is_empty)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Eq) _).
      intros.
      recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_I_Eq) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c_I_Eq) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c_I_Eq) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol eq) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_I_Eq) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c_I_Eq) (empty_rect _ scope_is_empty _)).
Defined.




Inductive metas_E_Eq_symbols : Type := C_E_Eq_symbol | c_E_Eq_symbol | d_E_Eq_symbol | p_E_Eq_symbol.

Definition metas_E_Eq : arity DeBruijn.
Proof.
  exists metas_E_Eq_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Definition C_E_Eq : family_index metas_E_Eq.
Proof.
  refine C_E_Eq_symbol.
Defined.

Definition c_E_Eq : family_index metas_E_Eq.
Proof.
  refine c_E_Eq_symbol.
Defined.

Definition d_E_Eq : family_index metas_E_Eq.
Proof.
  refine d_E_Eq_symbol.
Defined.

Definition p_E_Eq : family_index metas_E_Eq.
Proof.
  refine p_E_Eq_symbol.
Defined.


Definition E_Eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_E_Eq; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Eq) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_E_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_E_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable d_E_Eq) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable p_E_Eq) (Metavariable.empty_args scope_is_empty)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    * refine (raw_symbol (include_metavariable C_E_Eq) (Metavariable.empty_args scope_is_empty)).
    * refine (raw_symbol (include_metavariable c_E_Eq) (Metavariable.empty_args scope_is_empty)).
    * refine (raw_symbol (include_metavariable d_E_Eq) (Metavariable.empty_args scope_is_empty)).
Defined.



Inductive metas_C_Eq_symbols : Type := C_C_Eq_symbol | c_C_Eq_symbol | d_C_Eq_symbol | p_C_Eq_symbol.

Definition metas_C_Eq : arity DeBruijn.
Proof.
  exists metas_C_Eq_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Definition C_C_Eq : family_index metas_C_Eq.
Proof.
  refine C_C_Eq_symbol.
Defined.

Definition c_C_Eq : family_index metas_C_Eq.
Proof.
  refine c_C_Eq_symbol.
Defined.

Definition d_C_Eq : family_index metas_C_Eq.
Proof.
  refine d_C_Eq_symbol.
Defined.

Definition p_C_Eq : family_index metas_C_Eq.
Proof.
  refine p_C_Eq_symbol.
Defined.


Definition C_Eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas_C_Eq; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Eq) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_C_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_C_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable d_C_Eq) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable p_C_Eq) (Metavariable.empty_args scope_is_empty)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Eq) _).
    intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_C_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_C_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable d_C_Eq) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable p_C_Eq) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_symbol eq) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C_C_Eq) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c_C_Eq) (Metavariable.empty_args scope_is_empty)).
Defined.

Inductive rule_indexes := F_Tr_index | F_Tr_Eq_index | I_Tr_index | I_Tr_Eq_index | C_Tr_index 
                        | F_Sigma_index | I_Sigma_index | E_Sigma_index | C_Sigma_index 
                        | F_Eq_index | I_Eq_index | E_Eq_index | C_Eq_index.




Definition TReg : raw_type_theory Sig.
Proof.
  exists rule_indexes.
  intros.
  induction H.
  - refine F_Tr.
  - refine (raw_congruence_rule F_Tr tt).
  - refine I_Tr. 
  - refine (raw_congruence_rule I_Tr tt).
  - refine C_Tr.
  - refine F_Sigma.
  - refine I_Sigma.
  - refine E_Sigma.
  - refine C_Sigma.
  - refine F_Eq.
  - refine I_Eq.
  - refine E_Eq.
  - refine C_Eq.
Defined.




Definition derivable J := exists H, RawTypeTheory.derivation TReg H J.

Print derivable.

Definition Terminal_type {gamma} : raw_type Sig gamma.
Proof.
  refine (raw_symbol Terminal _).
  intros.
  destruct i.
Defined.


Section Sigma_type.

Definition Sigma_type {gamma : scope_carrier DeBruijn} (A : raw_type Sig (scope_sum gamma 0%nat)) (B : raw_type Sig (scope_sum gamma 1%nat)) : raw_type Sig gamma.
Proof.
  refine (raw_symbol Sigma _).
  intros.
  recursive_destruct i.
  - refine A.
  - refine B.
Defined.

End Sigma_type.


Section Eq_type.

Definition Eq_type {gamma : scope_carrier DeBruijn} (A : raw_type Sig (scope_sum gamma 0%nat)) (a b : raw_term Sig (scope_sum gamma 0%nat)) : raw_type Sig gamma.
Proof.
  refine (raw_symbol Eq _).
  intros.
  recursive_destruct i.
  - refine A.
  - refine a.
  - refine b.
Defined.



Definition star_term {gamma} : raw_term Sig gamma.
Proof.
  refine (raw_symbol star _).
  intros.
  destruct i.
Defined.

Definition pair_term {gamma : scope_carrier DeBruijn} (a b : raw_term Sig (scope_sum gamma 0%nat)) : raw_term Sig gamma.
Proof.
  refine (raw_symbol pairs _).
  intros.
  destruct i.
  - refine a.
  - refine b.
Defined.

Definition el_Sigma_term {gamma : scope_carrier DeBruijn} (d : raw_term Sig (scope_sum gamma 0%nat)) (m : raw_term Sig (scope_sum gamma 2%nat)) : raw_term Sig gamma.
Proof.
  refine (raw_symbol el_Sigma _).
  intros.
  destruct i.
  - refine d.
  - refine m.
Defined.

Definition eq_term {gamma : scope_carrier DeBruijn} (C : raw_type Sig (scope_sum gamma 0%nat)) (c : raw_term Sig (scope_sum gamma 0%nat)) : raw_term Sig gamma.
Proof.
  refine (raw_symbol eq _).
  intros.
  destruct i.
  - refine C.
  - refine c.
Defined.




Inductive eval_type {gamma} : raw_type Sig gamma -> raw_type Sig gamma -> Type :=
  | Terminal_eval : eval_type Terminal_type Terminal_type
  | Sigma_eval A B : eval_type (Sigma_type A B) (Sigma_type A B)
  | Eq_eval A a b : eval_type (Eq_type A a b) (Eq_type A a b).



Inductive eval_term {gamma} : raw_term Sig gamma -> raw_term Sig gamma -> Type :=
  | star_eval : eval_term star_term star_term
  | pair_eval1 a b : eval_term (pair_term a b) (pair_term a b)
  (* pair_eval2 a b c d g m : eval_term c (pair_term a b) -> eval_term m g -> eval_term (el_Sigma_term d m) g *)
  | equ_eval C c : eval_term (eq_term C c) (eq_term C c).

  Local Unset Elimination Schemes.

  Print Context.empty.

  Set Asymmetric Patterns.

Lemma eval_canon_tm (c : raw_term Sig 0%nat) g:
  eval_term c g -> (g = star_term) + (exists a b, g = pair_term a b) + (exists a A, g = eq_term A a).
Proof.
  intros.
  destruct X.
Admitted.

Lemma eval_canon_ty (C : raw_type Sig 0%nat) G:
  eval_type C G -> (G = Terminal_type) + (exists A B, G = Sigma_type A B) + (exists a b A, G = Eq_type A a b).
Proof.
Admitted.

Inductive computable : judgement Sig -> Type :=
  | ty_comp A : derivable [! [: :] |- A !] ->
                (exists G, 
                eval_type A G /\
                derivable [! [: :] |- A ≡ G !] /\
                (forall A1 A2, G = Sigma_type A1 A2 -> computable [! [: :] |- A1 !] /\ computable [! [: A1 :] |- A2 !]) /\
                (forall A1 b d, G = Eq_type A1 b d -> computable [! [: :] |- A1 !] /\ computable [! [: :] |- b ; A1 !] /\ computable [! [: :] |- d ; A1 !])) ->
                computable [! [: :] |- A !]
  | tyeq_comp A B : derivable [! [: :] |- A ≡ B !] ->
                    computable [! [: :] |- A !] /\ computable [! [: :] |- B !] /\
                    (exists GA GB, 
                    eval_type A GA /\ eval_type B GB /\
                    (forall A1 A2 B1 B2, (GA = Sigma_type A1 A2 <-> GB = Sigma_type B1 B2) /\ (GA = Sigma_type A1 A2 -> computable [! [: :] |- A1 ≡ B1 !] /\ computable [! [: A1 :] |- A2 ≡ B2 !])) /\
                    (forall A1 B1 a b c d, (GA = Eq_type A1 a c <-> GB = Eq_type B1 b d)  /\ (GA = Eq_type A1 a c -> computable [! [: :] |- A1 ≡ B1 !] /\ computable [! [: :] |- a ≡ b ; A1 !] /\ computable [! [: :] |- c ≡ d ; A1 !])) /\ 
                    (GA = Terminal_type <-> GB = Terminal_type)) ->
                    computable [! [: :] |- A ≡ B !]
  | tm_comp c A : derivable [! [: :] |- c ; A !] ->
                  computable [! [: :] |- A !] /\
                  (exists G g, 
                  eval_type A G /\
                  eval_term c g /\
                  derivable [! [: :] |- c ≡ g ; A !] /\
                  (forall A1 A2 a b, (G = Sigma_type A1 A2 <-> g = pair_term a b) /\ (G = Sigma_type A1 A2 -> computable [! [: :] |- a ; A1 !] /\ computable [! [: :] |- b ; substitute (fun _ => a) A2 !])) /\
                  (forall A1 b c d, (G = Eq_type A1 b d <-> g = eq_term A1 c) /\ (G = Eq_type A1 b d -> computable [! [: :] |- b ≡ d ; A1 !])) /\
                  (G = Terminal_type <-> g = star_term)) ->
                  computable [! [: :] |- c ; A !]
  | tmeq_comp A a b : derivable [! [: :] |- a ≡ b ; A !] ->
                    computable [! [: :] |- a ; A !] /\ computable [! [: :] |- b ; A !] /\
                    (exists G ga gb, 
                    eval_type A G /\ eval_term a ga /\ eval_term b gb /\
                    (forall A1 A2 a1 a2 b1 b2, (G = Sigma_type A1 A2 <-> ga = pair_term a1 a2 /\ gb = pair_term b1 b2) /\ (G = Sigma_type A1 A2 -> computable [! [: :] |- a1 ≡ b1 ; A1 !] /\ computable [! [: :] |- a2 ≡ b2 ; substitute (fun _ => a1) A2 !])) /\
                    (forall A1 b c d f, (G = Eq_type A1 c d <-> ga = eq_term A1 b /\ gb = eq_term A1 f) /\ (G = Eq_type A1 c d -> computable [! [: :] |- c ≡ d ; A1 !])) /\
                    (G = Terminal_type <-> ga = star_term /\ gb = star_term))
                    ->
                    computable [! [: :] |- a ≡ b ; A !].
  (*| ty_comp_ass Gamma B : derivable [! Gamma |- B !] -> (forall s : raw_substitution Sig 0%nat Gamma, computable [! [: :] |- substitute s B !]) -> computable [! Gamma |- B !] *)

  Scheme computable_ind := Induction for computable Sort Type.
  Scheme computable_rec := Minimality for computable Sort Type.
  Definition computable_rect := computable_ind.

