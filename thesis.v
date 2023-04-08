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
  | Terminal_symbol | star_symbol | Sigma_symbol | pairs_symbol | el_Sigma_symbol | Eq_symbol | eq_symbol | Qtr_symbol | class_symbol | el_Qtr_symbol.

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
  - refine (class_type, [< (class_type, 0%nat) >]). (* Qtr *)
  - refine (class_term, [< (class_term, 0%nat) >]). (* class *)
  - refine (class_term, [< (class_term, 1%nat); (class_term, 0%nat) >]). (* el_Qtr *)
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

Definition Qtr : family_index Sig.
Proof.
  refine Qtr_symbol.
Defined.

Definition class : family_index Sig.
Proof.
  refine class_symbol.
Defined.

Definition el_Qtr : family_index Sig.
Proof.
  refine el_Qtr_symbol.
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


Section Sigma_type.

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

Section F_Sigma_eq.

Inductive metas_F_Sigma_eq : Type := B_F_Sigma_eq_symbol | C_F_Sigma_eq_symbol | D_F_Sigma_eq_symbol | E_F_Sigma_eq_symbol.

Let metas : arity DeBruijn.
Proof.
  exists metas_F_Sigma_eq.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
Defined.

Let B : family_index metas.
Proof.
  refine B_F_Sigma_eq_symbol.
Defined.

Let C : family_index metas.
Proof.
  refine C_F_Sigma_eq_symbol.
Defined.

Let D : family_index metas.
Proof.
  refine D_F_Sigma_eq_symbol.
Defined.

Let E : family_index metas.
Proof.
  refine E_F_Sigma_eq_symbol.
Defined.



Definition F_Sigma_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
    + refine {| form_of_judgement := form_equality class_type; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
          apply zero_db.
        * refine (raw_symbol (include_metavariable E) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
          apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
    + refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable D) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable E) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
Defined.

End F_Sigma_eq.






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


Section I_Sigma_eq.

Inductive metas_I_Sigma_eq : Type := B_I_Sigma_eq_symbol | C_I_Sigma_eq_symbol | b_I_Sigma_eq_symbol | c_I_Sigma_eq_symbol | d_I_Sigma_eq_symbol | e_I_Sigma_eq_symbol.

Let metas : arity DeBruijn.
Proof.
  exists metas_I_Sigma_eq.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Let B : family_index metas.
Proof.
  refine B_I_Sigma_eq_symbol.
Defined.

Let C : family_index metas.
Proof.
  refine C_I_Sigma_eq_symbol.
Defined.

Let b : family_index metas.
Proof.
  refine b_I_Sigma_eq_symbol.
Defined.

Let c : family_index metas.
Proof.
  refine c_I_Sigma_eq_symbol.
Defined.

Let d : family_index metas.
Proof.
  refine d_I_Sigma_eq_symbol.
Defined.

Let e : family_index metas.
Proof.
  refine e_I_Sigma_eq_symbol.
Defined.



Definition I_Sigma_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable e) (Metavariable.empty_args scope_is_empty)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
    + refine (raw_symbol (include_symbol pairs) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_symbol pairs) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable e) (Metavariable.empty_args scope_is_empty)).  
Defined.

End I_Sigma_eq.


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


Definition app_terms {gamma : scope_carrier DeBruijn} (m : raw_term Sig (scope_sum gamma 2%nat)) (b c : raw_term Sig (scope_sum gamma 0%nat)) : raw_term Sig gamma.
Proof.
  refine (instantiate_expression (_ _) (raw_symbol (include_metavariable m_E_Sigma) _)).
  intros.
  destruct i.
  - refine d.
  - refine m.
Defined.

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


Section E_Sigma_eq.

Inductive metas_E_Sigma_eq : Type := B_E_Sigma_eq_symbol | C_E_Sigma_eq_symbol | M_E_Sigma_eq_symbol | d_E_Sigma_eq_symbol | d'_E_Sigma_eq_symbol | m_E_Sigma_eq_symbol | m'_E_Sigma_eq_symbol.

Let metas : arity DeBruijn.
Proof.
  exists metas_E_Sigma_eq.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_type, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 2%nat).
  - refine (class_term, 2%nat).
Defined.

Definition B : family_index metas.
Proof.
  refine B_E_Sigma_eq_symbol.
Defined.

Definition C : family_index metas.
Proof.
  refine C_E_Sigma_eq_symbol.
Defined.

Definition M : family_index metas.
Proof.
  refine M_E_Sigma_eq_symbol.
Defined.

Definition d : family_index metas.
Proof.
  refine d_E_Sigma_eq_symbol.
Defined.

Definition d' : family_index metas.
Proof.
  refine d'_E_Sigma_eq_symbol.
Defined.

Definition m : family_index metas.
Proof.
  refine m_E_Sigma_eq_symbol.
Defined.

Definition m' : family_index metas.
Proof.
  refine m'_E_Sigma_eq_symbol.
Defined.


Definition E_Sigma_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_symbol Sigma) _).
        intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
           apply (zero_db).
      * refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        refine (raw_symbol (include_metavariable M) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply (zero_db).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol Sigma) _).
        intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
          apply zero_db.
      * refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable d') (Metavariable.empty_args scope_is_empty)).
    + simple refine {| context_of_judgement := [: _; _:]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
      * refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable M) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
           refine (raw_symbol (include_symbol pairs) _).
           intros. recursive_destruct i.
           ++ refine (raw_variable _).
              apply zero_db.
           ++ refine (raw_variable _).
              apply (succ_db zero_db).
        -- refine (raw_symbol (include_metavariable m) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
          ++ apply zero_db.
          ++ apply (succ_db zero_db).
        -- refine (raw_symbol (include_metavariable m') (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
          ++ apply zero_db.
          ++ apply (succ_db zero_db). 
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable M) _).
      intros.
      refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_symbol el_Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable m) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
      ++ apply zero_db.
      ++ apply (succ_db zero_db).
      + refine (raw_symbol (include_symbol el_Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable d') (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable m') (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
      ++ apply zero_db.
      ++ apply (succ_db zero_db).
Defined.

End E_Sigma_eq.

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

End Sigma_type.


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


Section F_Eq_eq.

Inductive metas_F_Eq_eq : Type := C_F_Eq_eq | c_F_Eq_eq | d_F_Eq_eq | E_F_Eq_eq | e_F_Eq_eq | f_F_Eq_eq.

Let metas : arity DeBruijn.
Proof.
  exists metas_F_Eq_eq.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Let C : family_index metas.
Proof.
  refine C_F_Eq_eq.
Defined.

Let E : family_index metas.
Proof.
  refine E_F_Eq_eq.
Defined.

Let c : family_index metas.
Proof.
  refine c_F_Eq_eq.
Defined.

Let d : family_index metas.
Proof.
  refine d_F_Eq_eq.
Defined.

Let e : family_index metas.
Proof.
  refine e_F_Eq_eq.
Defined.

Let f : family_index metas.
Proof.
  refine f_F_Eq_eq.
Defined.


Definition F_Eq_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable E) (empty_rect _ scope_is_empty _)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable e) (empty_rect _ scope_is_empty _)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable d) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable f) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    * refine (raw_symbol (include_symbol Eq) _).
      intros. recursive_destruct i.
      + refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      + refine (raw_symbol (include_metavariable c) (empty_rect _ scope_is_empty _)).
      + refine (raw_symbol (include_metavariable d) (empty_rect _ scope_is_empty _)).
    * refine (raw_symbol (include_symbol Eq) _).
      intros. recursive_destruct i.
      + refine (raw_symbol (include_metavariable E) (empty_rect _ scope_is_empty _)).
      + refine (raw_symbol (include_metavariable e) (empty_rect _ scope_is_empty _)).
      + refine (raw_symbol (include_metavariable f) (empty_rect _ scope_is_empty _)).
Defined.

End F_Eq_eq.



Inductive metas_I_Eq_symbols : Type := C_I_Eq_symbol | c_I_Eq_symbol.

Definition metas_I_Eq : arity DeBruijn.
Proof.
  exists metas_I_Eq_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Definition C_I_Eq : family_index metas_I_Eq.
Proof.
  refine C_I_Eq_symbol.
Defined.

Definition c_I_Eq : family_index metas_I_Eq.
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


Section I_Eq_eq.

Inductive metas_I_Eq_eq : Type := c_I_Eq_eq | d_I_Eq_eq | C_I_Eq_eq .

Let metas : arity DeBruijn.
Proof.
  exists metas_I_Eq_eq.
  intros.
  induction H.
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_type, 0%nat).
Defined.

Let C : family_index metas.
Proof.
  refine C_I_Eq_eq.
Defined.

Let c : family_index metas.
Proof.
  refine c_I_Eq_eq.
Defined.

Let d : family_index metas.
Proof.
  refine d_I_Eq_eq.
Defined.



Definition I_Eq_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable C) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable c) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Eq) _).
      intros.
      recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol eq) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable c) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol eq) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (empty_rect _ scope_is_empty _)).
      * refine (raw_symbol (include_metavariable d) (empty_rect _ scope_is_empty _)).
Defined.

End I_Eq_eq.

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


Section F_Qtr.

Inductive metas_F_Qtr : Type := A_F_Qtr.

Let metas : arity DeBruijn.
Proof.
  exists metas_F_Qtr.
  intros.
  induction X.
  refine (class_type, 0%nat).
Defined.

Let A : family_index metas.
Proof.
  refine A_F_Qtr.
Defined.

Definition F_Qtr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _ >]; raw_rule_conclusion := _ |}.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    refine (raw_symbol (include_symbol Qtr) _).
    intros. recursive_destruct i.
    refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
Defined.

End F_Qtr.


Section F_Qtr_eq.

Inductive metas_F_Qtr_eq : Type := A_F_Qtr_eq | B_F_Qtr_eq.

Let metas : arity DeBruijn.
Proof.
  exists metas_F_Qtr_eq.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 0%nat).
Defined.

Let A : family_index metas.
Proof.
  refine A_F_Qtr_eq.
Defined.

Let B : family_index metas.
Proof.
  refine B_F_Qtr_eq.
Defined.

Definition F_Qtr_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _ >]; raw_rule_conclusion := _ |}.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable B) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable B) (empty_rect _ scope_is_empty _)).
Defined.

End F_Qtr_eq.


Section I_Qtr.

Inductive metas_I_Qtr : Type := A_I_Qtr | a_I_Qtr.

Let metas : arity DeBruijn.
Proof.
  exists metas_I_Qtr.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Let A : family_index metas.
Proof.
  refine A_I_Qtr.
Defined.

Let a : family_index metas.
Proof.
  refine a_I_Qtr.
Defined.


Definition I_Qtr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _ >]; raw_rule_conclusion := _ |}.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol class) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
Defined.

End I_Qtr.


Section eq_Qtr.

Inductive metas_eq_Qtr : Type := A_eq_Qtr | a_eq_Qtr | b_eq_Qtr.

Let metas : arity DeBruijn.
Proof.
  exists metas_eq_Qtr.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Let A : family_index metas.
Proof.
  refine A_eq_Qtr.
Defined.

Let a : family_index metas.
Proof.
  refine a_eq_Qtr.
Defined.

Let b : family_index metas.
Proof.
  refine b_eq_Qtr.
Defined.


Definition eq_Qtr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _; _ >]; raw_rule_conclusion := _ |}.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable b) (empty_rect _ scope_is_empty _)).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol class) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol class) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable b) (empty_rect _ scope_is_empty _)).
Defined.

End eq_Qtr.


Section E_Qtr.

Inductive metas_E_Qtr : Type := L_E_Qtr | A_E_Qtr | p_E_Qtr | l_E_Qtr.

Let metas : arity DeBruijn.
Proof.
  exists metas_E_Qtr.
  intros.
  induction H.
  - refine (class_type, 1%nat).
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 1%nat).
Defined.

Let L : family_index metas.
Proof.
  refine L_E_Qtr.
Defined.

Let A : family_index metas.
Proof.
  refine A_E_Qtr.
Defined.

Let p : family_index metas.
Proof.
  refine p_E_Qtr.
Defined.

Let l : family_index metas.
Proof.
  refine l_E_Qtr.
Defined.


Definition E_Qtr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _; _; _; _ >]; raw_rule_conclusion := _ |}.
  - simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (empty_rect _ scope_is_empty _) (raw_variable _))).
      apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable p) (empty_rect _ scope_is_empty _)).
  - simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
  - simple refine {| context_of_judgement := [: _; _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply (succ_db zero_db).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
      refine (raw_symbol (include_metavariable p) (empty_rect _ scope_is_empty _)).  
    + refine (raw_symbol (include_symbol el_Qtr) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable p) (empty_rect _ scope_is_empty _)).  
Defined.

End E_Qtr.



Section E_Qtr_eq.

Inductive metas_E_Qtr_eq : Type := L_E_Qtr_eq | A_E_Qtr_eq | p_E_Qtr_eq | l_E_Qtr_eq | p'_E_Qtr_eq | l'_E_Qtr_eq.

Let metas : arity DeBruijn.
Proof.
  exists metas_E_Qtr_eq.
  intros.
  induction H.
  - refine (class_type, 1%nat).
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 1%nat).
Defined.

Let L : family_index metas.
Proof.
  refine L_E_Qtr_eq.
Defined.

Let A : family_index metas.
Proof.
  refine A_E_Qtr_eq.
Defined.

Let p : family_index metas.
Proof.
  refine p_E_Qtr_eq.
Defined.

Let l : family_index metas.
Proof.
  refine l_E_Qtr_eq.
Defined.

Let p' : family_index metas.
Proof.
  refine p'_E_Qtr_eq.
Defined.

Let l' : family_index metas.
Proof.
  refine l'_E_Qtr_eq.
Defined.

Definition E_Qtr_eq : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _; _; _; _ >]; raw_rule_conclusion := _ |}.
  - simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (empty_rect _ scope_is_empty _) (raw_variable _))).
      apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable p) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable p') (empty_rect _ scope_is_empty _)).
  - simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l') (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
  - simple refine {| context_of_judgement := [: _; _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply (succ_db zero_db).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
      refine (raw_symbol (include_metavariable p) (empty_rect _ scope_is_empty _)).  
    + refine (raw_symbol (include_symbol el_Qtr) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable p) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol el_Qtr) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable l') (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable p') (empty_rect _ scope_is_empty _)).
Defined.

End E_Qtr_eq.


Section C_Qtr.

Inductive metas_C_Qtr : Type := L_C_Qtr | A_C_Qtr | a_C_Qtr | l_C_Qtr.

Let metas : arity DeBruijn.
Proof.
  exists metas_C_Qtr.
  intros.
  induction H.
  - refine (class_type, 1%nat).
  - refine (class_type, 0%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 1%nat).
Defined.

Let L : family_index metas.
Proof.
  refine L_C_Qtr.
Defined.

Let A : family_index metas.
Proof.
  refine A_C_Qtr.
Defined.

Let a : family_index metas.
Proof.
  refine a_C_Qtr.
Defined.

Let l : family_index metas.
Proof.
  refine l_C_Qtr.
Defined.


Definition C_Qtr : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := [< _; _; _; _ >]; raw_rule_conclusion := _ |}.
  - simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_symbol Qtr) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (empty_rect _ scope_is_empty _) (raw_variable _))).
      apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
  - simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
  - simple refine {| context_of_judgement := [: _; _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable A) (empty_rect _ scope_is_empty _)).
    + refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply (succ_db zero_db).
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable L) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
      refine (raw_symbol (include_symbol class) _).
      intros. recursive_destruct i.
      refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_symbol el_Qtr) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_variable _).
        apply zero_db.
      * refine (raw_symbol (include_symbol class) _).
        intros. recursive_destruct i.
        refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
    + refine (raw_symbol (include_metavariable l) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
      refine (raw_symbol (include_metavariable a) (empty_rect _ scope_is_empty _)).
Defined.

End C_Qtr.


Inductive rule_indexes := F_Tr_index | I_Tr_index | C_Tr_index 
                        | F_Sigma_index | F_Sigma_eq_index | I_Sigma_index | I_Sigma_eq_index | E_Sigma_index | E_Sigma_eq_index | C_Sigma_index 
                        | F_Eq_index | F_Eq_eq_index | I_Eq_index | I_Eq_eq_index | E_Eq_index | C_Eq_index
                        | F_Qtr_index | F_Qtr_eq_index | I_Qtr_index | eq_Qtr_index | E_Qtr_index | E_Qtr_eq_index | C_Qtr_index.




Definition TReg : raw_type_theory Sig.
Proof.
  exists rule_indexes.
  intros.
  induction H.
  - refine F_Tr.
  - refine I_Tr. 
  - refine C_Tr.
  - refine F_Sigma.
  - refine F_Sigma_eq.  
  - refine I_Sigma.
  - refine I_Sigma_eq.
  - refine E_Sigma.
  - refine E_Sigma_eq.
  - refine C_Sigma.
  - refine F_Eq.
  - refine F_Eq_eq.
  - refine I_Eq.
  - refine I_Eq_eq.
  - refine E_Eq.
  - refine C_Eq.
  - refine F_Qtr.
  - refine F_Qtr_eq.  
  - refine I_Qtr.
  - refine eq_Qtr.
  - refine E_Qtr.
  - refine E_Qtr_eq.
  - refine C_Qtr.
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

End Eq_type.

Definition Qtr_type {gamma : scope_carrier DeBruijn} (A : raw_type Sig (scope_sum gamma 0%nat)) : raw_type Sig gamma.
Proof.
  refine (raw_symbol Qtr _).
  intros.
  recursive_destruct i.
  refine A.
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
  | Eq_eval A a b : eval_type (Eq_type A a b) (Eq_type A a b)
  | Qtr_eval A : eval_type (Qtr_type A) (Qtr_type A).



Inductive eval_term {gamma} : raw_term Sig gamma -> raw_term Sig gamma -> Type :=
  | star_eval : eval_term star_term star_term
  | pair_eval1 a b : eval_term (pair_term a b) (pair_term a b)
  | pair_eval2 d b c g (m : raw_term Sig (scope_sum gamma 2%nat)) m_app : eval_term d (pair_term b c) -> eval_term m_app g -> eval_term (el_Sigma_term d m) g
  | equ_eval C c : eval_term (eq_term C c) (eq_term C c).

Local Unset Elimination Schemes.

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

