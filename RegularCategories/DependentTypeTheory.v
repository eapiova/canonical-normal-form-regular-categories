
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

(** THE TYPE THEORY OF REGULAR CATEGORIES *)

(* The signature of the theory *)

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



(* The logical rules of the theory *)


(* Terminal type rules *)


(* Formation rule *)

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


(* Introduction rule *)

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


(* Conversion rule *)

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


(* Indexed sum rules *)

(* Formation rules *)

Section F_Sigma.

Inductive metas_F_Sigma_symbols : Type := B_F_Sigma_symbol | C_F_Sigma_symbol.

Let metas : arity DeBruijn.
Proof.
  exists metas_F_Sigma_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
Defined.

Let B : family_index metas.
Proof.
  refine B_F_Sigma_symbol.
Defined.

Let C : family_index metas.
Proof.
  refine C_F_Sigma_symbol.
Defined.

Definition F_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _ >].
    simple refine {| context_of_judgement := [: _ :]; hypothetical_part := _ |}.
    + refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
    + refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
        apply zero_db.
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_type; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    refine (raw_symbol (include_symbol Sigma) _).
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
Defined.

Definition F_Sigma_eq := raw_congruence_rule F_Sigma tt.

End F_Sigma.


(* Introduction rules *)

Section I_Sigma.

Inductive metas_I_Sigma_symbols : Type := B_I_Sigma_symbol | C_I_Sigma_symbol | b_I_Sigma_symbol | c_I_Sigma_symbol.

Let metas : arity DeBruijn.
Proof.
  exists metas_I_Sigma_symbols.
  intros.
  induction H.
  - refine (class_type, 0%nat).
  - refine (class_type, 1%nat).
  - refine (class_term, 0%nat).
  - refine (class_term, 0%nat).
Defined.

Let B : family_index metas.
Proof.
  refine B_I_Sigma_symbol.
Defined.

Let C : family_index metas.
Proof.
  refine C_I_Sigma_symbol.
Defined.

Let b : family_index metas.
Proof.
  refine b_I_Sigma_symbol.
Defined.

Let c : family_index metas.
Proof.
  refine c_I_Sigma_symbol.
Defined.


Definition I_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _ >].
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
    + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
        refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
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
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
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
Defined.

Definition I_Sigma_eq := raw_congruence_rule I_Sigma tt.

End I_Sigma.


(* Elimination rules *)

Section E_Sigma.

Inductive metas_E_Sigma_symbols : Type := B_E_Sigma_symbol | C_E_Sigma_symbol | M_E_Sigma_symbol | d_E_Sigma_symbol | m_E_Sigma_symbol .

Let metas : arity DeBruijn.
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

Let B : family_index metas.
Proof.
  refine B_E_Sigma_symbol.
Defined.

Let C : family_index metas.
Proof.
  refine C_E_Sigma_symbol.
Defined.

Let M : family_index metas.
Proof.
  refine M_E_Sigma_symbol.
Defined.

Let d : family_index metas.
Proof.
  refine d_E_Sigma_symbol.
Defined.

Let m : family_index metas.
Proof.
  refine m_E_Sigma_symbol.
Defined.

Definition E_Sigma : raw_rule Sig.
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
      refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
      unfold hypothetical_judgement_expressions.
      intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol Sigma) _).
      intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
          apply zero_db.
      * refine (raw_symbol (include_metavariable d) (Metavariable.empty_args scope_is_empty)).
    + simple refine {| context_of_judgement := [: _; _:]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
      * refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
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
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
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
Defined.

Definition E_Sigma_eq := raw_congruence_rule E_Sigma tt.

End E_Sigma.


(* Conversion rule *)

Section C_Sigma.

Inductive metas_C_Sigma_symbols : Type := B_C_Sigma_symbol | C_C_Sigma_symbol | M_C_Sigma_symbol | b_C_Sigma_symbol | c_C_Sigma_symbol | m_C_Sigma_symbol .

Let metas : arity DeBruijn.
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

Let B : family_index metas.
Proof.
  refine B_C_Sigma_symbol.
Defined.

Let C : family_index metas.
Proof.
  refine C_C_Sigma_symbol.
Defined.

Let M : family_index metas.
Proof.
  refine M_C_Sigma_symbol.
Defined.

Let b : family_index metas.
Proof.
  refine b_C_Sigma_symbol.
Defined.

Let c : family_index metas.
Proof.
  refine c_C_Sigma_symbol.
Defined.

Let m : family_index metas.
Proof.
  refine m_C_Sigma_symbol.
Defined.


Definition C_Sigma : raw_rule Sig.
Proof.
  refine {| raw_rule_metas := metas; raw_rule_premise := _; raw_rule_conclusion := _ |}.
  - refine [< _; _; _; _ >].
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
        refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
        * refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      + refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
        refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
        unfold hypothetical_judgement_expressions.
        intros. recursive_destruct i.
        * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _)).
          refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
        * refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
    + simple refine {| context_of_judgement := [: _; _:]; hypothetical_part := _ |}.
      * refine (raw_symbol (include_metavariable B) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable C) (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _))).
      apply zero_db.
      * refine {| form_of_judgement := form_object class_term; judgement_expression := _ |}.
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
  - refine {| context_of_judgement := [: :]; hypothetical_part := _ |}.
    refine {| form_of_judgement := form_equality class_term; judgement_expression := _ |}.
    unfold hypothetical_judgement_expressions.
    intros. recursive_destruct i.
    + refine (raw_symbol (include_metavariable M) _).
      intros.
      refine (raw_symbol (include_symbol pairs) _).
      intros. recursive_destruct i0.
      * refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
    + refine (raw_symbol (include_symbol el_Sigma) _).
      intros. recursive_destruct i.
      * refine (raw_symbol (include_symbol pairs) _).
        intros. recursive_destruct i.
        -- refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
        -- refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
      * refine (raw_symbol (include_metavariable m) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) (raw_variable _)) (raw_variable _))).
        ++ apply zero_db.
        ++ apply (succ_db zero_db).
    + refine (raw_symbol (include_metavariable m) (Metavariable.extend_args (Metavariable.extend_args (Metavariable.empty_args scope_is_empty) _) _)).
      ++ refine (raw_symbol (include_metavariable b) (Metavariable.empty_args scope_is_empty)).
      ++ refine (raw_symbol (include_metavariable c) (Metavariable.empty_args scope_is_empty)).
Defined.

End C_Sigma.




(* Extensional equality type rules *)

(* Formation rules *)

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

Definition F_Eq_eq := raw_congruence_rule F_Eq tt.


(* Introduction rules *)

Section I_Eq.

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

Definition I_Eq_eq := raw_congruence_rule I_Eq tt.

End I_Eq.


(* Elimination rules *)

Section E_Eq.

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

End E_Eq.


(* Conversion rule *)

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



(* Quotients on terminal type rules *)


(* Formation rules *)

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

Definition F_Qtr_eq := raw_congruence_rule F_Qtr tt.

End F_Qtr.


(* Introduction rules *)

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


(* Elimination rules *)

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

Definition E_Qtr_eq := raw_congruence_rule E_Qtr tt.

End E_Qtr.


(* Conversion rule *)

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


(* TReg is a type theory with structural rules built in, we only have to submit the logical rules *)

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


(* Notion of derivable judgement *)

Definition derivable J := exists H, RawTypeTheory.derivation TReg H J.


(* We give names to canonical types and canonical elements *)

Definition Terminal_type {gamma} : raw_type Sig gamma.
Proof.
  refine (raw_symbol Terminal _).
  intros.
  destruct i.
Defined.


Section Sigma_type.

Definition Sigma_type {gamma : scope_carrier DeBruijn} (A : raw_type Sig gamma) (B : raw_type Sig (scope_sum gamma 1%nat)) : raw_type Sig gamma.
Proof.
  refine (raw_symbol Sigma _).
  intros.
  recursive_destruct i.
  - unfold argument_scope. simpl. rewrite <- add_n_O. refine A.
  - refine B.
Defined.

End Sigma_type.


Section Eq_type.

Definition Eq_type {gamma : scope_carrier DeBruijn} (A : raw_type Sig gamma) (a b : raw_term Sig gamma) : raw_type Sig gamma.
Proof.
  refine (raw_symbol Eq _).
  intros.
  recursive_destruct i.
  - unfold argument_scope; simpl; rewrite <- add_n_O; refine A.
  - unfold argument_scope; simpl; rewrite <- add_n_O; refine a.
  - unfold argument_scope; simpl; rewrite <- add_n_O; refine b.
Defined.

End Eq_type.

Definition Qtr_type {gamma : scope_carrier DeBruijn} (A : raw_type Sig gamma) : raw_type Sig gamma.
Proof.
  refine (raw_symbol Qtr _).
  intros.
  recursive_destruct i.
  unfold argument_scope; simpl; rewrite <- add_n_O; refine A.
Defined.



Definition star_term {gamma} : raw_term Sig gamma.
Proof.
  refine (raw_symbol star _).
  intros.
  destruct i.
Defined.

Definition pair_term {gamma : scope_carrier DeBruijn} (a b : raw_term Sig gamma) : raw_term Sig gamma.
Proof.
  refine (raw_symbol pairs _).
  intros.
  destruct i.
  - destruct f; unfold argument_scope; simpl; rewrite <- add_n_O; refine a.
  - unfold argument_scope; simpl; rewrite <- add_n_O; refine b.
Defined.

Definition el_Sigma_term {gamma : scope_carrier DeBruijn} (d : raw_term Sig gamma) (m : raw_term Sig (scope_sum gamma 2%nat)) : raw_term Sig gamma.
Proof.
  refine (raw_symbol el_Sigma _).
  intros.
  destruct i.
  - destruct f. unfold argument_scope. simpl. rewrite <- add_n_O. refine d.
  - refine m.
Defined.

Definition eq_term {gamma : scope_carrier DeBruijn} (C : raw_type Sig gamma) (c : raw_term Sig gamma) : raw_term Sig gamma.
Proof.
  refine (raw_symbol eq _).
  intros.
  destruct i.
  - destruct f. unfold argument_scope. simpl. rewrite <- add_n_O. refine C.
  - unfold argument_scope. simpl. rewrite <- add_n_O. refine c.
Defined.

Definition class_term {gamma : scope_carrier DeBruijn} (a : raw_term Sig gamma) : raw_term Sig gamma.
Proof.
  refine (raw_symbol class _).
  intros.
  destruct i.
  unfold argument_scope; simpl; rewrite <- add_n_O; refine a.
Defined.

Definition el_Qtr_term {gamma : scope_carrier DeBruijn} (l : raw_term Sig ((gamma+1)%nat)) (p : raw_term Sig gamma) : raw_term Sig gamma.
Proof.
  refine (raw_symbol el_Qtr _).
  intros.
  destruct i.
  - refine l.
  - unfold argument_scope. simpl. rewrite <- add_n_O. refine p.
Defined.


Definition sigma_subst {gamma : scope_carrier DeBruijn} (b c : raw_term Sig gamma): raw_substitution Sig gamma (scope_sum gamma 2%nat).
Proof.
  unfold raw_substitution.
  intros.
  destruct X.
  - apply b.
  - apply c.
Defined.

Definition qtr_subst {gamma : scope_carrier DeBruijn} (a : raw_term Sig gamma): raw_substitution Sig gamma (scope_sum gamma 1%nat).
Proof.
  unfold raw_substitution.
  intros.
  destruct X; apply a.
Defined.



(* We assume function extensionality, which is not given for free in proof assistants *)

Context `{Funext}.

Definition empty_instantiation Gamma : Metavariable.instantiation [< >] Sig Gamma. 
Proof.
  unfold Metavariable.instantiation.
  intros.
  destruct i.
Defined.


(* 
  Technical lemmas which says that if the premise judgments of a rule of the theory are derivable then the conclusion judgment is also derivable 
  This is trivial since rules of the theory are derivable inside the same theory, but they take time to prove them.
  Only the proof for F_Tr and I_Tr is shown
*)

Lemma refl_ty_derivable_empty_context A :
  derivable [! [: :] |- A !] -> derivable [! [: :] |- A ≡ A!].
Proof.
Admitted.

Lemma refl_tm_derivable_empty_context a A :
  derivable [! [: :] |- a ; A !] -> derivable [! [: :] |- a ≡ a ; A!].
Proof.
Admitted.

Lemma F_Tr_derivable_empty_context :
  derivable [! [: :] |- Terminal_type !].
Proof.
  exists [< >].
  simple refine (Closure.deduce' _ _ _).
  + simple refine (inr (F_Tr_index; [::]; empty_instantiation [::])).
  + unfold Terminal_type. apply Judgement.eq_by_eta. simpl. apply Judgement.eq_by_expressions.
    * intros. apply DB_is_empty. apply i.
    * intros. simpl. destruct i; try reflexivity.
      apply ap. apply path_forall. unfold "==". intros.
        destruct x.
  + intros; destruct p.
Defined.

Lemma I_Tr_derivable_empty_context :
  derivable [! [: :] |- star_term ; Terminal_type !].
Proof.
  exists [< >].
  simple refine (Closure.deduce' _ _ _).
  + simple refine (inr (I_Tr_index; [::]; empty_instantiation [::])).
  + unfold Terminal_type. apply Judgement.eq_by_eta. simpl. apply Judgement.eq_by_expressions.
    * intros. apply DB_is_empty. apply i.
    * intros. simpl. destruct i; try reflexivity.
      -- destruct f. apply ap. apply path_forall. unfold "==". intros.
        destruct x.
      -- unfold star_term. apply ap. apply path_forall. unfold "==". intros.
      destruct x.
  + intros; destruct p.
Defined.

Lemma C_Tr_derivable_empty_context t :
  derivable [! [: :] |- t ; Terminal_type !] -> derivable [! [: :] |- t ≡ star_term ; Terminal_type !].
Proof.
  exists [< [! [: :] |- t ; Terminal_type !] >].
  simple refine (Closure.deduce' _ _ _).
  + simple refine (inr (C_Tr_index; [::]; _)).
    unfold Metavariable.instantiation.
    intros.
    destruct i.
    apply t.
  + unfold Terminal_type. apply Judgement.eq_by_eta. simpl. apply Judgement.eq_by_expressions.
    * intros. apply DB_is_empty. apply i.
    * intros. simpl. destruct i. -- destruct f. apply ap; apply path_forall; unfold "=="; intros. destruct x.
      -- admit.
      -- unfold star_term. apply ap; apply path_forall; unfold "=="; intros. destruct x.
  + intros; destruct p. admit.
Admitted.


Lemma F_Sigma_derivable_empty_context B C :
  derivable [! [::] |- B !] -> derivable [! [: B :] |- C !] -> derivable [! [::] |- Sigma_type B C !].
Proof.
Admitted.

Lemma F_Sigma_eq_derivable_empty_context B C D E:
  derivable [! [::] |- B ≡ D !] -> derivable [! [: B :] |- C ≡ E !] -> derivable [! [::] |- Sigma_type B C ≡ Sigma_type D E !].
Proof.
Admitted.

Lemma I_Sigma_derivable_empty_context b c B C :
  derivable [! [::] |- b ; B !] -> derivable [! [: :] |- c ; substitute (fun _ => b) C !] -> derivable [! [::] |- Sigma_type B C !] -> derivable [! [::] |- pair_term b c ; Sigma_type B C !].
Proof.
Admitted.

Lemma I_Sigma_eq_derivable_empty_context b c d e B C :
  derivable [! [::] |- b ≡ d ; B !] -> derivable [! [: :] |- c ≡ e ; substitute (fun _ => b) C !] -> derivable [! [::] |- Sigma_type B C !] -> derivable [! [::] |- pair_term b c ≡ pair_term d e ; Sigma_type B C !].
Proof.
Admitted.

Lemma E_Sigma_derivable_empty_context x y d (m : raw_term Sig 2%nat) B C M :
  derivable [! [: Sigma_type B C :] |- M !] -> derivable [! [: :] |- d ; Sigma_type B C !] -> derivable [! [: B ; C :] |- m ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> derivable [! [::] |- el_Sigma_term d m ; substitute (fun _ => d) M !].
Proof.
Admitted.

Lemma E_Sigma_eq_derivable_empty_context x y d d' (m m' : raw_term Sig 2%nat) B C M :
  derivable [! [: Sigma_type B C :] |- M !] -> derivable [! [: :] |- d ≡ d' ; Sigma_type B C !] -> derivable [! [: B ; C :] |- m ≡ m' ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> derivable [! [::] |- el_Sigma_term d m ≡ el_Sigma_term d' m' ; substitute (fun _ => d) M !].
Proof.
Admitted.

Lemma C_Sigma_derivable_empty_context b c x y (m : raw_term Sig 2%nat) B C M :
  derivable [! [: Sigma_type B C :] |- M !] -> derivable [! [: :] |- b ; B !] -> derivable [! [: :] |- c ; substitute (fun _ => b) C !] -> derivable [! [: B ; C :] |- m ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> derivable [! [::] |- el_Sigma_term (pair_term b c) m ≡ substitute (sigma_subst b c ) m ; substitute (fun _ => pair_term b c) M !].
Proof.
Admitted.

Lemma F_Eq_derivable_empty_context c d C :
  derivable [! [::] |- C !] -> derivable [! [: :] |- c ; C !] -> derivable [! [::] |- d ; C !] -> derivable [! [::] |- Eq_type C c d !].
Proof.
Admitted.

Lemma F_Eq_eq_derivable_empty_context c d e f C E :
  derivable [! [::] |- C ≡ E !] -> derivable [! [: :] |- c ≡ e ; C !] -> derivable [! [::] |- d ≡ f ; C !] -> derivable [! [::] |- Eq_type C c d ≡ Eq_type E e f !].
Proof.
Admitted.

Lemma I_Eq_derivable_empty_context c C :
  derivable [! [: :] |- c ; C !] -> derivable [! [: :] |- eq_term C c ; Eq_type C c c !].
Proof.
Admitted.

Lemma I_Eq_eq_derivable_empty_context c d C :
  derivable [! [: :] |- c ≡ d ; C !] -> derivable [! [: :] |- eq_term C c ≡ eq_term C d ; Eq_type C c c !].
Proof.
Admitted.

Lemma E_Eq_derivable_empty_context c d p C :
  derivable [! [::] |- p ; Eq_type C c d !] -> derivable [! [::] |- C !] -> derivable [! [: :] |- c ; C !] -> derivable [! [::] |- d ; C !] -> derivable [! [::] |- c ≡ d ; C !].
Proof.
Admitted.

Lemma C_Eq_derivable_empty_context c d p C :
  derivable [! [::] |- p ; Eq_type C c d !] -> derivable [! [::] |- p ≡ eq_term C c ; Eq_type C c d !].
Proof.
Admitted.

Lemma F_Qtr_derivable_empty_context A :
  derivable [! [::] |- A !] -> derivable [! [::] |- Qtr_type A !].
Proof.
Admitted.

Lemma F_Qtr_eq_derivable_empty_context A B :
  derivable [! [::] |- A ≡ B !] -> derivable [! [::] |- Qtr_type A ≡ Qtr_type B !].
Proof.
Admitted.

Lemma I_Qtr_derivable_empty_context a A :
  derivable [! [::] |- a ; A !] -> derivable [! [::] |- class_term a ; Qtr_type A !].
Proof.
Admitted.

Lemma eq_Qtr_derivable_empty_context a b A :
  derivable [! [::] |- a ; A !] -> derivable [! [: :] |- b ; A !] -> derivable [! [::] |- class_term a ≡ class_term b ; Qtr_type A !].
Proof.
Admitted.


(*
Lemma E_Qtr_derivable_empty_context A L l p x y d (m : raw_term Sig 2%nat) B C M :
  derivable [! [: Qtr_type A :] |- L !] -> derivable [! [: :] |- p ; Qtr_type A !] -> derivable [! [: A :] |- l ; substitute (fun z => class_term (raw_variable _)) L !] -> derivable [! [: A ; A :] |- l ≡ l ; substitute (fun z => class_term (raw_variable _)) L !] -> derivable [! [::] |- el_Qtr_term l p ; substitute (fun _ => p) L !].
Proof.
Admitted.

Lemma E_Sigma_eq_derivable_empty_context x y d d' (m m' : raw_term Sig 2%nat) B C M :
  derivable [! [: Sigma_type B C :] |- M !] -> derivable [! [: :] |- d ≡ d' ; Sigma_type B C !] -> derivable [! [: B ; C :] |- m ≡ m' ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> derivable [! [::] |- el_Sigma_term d m ≡ el_Sigma_term d' m' ; substitute (fun _ => d) M !].
Proof.
Admitted.

Lemma C_Sigma_derivable_empty_context b c x y (m : raw_term Sig 2%nat) B C M :
  derivable [! [: Sigma_type B C :] |- M !] -> derivable [! [: :] |- b ; B !] -> derivable [! [: :] |- c ; substitute (fun _ => b) C !] -> derivable [! [: B ; C :] |- m ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> derivable [! [::] |- el_Sigma_term (pair_term b c) m ≡ substitute (sigma_subst b c ) m ; substitute (fun _ => pair_term b c) M !].
Proof.
Admitted.
*)