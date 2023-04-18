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
From GeneralTT Require Import TypeTheory.








(* Computation/Operational semantics rules *)

Local Unset Elimination Schemes.

Set Asymmetric Patterns.

Inductive eval_type {gamma} : raw_type Sig gamma -> raw_type Sig gamma -> Type :=
  | Terminal_eval : eval_type Terminal_type Terminal_type
  | Sigma_eval A B : eval_type (Sigma_type A B) (Sigma_type A B)
  | Eq_eval A a b : eval_type (Eq_type A a b) (Eq_type A a b)
  | Qtr_eval A : eval_type (Qtr_type A) (Qtr_type A).

Inductive eval_term {gamma} : raw_term Sig gamma -> raw_term Sig gamma -> Type :=
  | star_eval : eval_term star_term star_term
  | pair_eval1 a b : eval_term (pair_term a b) (pair_term a b)
  | pair_eval2 d b c g (m : raw_term Sig (scope_sum gamma 2%nat)) : eval_term d (pair_term b c) -> eval_term (substitute (sigma_subst b c) m) g -> eval_term (el_Sigma_term d m) g  
  | equ_eval C c : eval_term (eq_term C c) (eq_term C c)
  | class_eval a : eval_term (class_term a) (class_term a)
  | class_eval2 a p (l : raw_term Sig (scope_sum gamma 1%nat)) g : eval_term p (class_term a) -> eval_term (substitute (qtr_subst a) l) g -> eval_term (el_Qtr_term l p) g.

  Scheme eval_ind := Induction for eval_term Sort Type.
  Scheme eval_rec := Minimality for eval_term Sort Type.
  Definition eval_term_rect := eval_ind.


(* Inversion lemmas for computation rules *)

Lemma eval_canon_tm (c : raw_term Sig 0%nat) g:
  eval_term c g -> (g = star_term) + (exists a b, g = pair_term a b) + (exists a A, g = eq_term A a) + (exists a, g = class_term a).
Proof.
  intros.
  induction X.
  - left. left. left. reflexivity.
  - left. left. right. exists a. exists b. reflexivity.
  - apply IHX2.
  - left. right. exists c. exists C. reflexivity.
  - right. exists a. reflexivity.
  - apply IHX2.
Defined.

Lemma eval_canon_ty (C : raw_type Sig 0%nat) G:
  eval_type C G -> (G = Terminal_type) + (exists A B, G = Sigma_type A B) + (exists a b A, G = Eq_type A a b) + (exists A, G = Qtr_type A).
Proof.
  intros.
  destruct X.
  - left. left. left. reflexivity.
  - left. left. right. exists A. exists B. reflexivity.
  - left. right. exists a. exists b. exists A. reflexivity.
  - right. exists A. reflexivity.
Defined.


(* Definition of computable judgement *)

Inductive computable : judgement Sig -> Type :=
  | ty_comp A : derivable [! [: :] |- A !] ->
                (exists G, 
                eval_type A G /\
                derivable [! [: :] |- A ≡ G !] /\
                ((G = Terminal_type) +
                (exists A1 A2, G = Sigma_type A1 A2 /\ computable [! [: :] |- A1 !] /\ computable [! [: A1 :] |- A2 !]) +
                (exists A1 b d, G = Eq_type A1 b d /\ computable [! [: :] |- A1 !] /\ computable [! [: :] |- b ; A1 !] /\ computable [! [: :] |- d ; A1 !]) +
                (exists C, G = Qtr_type C /\ computable [! [: :] |- C !]))) ->
                computable [! [: :] |- A !]
  | tyeq_comp A B : derivable [! [: :] |- A ≡ B !] ->
                    (computable [! [: :] |- A !] /\ computable [! [: :] |- B !]) /\
                    (exists GA GB, 
                    eval_type A GA /\ eval_type B GB /\
                    ((GA = Terminal_type /\ GB = Terminal_type) +
                    (exists A1 A2 B1 B2, (GA = Sigma_type A1 A2 /\ GB = Sigma_type B1 B2 /\ computable [! [: :] |- A1 ≡ B1 !] /\ computable [! [: A1 :] |- A2 ≡ B2 !])) +
                    (exists A1 B1 a b c d, (GA = Eq_type A1 a c /\ GB = Eq_type B1 b d  /\ computable [! [: :] |- A1 ≡ B1 !] /\ computable [! [: :] |- a ≡ b ; A1 !] /\ computable [! [: :] |- c ≡ d ; A1 !])) +
                    (exists C D, (GA = Qtr_type C /\ GB = Qtr_type D) /\ computable [! [: :] |- C ≡ D !]))) ->
                    computable [! [: :] |- A ≡ B !]
  | tm_comp a A : derivable [! [: :] |- a ; A !] ->
                  computable [! [: :] |- A !] /\
                  (exists G g, 
                  eval_type A G /\
                  eval_term a g /\
                  derivable [! [: :] |- a ≡ g ; A !] /\
                  ((G = Terminal_type /\ g = star_term) +
                  (exists C D c d, (G = Sigma_type C D /\ g = pair_term c d) /\ computable [! [: :] |- c ; C !] /\ computable [! [: :] |- d ; substitute (fun _ => c) D !]) +
                  (exists A1 b c d, (G = Eq_type A1 b d /\ g = eq_term A1 c) /\ computable [! [: :] |- b ≡ d ; A1 !]) +
                  (exists C c, (G = Qtr_type C /\ g = class_term c) /\ computable [! [: :] |- c ; C !]))) ->
                  computable [! [: :] |- a ; A !]
  | tmeq_comp A a b : derivable [! [: :] |- a ≡ b ; A !] ->
                    (computable [! [: :] |- a ; A !] /\ computable [! [: :] |- b ; A !]) /\
                    (exists G ga gb, 
                    eval_type A G /\ eval_term a ga /\ eval_term b gb /\
                    ((G = Terminal_type /\ ga = star_term /\ gb = star_term) +
                    (exists A1 A2 a1 a2 b1 b2, (G = Sigma_type A1 A2 /\ ga = pair_term a1 a2 /\ gb = pair_term b1 b2) /\ computable [! [: :] |- a1 ≡ b1 ; A1 !] /\ computable [! [: :] |- a2 ≡ b2 ; substitute (fun _ => a1) A2 !]) +
                    (exists A1 b c d f, (G = Eq_type A1 c d /\ ga = eq_term A1 b /\ gb = eq_term A1 f) /\ computable [! [: :] |- c ≡ d ; A1 !])) +
                    (exists C c1 c2, (G = Qtr_type C /\ ga = class_term c1 /\ gb = class_term c2) /\ computable [! [: :] |- c1 ; C !] /\ computable [! [: :] |- c2 ; C !]))
                    ->
                    computable [! [: :] |- a ≡ b ; A !]
  | ty_comp_ass Gamma B : derivable [! Gamma |- B !] ->
                          (forall i a A, derivable [! [::] |- (a i) ; (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) B !]) ->
                          (forall i a c A, derivable [! [::] |- (a i) ≡ (c i); (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) B ≡ substitute (fun i => (c i)) B !]) ->
                          computable [! Gamma |- B !]
  | tyeq_comp_ass Gamma B D : derivable [! Gamma |- B ≡ D !] -> 
                          computable [! Gamma |- B !] ->
                          (forall i a A, derivable [! [::] |- (a i) ; (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) B ≡ substitute (fun i => (a i)) D !]) ->
                          (forall i a c A, derivable [! [::] |- (a i) ≡ (c i); (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) B ≡ substitute (fun i => (c i)) D !]) ->
                          computable [! Gamma |- B ≡ D !]
  | tm_comp_ass Gamma b B : derivable [! Gamma |- b ; B !] -> 
                          computable [! Gamma |- B !] ->
                          (forall i a A, derivable [! [::] |- (a i) ; (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) b ; substitute (fun i => (a i)) B !]) ->
                          (forall i a c A, derivable [! [::] |- (a i) ≡ (c i); (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) b ≡ substitute (fun i => (c i)) b ; substitute (fun i => (a i)) B !]) -> 
                          computable [! Gamma |- b ; B !]
  | tmeq_comp_ass Gamma b d B : derivable [! Gamma |- b ≡ d; B !] -> 
                          computable [! Gamma |- b ; B !] ->
                          (forall i a A, derivable [! [::] |- (a i) ; (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) b ≡ substitute (fun i => (a i)) d ; substitute (fun i => (a i)) B !]) ->
                          (forall i a c A, derivable [! [::] |- (a i) ≡ (c i); (A i) !] -> computable [! [: :] |- substitute (fun i => (a i)) b ≡ substitute (fun i => (c i)) d ; substitute (fun i => (a i)) B !]) ->
                          computable [! Gamma |- b ≡ d ; B !].

  Scheme computable_ind := Induction for computable Sort Type.
  Scheme computable_rec := Minimality for computable Sort Type.
  Definition computable_rect := computable_ind.



(* Technical inversion lemmas: we should have these for free, so most of the proofs are omitted *)

Lemma inversion_lemma_deriv J : 
  computable J -> derivable J.
Proof.
  intros; destruct X; easy.
Defined.

Lemma inversion_lemma_ty_eval A : 
computable [! [: :] |- A !] -> (exists G, 
                                eval_type A G).
Proof.
Admitted.

Lemma inversion_lemma_ty_correct_eval A : 
computable [! [: :] |- A !] -> (exists G,
                                derivable [! [: :] |- A ≡ G !]).
Proof.
Admitted.
                                
Lemma inversion_lemma_ty_parts A : 
  computable [! [: :] |- A !] -> (exists G, 
                                  ((exists A1 A2, G = Sigma_type A1 A2 /\ computable [! [: :] |- A1 !] /\ computable [! [: A1 :] |- A2 !]) +
                                  (exists A1 b d, G = Eq_type A1 b d /\ computable [! [: :] |- A1 !] /\ computable [! [: :] |- b ; A1 !] /\ computable [! [: :] |- d ; A1 !]) +
                                  (exists C, G = Qtr_type C /\ computable [! [: :] |- C !]))).
Proof.
Admitted.

Lemma inversion_lemma_ty_eq_assoc A B :
  computable [! [: :] |- A ≡ B !] ->
(computable [! [: :] |- A !] /\ computable [! [: :] |- B !]).
Proof.
Admitted.

Lemma inversion_lemma_ty_eq_eval A B :
  computable [! [: :] |- A ≡ B !] ->
(exists GA GB, 
eval_type A GA /\ eval_type B GB /\
((GA = Terminal_type /\ GB = Terminal_type) +
(exists A1 A2 B1 B2, (GA = Sigma_type A1 A2 /\ GB = Sigma_type B1 B2 /\ computable [! [: :] |- A1 ≡ B1 !] /\ computable [! [: A1 :] |- A2 ≡ B2 !])) +
(exists A1 B1 a b c d, (GA = Eq_type A1 a c /\ GB = Eq_type B1 b d  /\ computable [! [: :] |- A1 ≡ B1 !] /\ computable [! [: :] |- a ≡ b ; A1 !] /\ computable [! [: :] |- c ≡ d ; A1 !])) +
(exists C D, (GA = Qtr_type C /\ GB = Qtr_type D) /\ computable [! [: :] |- C ≡ D !]))).
Proof.
Admitted.

Lemma inversion_lemma_tm_assoc a A: 
  computable [! [: :] |- a ; A !] -> 
  computable [! [: :] |- A !].
Proof.
Admitted.

Lemma inversion_lemma_tm_eval : 
forall a A, computable [! [: :] |- a ; A !] -> 
(exists G g, 
eval_type A G /\
eval_term a g /\
derivable [! [: :] |- a ≡ g ; A !] /\
((G = Terminal_type /\ g = star_term) +
(exists C D c d, (G = Sigma_type C D /\ g = pair_term c d) /\ computable [! [: :] |- c ; C !] /\ computable [! [: :] |- d ; substitute (fun _ => c) D !]) +
(exists A1 b c d, (G = Eq_type A1 b d /\ g = eq_term A1 c) /\ computable [! [: :] |- b ≡ d ; A1 !]) +
(exists C c, (G = Qtr_type C /\ g = class_term c) /\ computable [! [: :] |- c ; C !]))).
Proof.
Admitted.

Lemma inversion_tm_eq_assoc a b A :  
computable [! [: :] |- a ≡ b ; A !] ->
                                      (computable [! [: :] |- a ; A !] /\ computable [! [: :] |- b ; A !]).
Proof.
Admitted.

Lemma inversion_tm_eq_parts a b A :  
computable [! [: :] |- a ≡ b ; A !] ->
                                      (exists G ga gb, 
                                      eval_type A G /\ eval_term a ga /\ eval_term b gb /\
                                      ((G = Terminal_type /\ ga = star_term /\ gb = star_term) +
                                      (exists A1 A2 a1 a2 b1 b2, (G = Sigma_type A1 A2 /\ ga = pair_term a1 a2 /\ gb = pair_term b1 b2) /\ computable [! [: :] |- a1 ≡ b1 ; A1 !] /\ computable [! [: :] |- a2 ≡ b2 ; substitute (fun _ => a1) A2 !]) +
                                      (exists A1 b c d f, (G = Eq_type A1 c d /\ ga = eq_term A1 b /\ gb = eq_term A1 f) /\ computable [! [: :] |- c ≡ d ; A1 !])) +
                                      (exists C c1 c2, (G = Qtr_type C /\ ga = class_term c1 /\ gb = class_term c2) /\ computable [! [: :] |- c1 ; C !] /\ computable [! [: :] |- c2 ; C !])).
Proof.
Admitted.

Lemma inversion_lemma_ty_ass : 
  forall Gamma B, computable [! Gamma |- B !] -> derivable [! Gamma |- B !] /\ 
                                                (forall s : raw_substitution Sig 0%nat Gamma, computable [! [: :] |- substitute s B !]).
Proof.
Admitted.

Lemma inversion_lemma_ty_eq_ass : 
forall Gamma B D, computable [! Gamma |- B ≡ D !] ->
                                                    derivable [! Gamma |- B ≡ D !] /\
                                                    computable [! Gamma |- B !] /\
                                                    (forall s : raw_substitution Sig 0%nat Gamma, computable [! [: :] |- substitute s B ≡ substitute s D  !]).
Proof.
Admitted.



(* Preservation of computability of (some) logical rules *)

Lemma refl_tm_computable_empty_context a A:
  computable [![::] |- a ; A!] -> computable [![::] |- a ≡ a ; A!].
Proof.
Admitted.

Lemma assumption_equal_types A B F:
  computable [! [::] |- A ≡ B !] -> (computable (Build_judgement [:A:] F) <-> computable (Build_judgement [:B:] F)).
Proof.
Admitted.

Lemma associate_ty_judgement Gamma A B :
  computable [! Gamma |- A ≡ B !] -> computable [! Gamma |- B !].
Proof.
Admitted.

Lemma elements_equal_types a A B :
  computable [! [::] |- A ≡ B !] -> (computable [! [: :] |- a ; A !] <-> computable [! [::] |- a ; B !]).
Proof.
Admitted.


Lemma F_Tr_computable_empty_context :
  computable [! [::] |- Terminal_type !].
Proof.
  constructor.
    * apply F_Tr_derivable_empty_context.
    * exists Terminal_type. split; [|split]. 
      - apply Terminal_eval.
      - apply refl_ty_derivable_empty_context. apply F_Tr_derivable_empty_context.
      - repeat left; reflexivity.
Defined.

Lemma I_Tr_computable_empty_context :
  computable [! [: :] |- star_term ; Terminal_type !].
Proof.
  constructor.
  - apply I_Tr_derivable_empty_context.
  - split. 
    + apply F_Tr_computable_empty_context.
    + exists Terminal_type, star_term.
      split; [|split]; [| |split]. 
      * apply Terminal_eval.
      * apply star_eval.
      * apply refl_tm_derivable_empty_context.
        apply I_Tr_derivable_empty_context. 
      * repeat left; easy.
Defined.

Lemma C_Tr_computable_empty_context t :
  computable [! [: :] |- t ; Terminal_type !] -> computable [! [: :] |- t ≡ star_term ; Terminal_type !].
Proof.
  constructor.
  - apply C_Tr_derivable_empty_context.
    apply inversion_lemma_deriv.
    apply X. 
  - split. 
    + split; [apply X | apply I_Tr_computable_empty_context]. 
    +   
      exists Terminal_type. exists star_term. exists star_term.
      repeat split.
      * constructor.
      * apply inversion_lemma_tm_eval in X. destruct X as (H1 & H2 & G & g & H5 & H6). destruct H6 as [[[H9 | H10] | H11] | H12].
        -- destruct H9. rewrite <- snd; easy.
        -- destruct H10 as (H10 & H11 & H12 & H13 & H14 & H15). destruct H14. rewrite fst in G. inversion G.
        -- destruct H11 as (H10 & H11 & H12 & H13 & H14 & H15). destruct H14. rewrite fst in G. inversion G.
        -- destruct H12 as (H10 & H11 & H12). destruct H12. destruct fst. rewrite fst in G. inversion G.
      * constructor.
      * repeat left. split; [ | split]; reflexivity.
Defined.


Lemma F_Sigma_computable_empty_context B C :
  computable [! [::] |- B !] -> computable [! [: B :] |- C !] -> computable [! [::] |- Sigma_type B C !].
Proof.
  constructor.
  * apply F_Sigma_derivable_empty_context.
    + apply inversion_lemma_deriv in X; easy.
    + apply inversion_lemma_deriv in X0; easy.
  * exists (Sigma_type B C). split; [|split]. 
    - apply Sigma_eval.
    - apply refl_ty_derivable_empty_context. apply F_Sigma_derivable_empty_context.
      + apply inversion_lemma_deriv in X; easy.
      + apply inversion_lemma_deriv in X0; easy.
    - left. left. right. exists B. exists C. repeat split; easy.
Defined.



Lemma F_Sigma_eq_computable_empty_context B C D E :
  computable [! [::] |- B ≡ D !] -> computable [! [: B :] |- C ≡ E !] -> computable [! [::] |- Sigma_type B C ≡ Sigma_type D E !].
Proof.
  constructor.
  * apply F_Sigma_eq_derivable_empty_context.
    + apply inversion_lemma_deriv in X; easy.
    + apply inversion_lemma_deriv in X0; easy.
  * split.
    - apply associate_ty_judgement in X0 as H.
      apply (assumption_equal_types B D _) in H; try apply X.
      apply inversion_lemma_ty_eq_ass in X0.
      apply inversion_lemma_ty_eq_assoc in X.
      destruct X.
      destruct X0 as (X4 & X5 & X6).
      split; apply F_Sigma_computable_empty_context; easy.
    - exists (Sigma_type B C). exists (Sigma_type D E).
      split; [|split]; try constructor. left. right. exists B. exists C. exists D. exists E. repeat split; easy.   
Defined.


Lemma I_Sigma_computable_empty_context b c B C :
  computable [! [::] |- b ; B !] -> computable [! [: :] |- c ; substitute (fun _ => b) C !] -> computable [! [::] |- Sigma_type B C !] -> computable [! [::] |- pair_term b c ; Sigma_type B C !].
Proof.
  constructor.
  - apply I_Sigma_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + apply X1.
    + exists (Sigma_type B C), (pair_term b c).
      split; [|split]; [| |split]. 
      * apply Sigma_eval.
      * apply pair_eval1.
      * apply refl_tm_derivable_empty_context.
        apply I_Sigma_derivable_empty_context; apply inversion_lemma_deriv; easy.
      * left. left. right. exists B. exists C. exists b. exists c. repeat split; easy.   
Defined.

(*
Lemma E_Sigma_computable_empty_context 
x y d d' (m m' : raw_term Sig 2%nat) B C M :
computable [! [: Sigma_type B C :] |- M !] -> computable [! [: :] |- d ≡ d' ; Sigma_type B C !] -> computable [! [: B ; C :] |- m ≡ m' ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> computable [! [::] |- el_Sigma_term d m ≡ el_Sigma_term d' m' ; substitute (fun _ => d) M !].
Proof.
  constructor.
  - apply E_Sigma_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + split; [apply X | apply I_Tr_computable_empty_context]. 
    + apply inversion_lemma_tm in X. destruct X as (H1 & H2 & H3 & g & H5 & H6 & H7 & H8 & H9 & H10 & H11). 
      exists Terminal_type. exists g. exists star_term.
      split; [|split]; [| |split].
      * constructor.
      * apply H6.
      * constructor.
      * repeat split; try easy; try intros; try destruct X; try easy.
        destruct H8. apply fst. destruct H5; easy.
Defined.
*)


Lemma F_Eq_computable_empty_context c d C :
  computable [! [::] |- C !] -> computable [! [: :] |- c ; C !] -> computable [! [::] |- d ; C !] -> computable [! [::] |- Eq_type C c d !].
Proof.
  constructor.
  * apply F_Eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
  * exists (Eq_type C c d). split; [|split]. 
    - apply Eq_eval.
    - apply refl_ty_derivable_empty_context. apply F_Eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
    - left. right. exists C. exists c. exists d. repeat split; easy.
Defined.



Lemma F_Eq_eq_computable_empty_context c d e f C E :
  computable [! [::] |- C ≡ E !] -> computable [! [: :] |- c ≡ e ; C !] -> computable [! [::] |- d ≡ f ; C !] -> computable [! [::] |- Eq_type C c d ≡ Eq_type E e f !].
Proof.
  constructor.
  * apply F_Eq_eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
  * split. 
    - apply inversion_tm_eq_assoc in X0.
      apply inversion_tm_eq_assoc in X1.
      destruct X0; destruct X1.
      apply (elements_equal_types e) in X as H.
      apply H in snd.
      apply (elements_equal_types f) in X as H1.
      apply H1 in snd0.
      apply inversion_lemma_ty_eq_assoc in X.
      destruct X.
      split; apply F_Eq_computable_empty_context; easy.
    - exists (Eq_type C c d). exists (Eq_type E e f); split; [|split]; try constructor. 
      right. exists C, E, c, e, d, f. repeat split; easy.
Defined.

Lemma I_Eq_computable_empty_context c C :
  computable [! [: :] |- c ; C !] -> computable [! [: :] |- eq_term C c ; Eq_type C c c !].
Proof.
  constructor.
  - apply I_Eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + apply inversion_lemma_tm_assoc in X as H.
      apply F_Eq_computable_empty_context; easy.
    + exists (Eq_type C c c), (eq_term C c).
      split; [|split]; [| |split]. 
      * apply Eq_eval.
      * apply equ_eval.
      * apply refl_tm_derivable_empty_context.
        apply I_Eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
      * left. right. exists C, c, c, c. repeat split; try easy; apply refl_tm_computable_empty_context; easy.   
Defined.

(*
Definition Eq_type_var_dep {gamma : scope_carrier DeBruijn} (C : raw_type Sig (gamma)%nat) : raw_type Sig (gamma+1)%nat.
Proof.
  refine (raw_symbol Eq _).
  intros.
  recursive_destruct i.
  - unfold argument_scope; simpl; rewrite <- add_n_O. unfold argument_class; simpl. apply (rename succ_db _)  in C. refine C.
  - unfold argument_scope; simpl; rewrite <- add_n_O; refine (raw_variable _). destruct gamma; apply zero_db.
  - unfold argument_scope; simpl; rewrite <- add_n_O; refine (raw_variable _). destruct gamma; apply zero_db.
Defined.
*)
(*
Lemma F_Eq_computable_dependent C :
  computable [! [: C :] |- Eq_type_var_dep C !].
  *)

Lemma sub_eq_ty_Eq_computable c d C :
  computable [! [: :] |- c ≡ d ; C !] -> computable [! [: :] |- Eq_type C c c ≡ Eq_type C d d !].
Proof.
Admitted.

Lemma I_Eq_eq_computable_empty_context c d C :
  computable [! [: :] |- c ≡ d ; C !] -> computable [! [: :] |- eq_term C c ≡ eq_term C d ; Eq_type C c c !].
Proof.
  constructor.
  - apply I_Eq_eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + apply inversion_tm_eq_assoc in X as H; destruct H; split; apply inversion_lemma_tm_assoc in fst as H1; try apply I_Eq_computable_empty_context; try easy.
      apply sub_eq_ty_Eq_computable in X as H2.
      apply (elements_equal_types (eq_term C d)) in H2.
      apply H2.
      apply I_Eq_computable_empty_context; easy.
    + exists (Eq_type C c c), (eq_term C c), (eq_term C d).
      split; [|split]; [| |split]. 
      * apply Eq_eval.
      * apply equ_eval.
      * apply equ_eval.
      * left. right. exists C, c, c, c, d. repeat split; try easy. apply inversion_tm_eq_assoc in X as H; destruct H; apply refl_tm_computable_empty_context; easy.   
Defined.

Lemma E_Eq_computable_empty_context c d p C :
  computable [! [::] |- p ; Eq_type C c d !] -> computable [! [::] |- C !] -> computable [! [: :] |- c ; C !] -> computable [! [::] |- d ; C !] -> computable [! [::] |- c ≡ d ; C !].
Proof.
  constructor.
  - apply (E_Eq_derivable_empty_context c d p); apply inversion_lemma_deriv; easy.
  - repeat split; try easy.
    admit.
Admitted.

Lemma C_Eq_computable_empty_context c d p C :
  computable [! [::] |- p ; Eq_type C c d !] -> computable [! [::] |- p ≡ eq_term C c ; Eq_type C c d !].
Proof.
  constructor.
  - apply C_Eq_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split.
    + split; try easy.
      apply inversion_lemma_tm_eval in X as X1.
      destruct X1 as (G & g & H1 & H2 & H5 & H6). destruct H6 as [[[H9 | H10] | H11] | H12].
        -- destruct H9. rewrite fst in H1. inversion H1.
        -- destruct H10 as (H10 & H11 & H12 & H13 & H14 & H15). destruct H14. rewrite fst in H1. inversion H1.
        -- destruct H11 as (A & a & e & b & H14 & H15). destruct H14. rewrite fst in H1. admit. 
        -- destruct H12 as (H10 & H11 & H12). destruct H12. destruct fst. rewrite fst in H1. inversion H1.
Admitted.

Lemma F_Qtr_computable_empty_context A :
  computable [! [::] |- A !] -> computable [! [::] |- Qtr_type A !].
Proof.
  constructor.
  * apply F_Qtr_derivable_empty_context.
    apply inversion_lemma_deriv in X; easy.
  * exists (Qtr_type A). split; [|split]. 
    - apply Qtr_eval.
    - apply refl_ty_derivable_empty_context. apply F_Qtr_derivable_empty_context.
    apply inversion_lemma_deriv in X; easy.
    - right. exists A. repeat split; easy.
Defined.

Lemma F_Qtr_eq_computable_empty_context A B :
  computable [! [::] |- A ≡ B !] -> computable [! [::] |- Qtr_type A ≡ Qtr_type B !].
Proof.
  constructor.
  * apply F_Qtr_eq_derivable_empty_context.
    apply inversion_lemma_deriv in X; easy.
  * split.
    - apply inversion_lemma_ty_eq_assoc in X. destruct X; split; apply F_Qtr_computable_empty_context; easy.
    - exists (Qtr_type A), (Qtr_type B). repeat split. { constructor. } { constructor. }
      right. exists A, B. repeat split; easy.
Defined.

Lemma I_Qtr_computable_empty_context a A :
  computable [! [::] |- a ; A !] -> computable [! [::] |- class_term a ; Qtr_type A !].
Proof.
  constructor.
  - apply I_Qtr_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + apply inversion_lemma_tm_assoc in X; apply F_Qtr_computable_empty_context; easy.
    + exists (Qtr_type A), (class_term a).
      split; [|split]; [| |split]. 
      * apply Qtr_eval.
      * apply class_eval.
      * apply refl_tm_derivable_empty_context.
        apply I_Qtr_derivable_empty_context; apply inversion_lemma_deriv; easy.
      * right. exists A, a. repeat split; easy.   
Defined.

Lemma eq_Qtr_computable_empty_context a b A :
  computable [! [::] |- a ; A !] -> computable [! [::] |- b ; A !] -> computable [! [::] |- class_term a ≡ class_term b ; Qtr_type A !].
Proof.
  constructor.
  - apply eq_Qtr_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + split; apply I_Qtr_computable_empty_context; easy.
    + exists (Qtr_type A), (class_term a), (class_term b).
      split; [|split]; [| |split]. { constructor. } { constructor. }{ constructor. } 
      right. exists A, a, b. repeat split; easy.   
Defined.

(*
Lemma E_Sigma_computable_empty_context 
x y d d' (m m' : raw_term Sig 2%nat) B C M :
computable [! [: Sigma_type B C :] |- M !] -> computable [! [: :] |- d ≡ d' ; Sigma_type B C !] -> computable [! [: B ; C :] |- m ≡ m' ; substitute (fun z => pair_term (raw_variable x) (raw_variable y) ) M !] -> computable [! [::] |- el_Sigma_term d m ≡ el_Sigma_term d' m' ; substitute (fun _ => d) M !].
Proof.
  constructor.
  - apply E_Sigma_derivable_empty_context; apply inversion_lemma_deriv; easy.
  - split. 
    + split; [apply X | apply I_Tr_computable_empty_context]. 
    + apply inversion_lemma_tm in X. destruct X as (H1 & H2 & H3 & g & H5 & H6 & H7 & H8 & H9 & H10 & H11). 
      exists Terminal_type. exists g. exists star_term.
      split; [|split]; [| |split].
      * constructor.
      * apply H6.
      * constructor.
      * repeat split; try easy; try intros; try destruct X; try easy.
        destruct H8. apply fst. destruct H5; easy.
Defined.
*)