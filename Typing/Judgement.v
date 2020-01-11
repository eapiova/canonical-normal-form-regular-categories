Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Expression.
Require Import Syntax.Substitution.
Require Import Syntax.Metavariable.
Require Import Typing.Context.

(** We first set up the combinatorics describing the “shapes” of the judgement forms — specifying how many expressions they will involve, and of what classes — before bringing in the actual syntax, and defining judgements themselves.

The motivation of this is so that definitions like “to translate a judgement under a signature map, translate each expression of the judgement” can be formalised literally as such (cf. [fmap_hypothetical_judgement] below), without having to case-split according to the form of the judgement and translate each expression component individually.
*)
Section JudgementCombinatorics.

  (** We take as primitive only the _hypothetical_ judgment forms:
  [! Γ |- A !],
  [! Γ |- A ≡ A' !],
  [! Γ |- a ; A !],
  [! Γ |- a ≡ a' ; A !],
  and rules and derivations will be given purely in terms of these.
 
  Other judgement forms — e.g. well-formed contexts, context morphisms — are taken as _auxiliary_ judgements, defined afterwards from thes primitive ones. *)
  Local Inductive form : Type :=
  | form_object (cl : syntactic_class)
      (* a thing is a term, a thing is a type *)
  | form_equality (cl : syntactic_class).
      (* terms are equal, types are equal *)

  Local Definition is_object : form -> Type
    := fun jf => match jf with
                     | form_object _ => Unit
                     | form_equality _ => Empty
                  end.

  Local Definition class_of : form -> syntactic_class
    := fun jf => match jf with
                     | form_object cl => cl
                     | form_equality cl => cl
                  end.

  (** A _judgement_ will have of a piece of syntax for each _slot_ of the given judgement form: so e.g. the term judgement [! Γ |- a ; A !] has one type slot and one term slot.  To be able to describe constructions on judgements uniformly later, we define the slots in a structured way, dividing them into the _head slot_ and _boundary slots_. *)

  Local Definition type_object_boundary := Family.empty syntactic_class.

  Inductive term_boundary_slot_index := the_type_slot.

  Definition term_boundary_slot :=
    {| family_index := term_boundary_slot_index ;
       family_element :=
         (fun slot =>
            match slot with
            | the_type_slot => class_type
            end)
    |}.

  (** The boundary slots of a term or type judgement. *)
  Local Definition object_boundary_slot (cl : syntactic_class)
    : family syntactic_class
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | class_type => type_object_boundary
       (* Boundary of a term judgement: the type of the term *)
       | class_term => term_boundary_slot
     end.

  Inductive equality_boundary_slot_index cl
  :=
    | the_equality_boundary_slot
        : family_index (object_boundary_slot cl)
          -> equality_boundary_slot_index cl
    | the_lhs_slot
    | the_rhs_slot.

  Local Definition equality_boundary_slot (cl : syntactic_class) :=
    {| family_index := equality_boundary_slot_index cl ;
       family_element :=
         (fun slot =>
            match slot with
            | the_equality_boundary_slot slot' => object_boundary_slot cl slot'
            | the_lhs_slot => cl
            | the_rhs_slot => cl
            end)
    |}.

  (* Syntactic classes of the slots in the boundary of a hypothetical judgement *)
  Local Definition boundary_slot (jf : form)
    : family syntactic_class
  := match jf with
       (* object judgement boundary is the boundary of the object *)
       | form_object cl => object_boundary_slot cl
       (* equality judgement boundary: a boundary of the corresponding
          object-judgement, together with two objects of the given class *)
       | form_equality cl  => equality_boundary_slot cl
     end.

  Inductive object_slot_index cl :=
  | the_object_boundary_slot : object_boundary_slot cl -> object_slot_index cl
  | the_head_slot : object_slot_index cl.

  Local Definition object_slot cl :=
    {| family_index := object_slot_index cl ;
       family_element :=
         (fun slot =>
            match slot with
            | the_object_boundary_slot slot' => object_boundary_slot cl slot'
            | the_head_slot => cl
            end)
    |}.

  (* Syntactic classes of the slots in a hypothetical judgement *)
  Local Definition slot (jf : form)
    : family syntactic_class
  := match jf with
       (* Equality case: boundary is everything *)
       | form_equality cl =>
           boundary_slot (form_equality cl)
       (* Object case: add the head slot *)
       | form_object cl =>
           object_slot cl
     end.
  (* NOTE: the order of slots for term judgements follows “dependency order” — later slots are (morally) dependent on earlier ones, so the type comes before the term.  However, the functions in section [Judgement_Notations] below follow standard written order, so the term comes before the type. *)

  Definition the_boundary_slot {jf : form}
    : Family.map (boundary_slot jf) (slot jf).
  Proof.
    simple refine (_;_).
    - destruct jf as [cl_ob | cl_eq].
      + exact (the_object_boundary_slot cl_ob).
      + exact idmap.
    - destruct jf; intros; apply idpath.
  Defined.

  Definition boundary_slot_from_object_boundary_slot {jf : form}
    : Family.map (object_boundary_slot (class_of jf)) (boundary_slot jf).
  Proof.
    simple refine (_;_).
    - destruct jf as [cl_ob | cl_eq].
      + exact idmap.
      + apply the_equality_boundary_slot.
    - destruct jf; intros; apply idpath.
  Defined.

  Definition the_head_slot_from_is_object
      {jf : form} (jf_obj : is_object jf)
    : slot jf.
  Proof.
    destruct jf.
    - apply the_head_slot.
    - destruct jf_obj.
  Defined.

  Definition class_of_head_slot_from_is_object
      {jf : form} (jf_obj : is_object jf)
    : slot jf (the_head_slot_from_is_object jf_obj) = class_of jf.
  Proof.
    destruct jf.
    - apply idpath.
    - destruct jf_obj.
  Defined.

End JudgementCombinatorics.

Section Judgements.

  Context {σ : shape_system}.
  Context (Σ : signature σ).

  Definition hypothetical_boundary_expressions jf γ
  := forall i : boundary_slot jf, raw_expression Σ (boundary_slot jf i) γ.
  Identity Coercion id_hypothetical_boundary_expressions :
    hypothetical_boundary_expressions >-> Funclass.

  Local Record hypothetical_boundary γ : Type
    := { form_of_boundary : form
       ; boundary_expression :>
           hypothetical_boundary_expressions form_of_boundary γ }.

  Arguments form_of_boundary {_} _.
  Arguments boundary_expression {_} _.

  Definition hypothetical_judgement_expressions jf γ
  := forall i : slot jf, raw_expression Σ (slot jf i) γ.
  Identity Coercion id_hypothetical_judgement_expressions :
    hypothetical_judgement_expressions >-> Funclass.

  Record hypothetical_judgement γ : Type
    := { form_of_judgement : form
       ; judgement_expression :>
           hypothetical_judgement_expressions form_of_judgement γ }.
  Arguments form_of_judgement {_} _.
  Arguments judgement_expression {_} _.

  Local Definition head {γ}
      (J : hypothetical_judgement γ)
      (J_obj : is_object (form_of_judgement J))
    : raw_expression Σ (class_of (form_of_judgement J)) γ.
  Proof.
    refine (transport (fun cl => raw_expression _ cl _) _ _).
    - apply (class_of_head_slot_from_is_object J_obj).
    - apply J.
  Defined.

  Local Record boundary : Type
  := { context_of_boundary : raw_context Σ
     ; hypothetical_part_of_boundary
         :> hypothetical_boundary context_of_boundary }.

  Record judgement : Type
  := { context_of_judgement : raw_context Σ
     ; hypothetical_part :> hypothetical_judgement context_of_judgement }.

  Definition shape_of_judgement (J : judgement) : shape_carrier σ
  := context_of_judgement J.

  Definition hypothetical_judgement_expressions_from_boundary_and_head
      {γ} {jf}
      (bdry : hypothetical_boundary_expressions jf γ)
      (head : is_object jf -> raw_expression Σ (class_of jf) γ)
    : hypothetical_judgement_expressions jf γ.
  Proof.
    destruct jf.
    - (* case: object judgement *)
      intros [ i | ].
      + apply bdry.
      + apply head. constructor.
    - (* case: equality judgement *)
      exact bdry.
  Defined.

  Definition hypothetical_boundary_of_judgement
      {γ} (J : hypothetical_judgement γ)
    : hypothetical_boundary γ.
  Proof.
    exists (form_of_judgement J).
    intros i. destruct J as [[jf_ob | jf_eq] j];
      exact (j (the_boundary_slot i)).
  Defined.
  
  Definition boundary_of_judgement
    : judgement -> boundary.
  Proof.
    intros J. exists (context_of_judgement J).
    apply hypothetical_boundary_of_judgement, J.
  Defined.

End Judgements.

(* TODO: make [Σ] implicit in context of section, so fewer items need [Arguments] redeclaring? *)
Arguments Build_hypothetical_boundary {_ _ _} _ _.
Arguments form_of_boundary {_ _ _} _. 
Arguments Build_hypothetical_judgement {_ _ _} _ _.
Arguments form_of_judgement {_ _ _} _. 
Arguments head {_ _ _} _ / _.
Arguments Build_boundary {_ _} _ _. 
Arguments context_of_boundary {_ _} _. 
Arguments Build_judgement {_ _} _ _. 
Arguments context_of_judgement {_ _} _. 
Arguments shape_of_judgement {_ _} _. 
Arguments hypothetical_part {_ _} _. 
Arguments boundary_of_judgement {_ _} _.

Section JudgementFmap.

  Context {σ : shape_system}.

  Definition fmap_hypothetical_boundary_expressions
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ') {jf} {γ} 
    : hypothetical_boundary_expressions Σ jf γ
      -> hypothetical_boundary_expressions Σ' jf γ.
  Proof.
    intros B i. apply (Expression.fmap f), B.
  Defined.

  Definition fmap_hypothetical_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ') {γ}
    : hypothetical_boundary Σ γ -> hypothetical_boundary Σ' γ.
  Proof.
    intros B. exists (form_of_boundary B).
    exact (fmap_hypothetical_boundary_expressions f B).
  Defined.

  Local Definition fmap_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ)
    : boundary Σ'.
  Proof.
    exists (Context.fmap f (context_of_boundary B)).
    exact (fmap_hypothetical_boundary f B).
  Defined.

  Definition fmap_hypothetical_judgement_expressions
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ') {jf} {γ} 
    : hypothetical_judgement_expressions Σ jf γ
      -> hypothetical_judgement_expressions Σ' jf γ.
  Proof.
    intros J i. apply (Expression.fmap f), J.
  Defined.

  Definition fmap_hypothetical_judgement
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ') {γ}
    : hypothetical_judgement Σ γ -> hypothetical_judgement Σ' γ.
  Proof.
    intros J. exists (form_of_judgement J).
    exact (fmap_hypothetical_judgement_expressions f J).
  Defined.

  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : judgement Σ -> judgement Σ'.
  Proof.
    intros J.
    exists (Context.fmap f (context_of_judgement J)).
    exact (fmap_hypothetical_judgement f (hypothetical_part J)).
  Defined.

  Context `{Funext}.

  Definition fmap_hypothetical_boundary_expressions_idmap
      {Σ} {jf} {γ} (B : hypothetical_boundary_expressions Σ jf γ)
    : fmap_hypothetical_boundary_expressions (Signature.idmap Σ) B = B.
  Proof. 
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
  Defined.

  Definition fmap_hypothetical_boundary_idmap
      {Σ} {γ} (B : hypothetical_boundary Σ γ)
    : fmap_hypothetical_boundary (Signature.idmap Σ) B = B.
  Proof. 
    apply (ap (Build_hypothetical_boundary _)).
    apply fmap_hypothetical_boundary_expressions_idmap.
  Defined.

  Definition fmap_fmap_hypothetical_boundary_expressions
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {jf} {γ} (B : hypothetical_boundary_expressions Σ jf γ)
    : fmap_hypothetical_boundary_expressions f'
        (fmap_hypothetical_boundary_expressions f B)
      = fmap_hypothetical_boundary_expressions (Signature.compose f' f) B.
  Proof.
    apply path_forall; intros i.
    apply Expression.fmap_fmap.
  Defined.

  Definition fmap_fmap_hypothetical_boundary
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_boundary Σ γ)
    : fmap_hypothetical_boundary f' (fmap_hypothetical_boundary f B)
      = fmap_hypothetical_boundary (Signature.compose f' f) B.
  Proof. 
    apply (ap (Build_hypothetical_boundary _)).
    apply fmap_fmap_hypothetical_boundary_expressions.
  Defined.

  Definition fmap_hypothetical_boundary_expressions_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {jf} {γ} (B : hypothetical_boundary_expressions Σ jf γ)
    : fmap_hypothetical_boundary_expressions (Signature.compose f' f) B
      = fmap_hypothetical_boundary_expressions f'
          (fmap_hypothetical_boundary_expressions f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_boundary_expressions.
  Defined.

  Definition fmap_hypothetical_boundary_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_boundary Σ γ)
    : fmap_hypothetical_boundary (Signature.compose f' f) B
      = fmap_hypothetical_boundary f' (fmap_hypothetical_boundary f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_boundary.
  Defined.

  Definition fmap_hypothetical_judgement_idmap
      {Σ} {γ} (J : hypothetical_judgement Σ γ)
    : fmap_hypothetical_judgement  (Signature.idmap Σ) J = J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
  Defined.

  Definition fmap_fmap_hypothetical_judgement
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_judgement Σ γ)
    : fmap_hypothetical_judgement f' (fmap_hypothetical_judgement f B)
      = fmap_hypothetical_judgement (Signature.compose f' f) B.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply Expression.fmap_fmap.
  Defined.

  Definition fmap_hypothetical_judgement_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_judgement Σ γ)
    : fmap_hypothetical_judgement (Signature.compose f' f) B
      = fmap_hypothetical_judgement f' (fmap_hypothetical_judgement f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_judgement.
  Defined.

  Local Definition fmap_idmap
      {Σ} (J : judgement Σ)
    : fmap (Signature.idmap Σ) J = J.
  Proof.
    eapply concat.
      2: { eapply (ap (Build_judgement _)), fmap_hypothetical_judgement_idmap. }
    refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _).
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
    (* TODO: easier if we generalise [eq_by_expressions]? *)
  Defined.

  Local Definition fmap_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : fmap (Signature.compose f' f) J = fmap f' (fmap f J).
  Proof.
    eapply concat.
    2: { eapply (ap (Build_judgement _)), fmap_hypothetical_judgement_compose. }
    unfold fmap. simpl.
      refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _).
      apply path_forall; intros i.
      apply Expression.fmap_compose.
    (* TODO: easier if we generalise [eq_by_expressions]? *)
  Defined.

  Local Definition fmap_fmap
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : fmap f' (fmap f J) = fmap (Signature.compose f' f) J.
  Proof.
    apply inverse, fmap_compose.
  Defined.

  Definition fmap_hypothetical_judgement_expressions_from_boundary_and_head
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf} {γ : σ} (B : hypothetical_boundary_expressions Σ jf γ)
      (e : is_object _ -> raw_expression Σ _ γ)
    : fmap_hypothetical_judgement_expressions f
        (hypothetical_judgement_expressions_from_boundary_and_head _ B e)
      = hypothetical_judgement_expressions_from_boundary_and_head _
          (fmap_hypothetical_boundary_expressions f B)
          (fun jf_ob => Expression.fmap f (e jf_ob)).
  Proof.
    destruct jf as [ocl | ecl].
    - apply path_forall; intros [ ? | ]; apply idpath.
    - apply idpath.
  Defined.

End JudgementFmap.

Section JudgementNotations.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition make_type_judgement
        (Γ : raw_context Σ) (A : raw_type Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_object class_type).
    intros [ [] | ]; exact A.
  Defined.

  Local Definition make_type_equality_judgement
             (Γ : raw_context Σ)
             (A A' : raw_type Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_equality class_type).
    intros [ [] |  | ].
    - exact A.
    - exact A'.
  Defined.

  Local Definition make_term_judgement
             (Γ : raw_context Σ) (a : raw_term Σ Γ) (A : raw_type Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_object class_term).
    intros [ [] | ].
    - exact A.
    - exact a.
  Defined.

  (* TODO: consistentise order with [make_term_judgement]. *)
  Local Definition make_term_equality_judgement
             (Γ : raw_context Σ) (A : raw_type Σ Γ) (a a': raw_term Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_equality class_term).
    intros [ [] | | ].
    - exact A.
    - exact a.
    - exact a'.
  Defined.

End JudgementNotations.

Notation "'[!' Γ |- A !]" := (make_type_judgement Γ A) : judgement_scope.
Notation "'[!' Γ |- A ≡ A' !]"
  := (make_type_equality_judgement Γ A A') : judgement_scope.
Notation "'[!' Γ |- a ; A !]"
  :=  (make_term_judgement Γ a A) : judgement_scope.
Notation "'[!' Γ |- a ≡ a' ; A !]"
  := (make_term_equality_judgement Γ A a a') : judgement_scope.

Open Scope judgement_scope.

Arguments make_type_judgement : simpl never.
Arguments make_type_equality_judgement : simpl never.
Arguments make_term_judgement : simpl never.
Arguments make_term_equality_judgement : simpl never.

(** A tactic that is often handy working with syntax, especially slots:
recursively destruct some object of an iterated inductive type.

Currently only supports specific inductive types hand-coded here. *)
(* TODO: can this be generalised to work for arbitrary inductive types? *)
Ltac recursive_destruct x :=
    compute in x;
    try match type of x with
    | form =>
      let cl := fresh "cl" in
      destruct x as [ cl | cl ]; recursive_destruct cl
    | syntactic_class => destruct x as [ | ]
    | option _ =>
      let y := fresh "y" in
      destruct x as [ y | ]; [recursive_destruct y | idtac ]
    | Empty => destruct x
    | Unit => destruct x as []
    | sum _ _ =>
      let y := fresh "y" in
      destruct x as [ y | y ]; recursive_destruct y
    | sig _ =>
      let x1 := fresh "x1" in
      let x2 := fresh "x2" in
      destruct x as [ x1 x2 ]; recursive_destruct x1; recursive_destruct x2
    | term_boundary_slot_index => destruct x as []
    | object_slot_index _ =>
      let slot := fresh "slot" in
      destruct x as [ slot | ] ; [ recursive_destruct slot | idtac ]
    | equality_boundary_slot_index _ =>
      let slot := fresh "slot" in
      destruct x as [ slot | | ] ; [ recursive_destruct slot | idtac | idtac ]
    | _ => idtac
    end.


Section Equality_Lemmas.
(** If judgements were record types, rather than function types over their finite set of slots, they would have judgemental eta, which would be very convenient.

In lieu of that, we give explicit lemmas for judgement equality:
- one [eq_by_eta] analogous to eta-expansion and the eta rule,
- one [eq_by_expressions] analogous to general function extensionality. *)

  Context {σ : shape_system} {Σ : signature σ} `{Funext}.

  Local Definition eta_expand (J : judgement Σ)
    : judgement Σ.
  Proof.
    destruct J as [Γ [jf J]].
    set (jf_keep := jf).
    recursive_destruct jf.
    - apply (make_type_judgement Γ).
      exact (J (the_head_slot _)).
    - apply (make_term_judgement Γ).
      + exact (J (the_head_slot _)).
      + refine (J (@the_boundary_slot
                     (form_object class_term) the_type_slot)).
    - apply (make_type_equality_judgement Γ).
      + exact (J (the_lhs_slot _)).
      + exact (J (the_rhs_slot _)).
    - apply (make_term_equality_judgement Γ).
      + exact (J (the_equality_boundary_slot class_term the_type_slot)).
      + exact (J (the_lhs_slot _)).
      + exact (J (the_rhs_slot _)).
  Defined.

  Global Arguments eta_expand / .

  Local Definition eta (j : judgement Σ)
    : eta_expand j = j.
  Proof.
    destruct j as [Γ [jf j]]; recursive_destruct jf;
      apply (ap (Build_judgement _)), (ap (Build_hypothetical_judgement _));
      apply path_forall; intros i;
      recursive_destruct i;
      apply idpath.
  Defined.

  (** To give something for a judgement (e.g. to derive it), one can always eta-expand the judgement first. *)
  Local Definition canonicalise
      (P : judgement Σ -> Type)
      (j : judgement Σ)
    : P (eta_expand j) -> P j.
  Proof.
    apply transport, eta.
  Defined.
  (** Typical usage, when giving a derivation, to make the goal judgement more readable: [apply Judgement.canonicalise; simpl] *)

  (** To check two judgements are equal, it’s enough to check their eta-expansions.
   Convenient for when modulo eta expansion, judgements are literally equal:
   [apply Judgement.eq_by_eta, idpath.] 

   For other cases, [eq_by_expressions] is usually better. *)
  Local Definition eq_by_eta
      (j j' : judgement Σ)
    : eta_expand j = eta_expand j' -> j = j'.
  Proof.
    intros e.
    exact ((eta j)^ @ e @ eta j').
  Defined.

  (** When two judgements have the same form and are over the same shape, 
  then they are equal if all expressions involved (in both the context and
  the hypothetical part) are equal.

  Often useful in cases where the equality of expressions is for a uniform
  reason, such as functoriality/naturality lemmas. 

  For cases where the specific form of the judgement is involved in the 
  difference, [eq_by_eta] may be cleaner. *)
  Local Definition eq_by_expressions
      {γ : σ} {Γ Γ' : γ -> raw_type Σ γ}
      {jf : form} {J J' : _}
      (e_Γ : forall i, Γ i = Γ' i)
      (e_J : forall i, J i = J' i)
    : Build_judgement (Build_raw_context γ Γ)
                      (Build_hypothetical_judgement jf J)
    = Build_judgement (Build_raw_context γ Γ')
                      (Build_hypothetical_judgement jf J').
  Proof.
    eapply concat.
    { eapply (ap (Build_judgement _)),
      (ap (Build_hypothetical_judgement _)), path_forall; exact e_J. }
    apply (ap (fun Γ => Build_judgement (Build_raw_context γ Γ) _)).
    apply path_forall; auto.
  Defined.

  (** When two judgements have the same form and are over the same shape, 
  then they are equal if all expressions involved (in both the context and
  the hypothetical part) are equal.

  Often useful in cases where the equality of expressions is for a uniform
  reason, such as functoriality/naturality lemmas. 

  For cases where the specific form of the judgement is involved in the 
  difference, [eq_by_eta] may be cleaner. *)
  Local Definition boundary_eq_by_expressions
      {γ : σ} {Γ Γ' : γ -> raw_type Σ γ}
      {jf : form} {B B' : _}
      (e_Γ : forall i, Γ i = Γ' i)
      (e_B : forall i, B i = B' i)
    : Build_boundary (Build_raw_context γ Γ)
                      (Build_hypothetical_boundary jf B)
    = Build_boundary (Build_raw_context γ Γ')
                      (Build_hypothetical_boundary jf B').
  Proof.
    eapply concat.
    { eapply (ap (Build_boundary _)),
      (ap (Build_hypothetical_boundary _)), path_forall; exact e_B. }
    apply (ap (fun Γ => Build_boundary (Build_raw_context γ Γ) _)).
    apply path_forall; auto.
  Defined.

End Equality_Lemmas.

(** A key notion is the _presuppositions_ of a judgement.

For instance, the presuppositions of [ Γ |- a : A ] are the judgements [ |- Γ ] and [ Γ |- A type ].

As with judgements themselves, we first describe set up the combinatorics indexing the constructions involved. *)

Section PresuppositionsCombinatorics.
(** Whenever an object appears in the boundary of an object judgement, then its
    boundary embeds into that boundary.

    NOTE. This is a special case of [boundary_slot_from_presupposition] below.
    It is abstracted out because it’s used twice: directly for object
    judgements, and as part of the case for equality judgements.

    In fact it’s almost trivial, so could easily be inlined; but conceptually
    it is the same thing both times, and in type theory with more judgements,
    it would be less trivial, so we keep it factored out. *)

  Local Definition object_boundary_from_boundary_slots
    {cl : syntactic_class} (i : object_boundary_slot cl)
    : Family.map
        (object_boundary_slot (object_boundary_slot cl i))
        (object_boundary_slot cl).
  Proof.
    apply Family.Build_map'. intros j.
    destruct cl as [ | ]; cbn in i.
    (* Ty: nothing to do, no objects in boundary *)
    - destruct i.
    (* Tm: i must be type, so again nothing left, no j in its boundary *)
    - destruct i as []; destruct j.
  Defined.

(** Wherever an judgement [I] occurs as a presupposition of a judgement [J],
there is a canonical embedding of the slots of [I] into the slots of [J]. *)
  Local Definition boundary_slot_from_presupposition
    {jf : form} (i : boundary_slot jf)
    : Family.map
        (slot (form_object (boundary_slot jf i)))
        (boundary_slot jf).
  Proof.
    apply Family.Build_map'.
    intros [ j | ].
    - (* case: j in boundary part of presupposition *)
      destruct jf as [ cl | cl ].
      + (* original jf is object judgement *)
        exists (object_boundary_from_boundary_slots i j).
        apply (Family.map_commutes _ j).
      + (* original jf is equality judgement *)
        destruct i as [ i' |  | ].
        * (* i is in shared bdry of LHS/RHS *)
          cbn in j.
          exists
            (the_equality_boundary_slot _ (object_boundary_from_boundary_slots i' j)).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (the_equality_boundary_slot _ j). apply idpath.
        * (* i is LHS *)
          exists (the_equality_boundary_slot _ j). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.

  Local Definition slot_from_presupposition
    {jf : form} (i : boundary_slot jf)
    : Family.map
        (slot (form_object (boundary_slot _ i)))
        (slot jf).
  Proof.
    eapply Family.compose.
    - apply the_boundary_slot.
    - apply boundary_slot_from_presupposition.
  Defined.

End PresuppositionsCombinatorics.

Section Presuppositions.
(** TODO: the naming in this section seems a bit ugly. *)

  Context {σ : shape_system}.

  (** The presuppositions of a judgment boundary [jb] *)
  Definition presupposition_of_boundary
      {Σ : signature σ} (B : boundary Σ)
    : family (judgement Σ).
  Proof.
    simple refine (Build_family _ _ _).
    - exact (boundary_slot (form_of_boundary B)).
    - intros i. exists (context_of_boundary B).
      exists (form_object (boundary_slot _ i)).
      intros j.
      refine (transport (fun cl => raw_expression _ cl _) _ _).
      + exact (Family.map_commutes (boundary_slot_from_presupposition i) j).
      + exact (B (boundary_slot_from_presupposition i j)).
  Defined.

  (** The presuppositions of judgement [j]. *)
  Definition presupposition
      {Σ : signature σ} (j : judgement Σ)
    : family (judgement Σ)
  := presupposition_of_boundary (boundary_of_judgement j).

  (** Interactions between functoriality under signature maps,
   and taking presuppositions. *)

  Local Definition fmap_presupposition_of_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ) (p : presupposition_of_boundary B)
    : fmap f (presupposition_of_boundary B p)
    = presupposition_of_boundary (fmap_boundary f B) p.
  Proof.
    destruct B as [Γ [jf B]].
    recursive_destruct jf; recursive_destruct p; try apply idpath;
      refine (eq_by_expressions _ _);
      intros j; recursive_destruct j; apply idpath.
  Defined.

  (* TODO: this should be an iso! *)
  Local Definition presupposition_fmap_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ)
    : Family.map
        (presupposition_of_boundary (fmap_boundary f B))
        (Family.fmap (fmap f) (presupposition_of_boundary B)).
  Proof.
    exists idmap.
    intros i; apply fmap_presupposition_of_boundary.
  Defined.

  Local Definition fmap_presupposition `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement Σ)
      (p : presupposition J)
    : fmap f (presupposition J p)
    = presupposition (fmap f J) p.
  Proof.
    destruct J as [Γ [jf J]].
      recursive_destruct jf; recursive_destruct p; try apply idpath;
        refine (eq_by_expressions _ _);
        intros j; recursive_destruct j; apply idpath.    
  Defined.

  (* TODO: this should be an iso!  And consistentise with [presupposition_fmap_boundary]. *)
  Local Definition fmap_presupposition_family `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : Family.map
        (Family.fmap (fmap f) (presupposition J))
        (presupposition (fmap f J)).
  Proof.
    exists (fun p => p).
    intros p; apply inverse, fmap_presupposition.
  Defined.

End Presuppositions.

Section Renaming.
(** _Hypothetical_ judgements admit renaming along aritrary maps of shapes, just like expressions.

_Complete_ judgements, involving contexts, admit renaming only along _isomorphisms_ of shapes.  (Cf. discussion at [Context.rename].) *)

  Context {σ : shape_system} {Σ : signature σ}.

  Definition rename_hypothetical_boundary_expressions
      {jf} {γ γ' : σ} (f : γ -> γ')
      (B : hypothetical_boundary_expressions Σ jf γ)
    : hypothetical_boundary_expressions Σ jf γ'.
  Proof.
    exact (fun j => rename f (B j)).
  Defined.

  Definition rename_hypothetical_boundary
      {γ γ' : σ} (f : γ -> γ')
      (B : hypothetical_boundary Σ γ)
    : hypothetical_boundary Σ γ'.
  Proof.
    exists (form_of_boundary B).
    exact (rename_hypothetical_boundary_expressions f B).
  Defined.

  Definition rename_hypothetical_judgement
      {γ γ' : σ} (f : γ -> γ')
      (J : hypothetical_judgement Σ γ)
    : hypothetical_judgement Σ γ'.
  Proof.
    exists (form_of_judgement J).
    exact (fun j => rename f (J j)).
  Defined.

  (** Note: argument order from here on follows [Context.rename], not general [rename] for expressions. *)
  Local Definition rename
      (J : judgement Σ)
      {γ' : shape_carrier σ} (f : γ' <~> shape_of_judgement J)
    : judgement Σ.
  Proof.
    exists (Context.rename (context_of_judgement J) f).
    exists (form_of_judgement J).
    exact (rename_hypothetical_judgement (equiv_inverse f)
           (hypothetical_part J)).
  Defined.

  Context `{H_Funext : Funext}.

  Local Definition rename_rename
      (J : judgement Σ)
      {γ' : shape_carrier σ} (e : γ' <~> shape_of_judgement J)
      {γ'' : shape_carrier σ} (e' : γ'' <~> γ')
    : rename (rename J e) e'
      = rename J (equiv_compose e e').
  Proof.
    refine (eq_by_expressions _ _); cbn.
    - intros i. apply rename_rename.
    - intros i. unfold rename_hypothetical_judgement; cbn.
        apply rename_rename.
  Defined.

  Local Definition rename_idmap
      (J : judgement Σ)
    : rename J (equiv_idmap _)
      = J.
  Proof.
    refine (eq_by_expressions _ _); cbn.
    - intros i. apply rename_idmap.
    - intros i. unfold rename_hypothetical_judgement; cbn.
      apply rename_idmap.
  Defined.

  Local Definition rename_inverse
      (J : judgement Σ)
      {γ' : shape_carrier σ} (e : shape_of_judgement J <~> γ')
    : rename (rename J (e^-1)) e = J.
  Proof.
    eapply concat. { apply rename_rename. }
    eapply concat. 2: { apply rename_idmap. }
    apply ap, ecompose_Ve.
  Defined.

  (* TODO: consistentise naming: [rename_idmap_widget] or [rename_widget_idmap]? *)
  Lemma rename_hypothetical_boundary_expressions_idmap
      {jf} {γ : σ} (B : hypothetical_boundary_expressions _ jf γ)
    : rename_hypothetical_boundary_expressions idmap B = B.
  Proof.
    apply path_forall; intros i.
    apply Expression.rename_idmap.
  Defined.

  Lemma rename_hypothetical_boundary_idmap
      {γ : σ} (B : hypothetical_boundary _ γ)
    : rename_hypothetical_boundary idmap B = B.
  Proof.
    apply (ap (Build_hypothetical_boundary _)).
    apply rename_hypothetical_boundary_expressions_idmap.
  Defined.

  Definition rename_idmap_hypothetical_judgement
      {γ : σ}
      (J : hypothetical_judgement Σ γ)
    : rename_hypothetical_judgement idmap J
    = J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i; apply Expression.rename_idmap.
  Defined.

  Definition rename_rename_hypothetical_judgement
      {γ γ' γ'' : σ} (f : γ -> γ') (g : γ' -> γ'')
      (J : hypothetical_judgement Σ γ)
    : rename_hypothetical_judgement g
        (rename_hypothetical_judgement f J)
    = rename_hypothetical_judgement (g o f) J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i; apply Expression.rename_rename.
  Defined.

End Renaming.

Section Substitution.
(** _Hypothetical_ judgements admit renaming along aritrary maps of shapes, just like expressions.

_Complete_ judgements, involving contexts, admit renaming only along _isomorphisms_ of shapes.  (Cf. discussion at [Context.rename].) *)

  Context {σ : shape_system} {Σ : signature σ}.

  Definition substitute_hypothetical_boundary_expressions
      {jf} {γ γ' : σ} (f : raw_context_map Σ γ' γ)
      (B : hypothetical_boundary_expressions Σ jf γ)
    : hypothetical_boundary_expressions Σ jf γ'.
  Proof.
    exact (fun j => substitute f (B j)).
  Defined.

  Definition substitute_hypothetical_boundary
      {γ γ' : σ} (f : raw_context_map Σ γ' γ)
      (B : hypothetical_boundary Σ γ)
    : hypothetical_boundary Σ γ'.
  Proof.
    exists (form_of_boundary B).
    exact (substitute_hypothetical_boundary_expressions f B).
  Defined.

  Definition substitute_hypothetical_judgement
      {γ γ' : σ} (f : raw_context_map Σ γ' γ)
      (J : hypothetical_judgement Σ γ)
    : hypothetical_judgement Σ γ'.
  Proof.
    exists (form_of_judgement J).
    exact (fun j => substitute f (J j)).
  Defined.

  Context `{Funext}.

  Definition substitute_rename_hypothetical_judgement
      {γ γ' γ'' : σ} (f : γ -> γ') (g : raw_context_map Σ γ'' γ')
      (J : hypothetical_judgement Σ γ)
    : substitute_hypothetical_judgement g
        (rename_hypothetical_judgement f J)
    = substitute_hypothetical_judgement (g o f) J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i; apply substitute_rename.
  Defined.

  Definition rename_substitute_hypothetical_judgement
      {γ γ' γ'' : σ} (f : raw_context_map Σ γ' γ) (g : γ' -> γ'')
      (J : hypothetical_judgement Σ γ)
    : rename_hypothetical_judgement g
        (substitute_hypothetical_judgement f J)
    = substitute_hypothetical_judgement (Expression.rename g o f) J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i; apply rename_substitute.
  Defined.

End Substitution.

Section Instantiation.
(** Interaction of judgements with metavariable instantiations *)

  Context {σ : shape_system} `{Funext}.

  Definition instantiate_hypothetical_judgement
      {a : arity σ} {Σ : signature σ} {γ : σ}
      (I : Metavariable.instantiation a Σ γ)
      {δ} (j : hypothetical_judgement (Metavariable.extend Σ a) δ)
    : hypothetical_judgement Σ (shape_sum γ δ).
  Proof.
    exists (form_of_judgement j).
    intro i; exact (instantiate_expression I (j i)).
  Defined.

  Local Definition instantiate
      {a : arity σ} {Σ : signature σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (j : judgement (Metavariable.extend Σ a))
    : judgement Σ.
  Proof.
    exists (Context.instantiate _ I (context_of_judgement j)).
    apply (instantiate_hypothetical_judgement I (hypothetical_part j)).
  Defined.

  (* TODO: factor out [fmap_instantiate_hypothetical_judgement] *)
  Local Lemma fmap_instantiate
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (J : judgement (Metavariable.extend _ _))
    : fmap f (instantiate Γ I J)
    = instantiate
        (Context.fmap f Γ) 
        (instantiation_fmap f I)
        (fmap (Metavariable.fmap1 f a) J).
  Proof.
    refine (eq_by_expressions _ _). 
    - (* context part *)
      refine (coproduct_rect shape_is_sum _ _ _); intros i;
        unfold Context.instantiate.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
        apply fmap_rename.
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
        apply fmap_instantiate_expression.
    - intros i; apply fmap_instantiate_expression.
  Defined.

  Lemma instantiate_fmap2_hypothetical_judgement
      {a a' : arity σ} (f : Family.map a a')
      {Σ} {γ} (I : Metavariable.instantiation a' Σ γ)
      {δ} (J : hypothetical_judgement (Metavariable.extend Σ a) δ)
    : instantiate_hypothetical_judgement I
        (fmap_hypothetical_judgement (Metavariable.fmap2 _ f) J)
    = instantiate_hypothetical_judgement (instantiation_fmap2 f I) J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply instantiate_fmap2.
  Defined.

  Lemma instantiate_fmap2_judgement
      {a a' : arity σ} (f : Family.map a a')
      {Σ} {Γ : raw_context Σ} (I : Metavariable.instantiation a' Σ Γ)
      (J : judgement (Metavariable.extend Σ a))
    : instantiate Γ I (fmap (Metavariable.fmap2 _ f) J)
    = instantiate Γ (instantiation_fmap2 f I) J.
  Proof.
    apply eq_by_expressions.
    - apply (coproduct_rect shape_is_sum).
      + intros.
        eapply concat. { rapply coproduct_comp_inj1. }
        apply inverse. rapply coproduct_comp_inj1.
      + intros.
        eapply concat. { rapply coproduct_comp_inj2. }
        eapply concat. 2: { apply inverse. rapply coproduct_comp_inj2. }
        apply instantiate_fmap2.
    - intros; apply instantiate_fmap2.
  Defined.

  Definition copair_instantiation_inl_hypothetical_judgement
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ) 
      {δ} (J : hypothetical_judgement (Metavariable.extend Σ a) δ)
    : instantiate_hypothetical_judgement
        (copair_instantiation Ia Ib)
        (fmap_hypothetical_judgement (Metavariable.fmap2 _ Family.inl) J)
      = instantiate_hypothetical_judgement Ia J.
  Proof.
    apply instantiate_fmap2_hypothetical_judgement.
  Defined.

  Definition copair_instantiation_inr_hypothetical_judgement
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ) 
      {δ} (J : hypothetical_judgement (Metavariable.extend Σ b) δ)
    : instantiate_hypothetical_judgement
        (copair_instantiation Ia Ib)
        (fmap_hypothetical_judgement (Metavariable.fmap2 _ Family.inr) J)
      = instantiate_hypothetical_judgement Ib J.
  Proof.
    apply instantiate_fmap2_hypothetical_judgement.
  Defined.

  (* TODO: rename this and following to [Judgement.copair_instantiation_inl], etc. *)
  Definition copair_instantiation_inl_judgement
      {Σ} {a b : arity σ} (Γ : raw_context _)
      (Ia : Metavariable.instantiation a Σ Γ) 
      (Ib : Metavariable.instantiation b Σ Γ) 
      (J : judgement (Metavariable.extend Σ a))
    : instantiate Γ
        (copair_instantiation Ia Ib)
        (fmap (Metavariable.fmap2 _ Family.inl) J)
      = instantiate Γ Ia J.
  Proof.
    apply instantiate_fmap2_judgement.
  Defined.

  Definition copair_instantiation_inr_judgement
      {Σ} {a b : arity σ} (Γ : raw_context _)
      (Ia : Metavariable.instantiation a Σ Γ) 
      (Ib : Metavariable.instantiation b Σ Γ) 
      (J : judgement (Metavariable.extend Σ b))
    : instantiate Γ
        (copair_instantiation Ia Ib)
        (fmap (Metavariable.fmap2 _ Family.inr) J)
      = instantiate Γ Ib J.
  Proof.
    apply instantiate_fmap2_judgement.
  Defined.

  Context {Σ : signature σ}.

  Local Lemma unit_instantiate
      {a} (J : judgement (Metavariable.extend Σ a))
    : instantiate [::] (unit_instantiation a)
        (fmap (Metavariable.fmap1 include_symbol _) J)
      = rename J (shape_sum_empty_inr _)^-1.
  Proof.
    refine (eq_by_expressions _ _). 
    - refine (coproduct_rect shape_is_sum _ _ _).
      + apply (empty_rect _ shape_is_empty).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply unit_instantiate_expression. }
        apply ap, ap, inverse. cbn.
        refine (coproduct_comp_inj2 _).
    - intros i; apply unit_instantiate_expression.
  Defined.

  Local Lemma instantiate_instantiate
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement (Metavariable.extend Σ b))
    : instantiate
        (Context.instantiate _ I Δ)
        (instantiate_instantiation I J) j
    = rename
        (instantiate Γ I
          (instantiate Δ J
            (fmap (Metavariable.fmap1 include_symbol _) j)))
         (shape_assoc _ _ _)^-1.
  Proof.
    refine (eq_by_expressions _ _).
      + apply @Context.instantiate_instantiate_pointwise; auto.
      + intros i. refine (instantiate_instantiate_expression _ _ _).
  Defined.

  Lemma instantiate_hypothetical_judgement_rename_instantiation
        (γ γ' : σ.(shape_carrier)) (f : γ -> γ')
        {a}  (I : Metavariable.instantiation a Σ γ)
        {δ} (J : hypothetical_judgement _ δ)
    : instantiate_hypothetical_judgement (rename_instantiation f I) J
    = rename_hypothetical_judgement
        (Coproduct.fmap shape_is_sum shape_is_sum f idmap)
        (instantiate_hypothetical_judgement I J).
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply instantiate_rename_instantiation.
  Defined.

  Lemma instantiate_hypothetical_judgement_substitute_instantiation
        (γ γ' : σ.(shape_carrier)) (f : raw_context_map Σ γ' γ)
        {a}  (I : Metavariable.instantiation a Σ γ)
        {δ} (J : hypothetical_judgement _ δ)
    : instantiate_hypothetical_judgement (substitute_instantiation f I) J
    = substitute_hypothetical_judgement
        (Substitution.extend γ γ' δ f)
        (instantiate_hypothetical_judgement I J).
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply instantiate_substitute_instantiation.
  Defined.

  (** The instantiation under [I] of any presupposition of a judgement [j]
      is equal to the corresponding presupposition of the instantiation of [j]
      itself under [I]. *)
  Definition instantiate_presupposition
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (j : judgement _)
      (i : presupposition (instantiate _ I j))
    : instantiate _ I (presupposition j i)
      = presupposition (instantiate _ I j) i.
  Proof.
    apply (ap (Build_judgement _)). (* context of presup unchanged *)
    apply (ap (Build_hypothetical_judgement _)). (* form of presup unchanged *)
    destruct j as [Δ [jf J]].
    (* hypothetical presupposition *)
    apply path_forall; intros k.
    recursive_destruct jf;
      recursive_destruct i;
      recursive_destruct k;
      apply idpath.
  Defined.

End Instantiation.

Arguments instantiate : simpl nomatch.

(** Combining two object judgements into an equality judgement
e.g. combining [Γ |- a1 : A1], [Γ |- a2 : A2] into [ Γ |- a1 = a2 : A2 ].

As per the example, we always combine “left-handedly”, taking the boundary of the combination to be the boundary of the first judgement. *)
Section Combine_Judgement.

  Context {σ : shape_system} `{Funext}.

  (** Given two object judgements [J] [K] of the same form,
   combine them into an equality judgement comparing their heads,
   over the boundary of [J]. *)
  (* TODO: consider naming! *)
  (* TODO: make [class_of] a coercion?
   also [boundary_slot_from_object_boundary_slot]? *)
  (* TODO: play around with definition to see if we can make this easier to reason about. *)
  Definition combine_hypothetical_judgement
      {Σ : signature σ}
      {γ} (J K : hypothetical_judgement Σ γ)
      (e : form_of_judgement J = form_of_judgement K)
      (J_obj : is_object (form_of_judgement J))
    : hypothetical_judgement Σ γ.
  Proof.
    exists (form_equality (class_of (form_of_judgement J))).
    intros [s | | ].
    - refine (transport (fun cl => raw_expression _ cl _) _ _).
      2: { exact (J (the_boundary_slot
                         (boundary_slot_from_object_boundary_slot s))). }
      eapply concat. { apply Family.map_commutes. }
      eapply (Family.map_commutes boundary_slot_from_object_boundary_slot).
    - exact (head J J_obj).
    - refine (transport (fun cl => raw_expression _ cl _) _ _).
      2: { refine (head K _). eapply transport; eassumption. }
      apply (ap class_of), inverse, e.
  Defined.

  (* TODO: refactor to this in other lemmas below about [combine_hypothetical_judgement] *)
  (* TODO: remove unnecessary [p_e], [p_obj] arguments, by showing above that things are hprops *)
  Lemma combine_hypothetical_judgement_eq
      {Σ : signature σ}
      {γ : σ} {J J' K K' : hypothetical_judgement Σ γ}
      {e : form_of_judgement J = form_of_judgement K}
      {e' : form_of_judgement J' = form_of_judgement K'}
      {J_obj : is_object (form_of_judgement J)}
      {J'_obj : is_object (form_of_judgement J')}
      (p_J : J' = J)
      (p_K : K' = K)
      (p_e : ap form_of_judgement p_J^ @ e' @ ap form_of_judgement p_K = e)
      (p_obj : transport (fun J => _ (form_of_judgement J)) p_J J'_obj
                                    = J_obj)
    : combine_hypothetical_judgement J K e J_obj 
      = combine_hypothetical_judgement J' K' e' J'_obj. 
  Proof.
    destruct p_J, p_K, p_e, p_obj; simpl.
    erapply ap_1back.
    eapply concat. { apply concat_p1. }
    apply concat_1p.
  Defined.

  Lemma rename_combine_hypothetical_judgement
    {Σ} {γ γ' : σ} (f : γ -> γ')
    (K K' : hypothetical_judgement Σ γ)
    (e : form_of_judgement K = form_of_judgement K')
    (K_obj : is_object (form_of_judgement K))
    : rename_hypothetical_judgement f
                         (combine_hypothetical_judgement K K' e K_obj)
    = combine_hypothetical_judgement
        (rename_hypothetical_judgement f K)
        (rename_hypothetical_judgement f K')
        e K_obj.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros [s | | ];
      destruct K as [jf K], K' as [jf' K']; cbn in e, K_obj;
      destruct e, jf; destruct K_obj;
    (* we destruct enough that all the equalities appearing under transports in the goal become idpaths, and the transports compute. *)
      apply idpath.
  Defined.

  Lemma instantiate_combine_hypothetical_judgement
    {Σ : signature σ} {a} {γ} (Ia : Metavariable.instantiation a Σ γ)
    {δ} (K K' : hypothetical_judgement _ δ)
    (e : form_of_judgement K = form_of_judgement K')
    (K_obj : is_object (form_of_judgement K))
    : instantiate_hypothetical_judgement Ia
                         (combine_hypothetical_judgement K K' e K_obj)
    = combine_hypothetical_judgement
        (instantiate_hypothetical_judgement Ia K)
        (instantiate_hypothetical_judgement Ia K')
        e K_obj.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros [s | | ];
      destruct K as [jf K], K' as [jf' K']; cbn in e, K_obj;
      destruct e, jf; destruct K_obj;
    (* we destruct enough that all the equalities appearing under transports in the goal become idpaths, and the transports compute. *)
      apply idpath.
  Defined.

(** If [f g] are two raw context maps [Δ -> Γ], and [J] an object judgement
over [Γ], there is an equality judgement comparing the pullbacks of [J] along
[f], [g].  E.g. [Γ |- A], this gives [Δ |- f^*A = g^*A]; for [Γ |- a:A], this
is [Δ |- f^*a = g^*A : f^*A] *)
  Definition substitute_equal_hypothetical_judgement
      {Σ : signature σ}
      {δ γ} (f g : raw_context_map Σ δ γ)
      (J : hypothetical_judgement Σ γ)
      (J_obj : is_object (form_of_judgement J))
    : hypothetical_judgement Σ δ.
  Proof.
    simple refine (combine_hypothetical_judgement _ _ _ _).
    - exact (substitute_hypothetical_judgement f J).
    - exact (substitute_hypothetical_judgement g J).
    - apply idpath.
    - apply J_obj.
  Defined.

  Definition rename_substitute_equal_hypothetical_judgement {Σ}
      {δ γ} (f g : raw_context_map Σ δ γ) {δ' : σ} {r : δ -> δ'}
      (J : hypothetical_judgement Σ γ)
      (J_obj : is_object (form_of_judgement J))
    : rename_hypothetical_judgement r
        (substitute_equal_hypothetical_judgement f g J J_obj)
    = substitute_equal_hypothetical_judgement
        (Expression.rename r o f)
        (Expression.rename r o g)
        J J_obj.
  Proof.
    eapply concat. { apply rename_combine_hypothetical_judgement. }
    refine (ap2 (fun J K
                       => combine_hypothetical_judgement
                            (Build_hypothetical_judgement _ J)
                            (Build_hypothetical_judgement _ K)
                            _ _)
                  _ _);
    apply path_forall; intros i; apply rename_substitute.
  Defined.

  Definition substitute_equal_rename_hypothetical_judgement {Σ}
      {γ γ' δ : σ} (r : γ -> γ') (f g : raw_context_map Σ δ γ')
      (J : hypothetical_judgement Σ γ)
      (J_obj : is_object (form_of_judgement J))
    : substitute_equal_hypothetical_judgement f g
        (rename_hypothetical_judgement r J) J_obj
    = substitute_equal_hypothetical_judgement (f o r) (g o r) J J_obj.
  Proof.
    refine (ap2 (fun J K
                       => combine_hypothetical_judgement
                            (Build_hypothetical_judgement _ J)
                            (Build_hypothetical_judgement _ K)
                            _ _)
                  _ _);
    apply path_forall; intros i; apply substitute_rename.
  Defined.


  Definition combine_judgement
      {Σ : signature σ}
      (J : judgement Σ)
      (K : hypothetical_judgement Σ (context_of_judgement J))
      (e : form_of_judgement J = form_of_judgement K)
      (J_obj : is_object (form_of_judgement J))
    : judgement Σ.
  Proof.
    exists (context_of_judgement J).
    apply (combine_hypothetical_judgement J K); try assumption.
  Defined.

  (* NOTE: the typing of this lemma is a bit subtle:
     the “cheat” in [combine_judgement] is exposed here,
     i.e. the mismatch that the second argument of [combine_judgement]
     is actually a hypothetical judgement. *)
  Lemma instantiate_combine_judgement
      {Σ : signature σ}
      {a} (J : judgement (Metavariable.extend Σ a))
      (Δ := context_of_judgement J)
      (K_hyp : hypothetical_judgement (Metavariable.extend Σ a) Δ)
      {e : form_of_judgement J = form_of_judgement K_hyp}
      {J_obj : is_object (form_of_judgement J)}
      {Γ : raw_context Σ} (I : Metavariable.instantiation a Σ Γ)
      {Θ : Δ -> raw_type _ Δ}
      (K := Build_judgement (Build_raw_context _ Θ) K_hyp)
    : instantiate Γ I (combine_judgement J K e J_obj)
      = combine_judgement (instantiate Γ I J) (instantiate Γ I K) e J_obj.
  Proof.
    apply (ap (Build_judgement _)).
    apply instantiate_combine_hypothetical_judgement.
  Defined.

End Combine_Judgement.