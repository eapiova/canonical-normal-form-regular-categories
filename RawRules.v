Require Import HoTT.
Require Import Auxiliary RawSyntax.

Section Structural_Rules.

Context (Σ : Signature).

(* Structural rules:

  - context formation rules
  - var rule
  - subst, wkg rules, for each type of judgement.
  - equality rules

*) 


Section Context_Formation.

(* TODO: the context formation rules.  A special case — need to be defined directly as closure conditions, since our raw rules only allow derivation of hypothetical judgements.  *)


(* TODO: empty context rule *)
(* TODO: context extension rule *)

(* An issue arising from the present approach to shapes/proto-contexts: if the context extension rule is formulated just with [shape_extend], then it will give no way to ever prove well-typedness of contexts with other shapes; in particular, of contexts using [shape_coprod], which will arise in the premises of logical rules. 

  Possible solutions (without entirely changing the proto-context approach):

  - a closure condition for the context judgements under “renaming variables” along isomorphisms of proto-contexts? 
  - formulate the context-extension rule in more general way: for *any* coproduct… (though still, is that enough?) 
 *)

(* TODO: renaming-of-variables rule (?)*)

End Context_Formation.

Section Var_Subst_Wkg.

(* The var rule:

  |– A type
-----------
x:A |– x:A

*)

Definition var_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [< 
      (Ty , shape_empty _ )    (* [ A ] *)
    >] : Arity).
  (* Name the symbols. *)
  pose (A := None : Metas).
  exists Metas.
  (* premises *)
  - refine [< _ >].
    (* Premise:  |— A type *)
    exists (HJF (obj_HJF Ty)).
    exists [: :].
    intros [ [] | ].  (* destructing an “option Empty” *)
    exact [M/ A /].
  (* conclusion *)
  - exists (HJF (obj_HJF Tm)).
    (* context of conclusion *)
    exists [: [M/ A /] :].
    intros [ [ [] | ] | ]; cbn.  (* destructing an “opetion (option Empty)” *)
    (* the term *)
    + refine (var_raw _).
      apply (plusone_top _ _ (shape_is_plusone _ _)).
    (* the type *)
    + exact [M/ A /].
Defined.

(* TODO: rule WKG_Ty 

 |– A type
 |– B type
-------------
x:B |– A type
*)

(* TODO: rule WKG_Tm

 |– A type
 |– a:A
 |– B type
-------------
x:B |– a:A
*)

(* TODO: rule WKG_TyEq *)

(* TODO: rule WKG_TmEq *)

(* TODO: QUESTION — is it enough to give single-variable substitution rules, or must we give more general family of rules for substituting along context morphisms? *)

(* TODO: rule SUBST_Ty *)

(* TODO: rule SUBST_TmEq *)

(* TODO: rule SUBST_TyEq *)

(* TODO: rule SUBST_TmEq *)

End Var_Subst_Wkg.

Section Equality_Rules.

(* TODO: rule REFL_TyEq *)

(* TODO: rule SYMM_TyEq *)

(* TODO: rule TRANS_TyEq *)

(* TODO: rule REFL_TmEq *)

(* TODO: rule SYMM_TmEq *)

(* TODO: rule TRANS_TmEq *)

(* TODO: rule COERCE_Ty 

 |– A, A' type
 |– A = A' type
 |– a:A
-------------
 |– a:A'
*)

End Equality_Rules.

End Structural_Rules.
