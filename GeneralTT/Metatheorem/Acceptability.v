
From HoTT Require Import HoTT.

From GeneralTT Require Import Syntax.All.
From GeneralTT Require Import Typing.All.
From GeneralTT Require Import Metatheorem.UniqueTyping.
From GeneralTT Require Import Metatheorem.Elimination.
From GeneralTT Require Import Metatheorem.Presuppositions.


Definition acceptable {σ} {Σ : signature σ} (T : raw_type_theory Σ)
  : Type
:= (is_tight_type_theory T)
  * (substitutive T)
  * (congruous T)
  * (presuppositive_raw_type_theory T).
