Require Export LogicalRelations.

(** Kripke logical relations generalize logical relations along the
  lines of the Kripke semantics of modal logic. A Kripke logical
  relation is indexed by a set of worlds equipped with an
  accessibility relation.

  This is useful when reasoning about stateful systems, because in
  that context the way we want to relate different components may
  evolve with the system state. Then, the Kripke world is essentially
  the relational counterpart to the state of the system, and the
  accessibility relation specifies how this world may evolve alongside
  the state (it denotes a notion of "possible future", for instance). *)


(** * Kripke frames and logical relations *)

(** Kripke frames specify the set of worlds over which a KLR is
  indexed, as well an associated set of initial worlds and
  accessibility relation. For a given Kripke frame, the type [klr]
  is a [W]-indexed version of [rel]. *)

Class KripkeFrame (W: Type) :=
  {
    acc: rel W W;
    winit: W -> Prop;
    klr A B := W -> rel A B;
  }.

Infix "~>" := acc (at level 70).
Notation "* ~> w" := (winit w) (at level 40).

Delimit Scope klr_scope with klr.
Bind Scope klr_scope with klr.


(** * Kripke relators *)

(** Just like relators allow us to construct complex relations from
  simpler ones in a structure-preserving way, Kripke relators allow us
  to build complex Kripke relations from simpler Kripke relations. *)

(** ** Lifted relators *)

(** First, we lift usual relators to obtain a Kripke version,
  basically as the pointwise extension over worlds of the original
  ones. *)

(** *** Lifiting operators *)

Section LIFT.
  Context `{kf: KripkeFrame}.
  Context {A1 B1 A2 B2 A B: Type}.

  (** For elementary relations, the corresponding Kripke relation can
    just ignore the Kripke world. *)

  Definition k (R: rel A B): klr A B :=
    fun w => R.

  Global Instance k_rel var:
    Monotonic k (var ++> - ==> var).
  Proof.
    unfold k; rauto.
  Qed.

  Global Instance k_rintro P R (w: W) (x: A) (y: B):
    RIntro P R x y ->
    RIntro P (k R w) x y.
  Proof.
    firstorder.
  Qed.

  (** For relators of higher arities, we let the original relator [RR]
    operate independently at each world [w]. *)

  Definition k1 RR (R1: klr A1 B1): klr A B :=
    fun w => RR (R1 w).

  Global Instance k1_rel var1 var:
    Monotonic k1 ((var1 ++> var) ++> ((- ==> var1) ++> (- ==> var))).
  Proof.
    unfold k1; rauto.
  Qed.

  Global Instance k1_rintro P RR (R1: klr A1 B1) w x y:
    RIntro P (RR (R1 w)) x y ->
    RIntro P (k1 RR R1 w) x y.
  Proof.
    firstorder.
  Qed.

  Definition k2 RR (R1: klr A1 B1) (R2: klr A2 B2): klr A B :=
    fun w => RR (R1 w) (R2 w).

  Global Instance k2_rel var1 var2 var:
    Monotonic k2
      ((var1 ++> var2 ++> var) ++>
       ((- ==> var1) ++> (- ==> var2) ++> (- ==> var))).
  Proof.
    unfold k2; rauto.
  Qed.

  Global Instance k2_rintro P RR (R1: klr A1 B1) (R2: klr A2 B2) w x y:
    RIntro P (RR (R1 w) (R2 w)) x y ->
    RIntro P (k2 RR R1 R2 w) x y.
  Proof.
    firstorder.
  Qed.
End LIFT.

Global Instance k_rel_params: Params (@k) 4.
Global Instance k1_rel_params: Params (@k1) 5.
Global Instance k2_rel_params: Params (@k2) 6.

(** *** Usual relators *)

(** Using the lifting operators defined above, we can provide a set of
  usual Kripke relators for various types. *)

Section USUAL.
  Context `{kf: KripkeFrame}.

  Definition arrow_klr {A1 A2 B1 B2} :=
    k2 (@arrow_rel A1 A2 B1 B2).

  Definition prod_klr {A1 A2 B1 B2} :=
    k2 (@prod_rel A1 A2 B1 B2).

  Definition sum_klr {A1 A2 B1 B2} :=
    k2 (@sum_rel A1 A2 B1 B2).

  Definition list_klr {A1 A2} :=
    k1 (@list_rel A1 A2).

  Definition set_kle {A B} (R: klr A B): klr (A -> Prop) (B -> Prop) :=
    fun w sA sB => forall a, sA a -> exists b, sB b /\ R w a b.

  Definition set_kge {A B} (R: klr A B): klr (A -> Prop) (B -> Prop) :=
    fun w sA sB => forall b, sB b -> exists a, sA a /\ R w a b.

  Definition klr_curry `{KripkeFrame} {A1 B1 C1 A2 B2 C2} :=
    k1 (@rel_curry A1 B1 C1 A2 B2 C2).
End USUAL.

Infix "++>" := arrow_klr : klr_scope.
Infix "*" := prod_klr : klr_scope.
Infix "+" := sum_klr : klr_scope.
Notation "% R" := (klr_curry R) : klr_scope.

(** ** Modal relators *)

(** In addition to the usual relators defined above, we can define
  Kripke-specific relators corresponding to the box and diamond
  modalities. *)

Section MODALITIES.
  Context `{kf: KripkeFrame}.

  (** The box modality asserts that the relation holds at all
    possible future worlds. *)

  Definition klr_box {A B} (R: klr A B): klr A B :=
    fun w x y => forall w', w ~> w' -> R w' x y.

  Global Instance klr_box_subrel {A B}:
    Monotonic (@klr_box A B) ((- ==> subrel) ++> (- ==> subrel)).
  Proof.
    firstorder.
  Qed.

  Lemma klr_box_rintro {A B} (R: klr A B) w x y:
    RIntro (forall w' (Hw': w ~> w'), R w' x y) (klr_box R w) x y.
  Proof.
    firstorder.
  Qed.

  (** Dually, the diamond modality asserts that the relation holds at
    some possible future world. Note the order of the premises in our
    intro rule: we want to first determine what [w'] should be, then
    attempt to prove [w ~> w']. *)

  Definition klr_diam {A B} (R: klr A B): klr A B :=
    fun w x y => exists w', w ~> w' /\ R w' x y.

  Global Instance klr_diam_subrel {A B}:
    Monotonic (@klr_diam A B) ((- ==> subrel) ++> (- ==> subrel)).
  Proof.
    firstorder.
  Qed.

  Lemma klr_diam_rintro {A B} (R: klr A B) w w' x y:
    RExists (R w' x y /\ w ~> w') (klr_diam R w) x y.
  Proof.
    firstorder.
  Qed.
End MODALITIES.

Global Instance klr_box_subrel_params: Params (@klr_box) 4.
Global Instance klr_diam_subrel_params: Params (@klr_diam) 4.

Hint Extern 0 (RIntro _ (klr_box _ _) _ _) =>
  eapply klr_box_rintro : typeclass_instances.

Hint Extern 0 (RExists _ (klr_diam _ _) _ _) =>
  eapply klr_diam_rintro : typeclass_instances.

Notation "[] R" := (klr_box R) (at level 35) : klr_scope.
Notation "<> R" := (klr_diam R) (at level 35) : klr_scope.

(** ** Flattening KLRs *)

(** When converting back to a standard [rel], we can quantify over
  initial worlds in the same two ways. *)

Section UNKRIPKIFY.
  Context `{kf: KripkeFrame}.

  Definition rel_box {A B} (R: klr A B): rel A B :=
    fun x y => forall w, winit w -> R w x y.

  Global Instance rel_box_subrel A B:
    Monotonic (@rel_box A B) ((- ==> subrel) ++> subrel).
  Proof.
    firstorder.
  Qed.

  Lemma rel_box_rintro {A B} (R: klr A B) x y:
    RIntro (forall w (Hw : winit w), R w x y) (rel_box R) x y.
  Proof.
    firstorder.
  Qed.

  Definition rel_diam {A B} (R: klr A B): rel A B :=
    fun x y => exists w, winit w /\ R w x y.

  Global Instance rel_diam_subrel A B:
    Monotonic (@rel_diam A B) ((- ==> subrel) ++> subrel).
  Proof.
    firstorder.
  Qed.

  Lemma rel_diam_rintro {A B} (R: klr A B) w x y:
    RExists (R w x y /\ winit w) (rel_diam R) x y.
  Proof.
    firstorder.
  Qed.
End UNKRIPKIFY.

Global Instance rel_box_subrel_params: Params (@rel_box) 3.
Global Instance rel_diam_subrel_params: Params (@rel_diam) 3.

Hint Extern 0 (RIntro _ (rel_box _) _ _) =>
  eapply rel_box_rintro : typeclass_instances.

Hint Extern 0 (RExists _ (rel_diam _) _ _) =>
  eapply rel_diam_rintro : typeclass_instances.

Notation "[] R" := (rel_box R) (at level 35) : rel_scope.
Notation "<> R" := (rel_diam R) (at level 35) : rel_scope.

